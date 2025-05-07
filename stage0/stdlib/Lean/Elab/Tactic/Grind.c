// Lean compiler output
// Module: Lean.Elab.Tactic.Grind
// Imports: Init.Grind.Tactics Lean.Meta.Tactic.Grind Lean.Meta.Tactic.TryThis Lean.Elab.Command Lean.Elab.MutualDef Lean.Elab.Tactic.Basic Lean.Elab.Tactic.Config
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabResetGrindAttrs___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ensureNonAmbiguous___at___Lean_resolveGlobalConstNoOverload___at___Lean_Elab_Tactic_elabGrindPattern_spec__0_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Elab_Tactic_elabGrindParams_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_setGrindParams(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalGrind__1(lean_object*);
lean_object* lean_format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty___at___Lean_Meta_Grind_initFn____x40_Lean_Meta_Tactic_Grind_EMatchTheorem___hyg_2570__spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_elabGrindParams_spec__3(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst___at___Lean_resolveGlobalConstNoOverload___at___Lean_Elab_Tactic_elabGrindPattern_spec__0_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_formatStx(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Elab_Tactic_mkGrindOnly_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Elab_Tactic_mkGrindOnly_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___Lean_resolveGlobalConst___at___Lean_resolveGlobalConstNoOverload___at___Lean_Elab_Tactic_elabGrindPattern_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_PersistentHashSet_toList___at___Lean_Elab_Tactic_mkGrindOnly_spec__5_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___at___Lean_resolveGlobalConst___at___Lean_resolveGlobalConstNoOverload___at___Lean_Elab_Tactic_elabGrindPattern_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_elabConfig(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_elabGrindPattern_spec__8(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGrindCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_grind___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_withMainContext_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_addEMatchTheorem(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_filterFieldList___at_____private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___Lean_resolveGlobalConst___at___Lean_resolveGlobalConstNoOverload___at___Lean_Elab_Tactic_elabGrindPattern_spec__0_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentD(lean_object*);
uint8_t l_Array_isEmpty___redArg(lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_Environment_addExtraName_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_toList___at___Lean_Elab_Tactic_mkGrindOnly_spec__5(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___Lean_evalConst___at_____private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback_unsafe__1_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_resetCasesExt___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkAuxName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_registerNormTheorems(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabResetGrindAttrs___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGrindCore___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___Lean_evalConst___at_____private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback_unsafe__1_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Tactic_mkGrindOnly_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_toList___at___Lean_Elab_Tactic_mkGrindOnly_spec__5___boxed(lean_object*);
lean_object* l_Lean_getConstInfo___at_____private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_elabConfig_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isReducible___at_____private_Lean_Meta_Basic_0__Lean_Meta_getDefInfoTemp_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabResetGrindAttrs(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Elab_Tactic_mkGrindOnly_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGrind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Match_isMatchEqnTheorem(lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_PersistentHashSet_toList___at___Lean_Elab_Tactic_mkGrindOnly_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_grindParamsPos;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_instMonadEIO___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_instHashableEMatchTheoremTrace;
lean_object* l_Lean_Elab_Tactic_getMainGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_assign___at___Lean_Elab_Tactic_refineCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_filterFieldList___at_____private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___Lean_resolveGlobalConst___at___Lean_resolveGlobalConstNoOverload___at___Lean_Elab_Tactic_elabGrindPattern_spec__0_spec__0_spec__0_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isCasesAttrCandidate_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst___at___Lean_resolveGlobalConstNoOverload___at___Lean_Elab_Tactic_elabGrindPattern_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_grind___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabInitGrindNorm___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_elabInitGrindNorm_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_logWarningAt___at___Lean_Linter_logLint___at___Lean_Linter_logLintIf___at___Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkGrindParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_filterFieldList___at_____private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___Lean_resolveGlobalConst___at___Lean_resolveGlobalConstNoOverload___at___Lean_Elab_Tactic_elabGrindPattern_spec__0_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst___at___Lean_resolveGlobalConstNoOverload___at___Lean_Elab_Tactic_elabGrindPattern_spec__0_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkGrindParams(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindPattern___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Elab_Tactic_elabGrindParams_spec__2___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toPArray_x27___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_elabGrindParams_spec__3_spec__3(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasSyntheticSorry(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabResetGrindAttrs___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_getConfigItems(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___Lean_filterFieldList___at_____private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___Lean_resolveGlobalConst___at___Lean_resolveGlobalConstNoOverload___at___Lean_Elab_Tactic_elabGrindPattern_spec__0_spec__0_spec__0_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConst___at_____private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback_unsafe__1_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___Lean_evalConst___at_____private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback_unsafe__1_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_elabInitGrindNorm_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_isBuiltinEagerCases(lean_object*);
lean_object* l_ReaderT_instMonad(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_EMatchTheorems_eraseDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabResetGrindAttrs___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindConfig___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_abstract(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_grindOnlyPos;
lean_object* l_Lean_Meta_Grind_preprocessPattern(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getCasesTypes(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_instantiateMVarsProfiling(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_EMatchTheorems_find(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
lean_object* l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_grind_warning;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Elab_Tactic_elabGrindPattern_spec__8_spec__8(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
lean_object* l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_eval_const(lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_ensureNonAmbiguous___at___Lean_resolveGlobalConstNoOverload___at___Lean_Elab_Tactic_elabGrindPattern_spec__0_spec__5_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_filterFieldList___at_____private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___Lean_resolveGlobalConst___at___Lean_resolveGlobalConstNoOverload___at___Lean_Elab_Tactic_elabGrindPattern_spec__0_spec__0_spec__0_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_Syntax_TSepArray_getElems___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe___redArg____x40_Lean_Elab_Tactic_Grind___hyg_5_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___Lean_filterFieldList___at_____private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___Lean_resolveGlobalConst___at___Lean_resolveGlobalConstNoOverload___at___Lean_Elab_Tactic_elabGrindPattern_spec__0_spec__0_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Tactic_mkGrindOnly_spec__9_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Elab_Tactic_mkGrindOnly_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_CasesTypes_eraseDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst___at___Lean_resolveGlobalConstNoOverload___at___Lean_Elab_Tactic_elabGrindPattern_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_beqEMatchTheoremTrace____x40_Lean_Meta_Tactic_Grind_Types___hyg_329____boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabResetGrindAttrs___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_elabGrindParams_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGrindCore___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Tactic_mkGrindOnly_spec__3_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkSep(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalGrindTrace__1(lean_object*);
lean_object* l_Lean_Meta_Grind_mkEMatchTheoremForDecl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Tactic_mkGrindOnly_spec__7_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getEMatchTheorems___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_elabResetGrindAttrs__1(lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_Result_hasFailures(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindParams(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigItemViews(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Tactic_mkGrindOnly_spec__7_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Elab_Tactic_mkGrindOnly_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Elab_Tactic_mkGrindOnly_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Elab_Tactic_mkGrindOnly_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getSepArgs(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Elab_Tactic_mkGrindOnly_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Elab_Tactic_mkGrindOnly_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_toString___at___Lean_ensureNoOverload___at___Lean_realizeGlobalConstNoOverloadCore_spec__0_spec__1(lean_object*);
lean_object* l_Lean_resolveGlobalName___at___Lean_resolveLocalName_loop___at___Lean_resolveLocalName___at___Lean_Elab_Term_isLocalIdent_x3f_spec__0_spec__9_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_elabInitGrindNorm_spec__0___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_toList___at___Lean_Elab_Tactic_mkGrindOnly_spec__0(lean_object*);
lean_object* l_Lean_Meta_isEqnThm_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
lean_object* l_List_filterMapTR_go___at___Lean_preprocessSyntaxAndResolve___at___Lean_realizeGlobalConst_spec__0_spec__0(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVarsUsingDefault(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___at___Lean_filterFieldList___at___Lean_realizeGlobalConstCore_spec__0_spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___at___Lean_ensureNonAmbiguous___at___Lean_realizeGlobalConstNoOverload_spec__0_spec__1(lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_toList___at___Lean_Environment_dbgFormatAsyncState_spec__14___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_elabInitGrindNorm_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_syntax_ident(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindConfig___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Elab_Tactic_mkGrindOnly_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___Lean_PersistentHashSet_toList___at___Lean_Elab_Tactic_mkGrindOnly_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___Lean_PersistentHashSet_toList___at___Lean_Elab_Tactic_mkGrindOnly_spec__0_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Elab_Tactic_elabGrindParams_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConst___at_____private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback_unsafe__1_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverload___at___Lean_Elab_Tactic_elabGrindPattern_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabInitGrindNorm___lam__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Lean_Meta_Grind_getAttrKindCore(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_ensureNonAmbiguous___at___Lean_resolveGlobalConstNoOverload___at___Lean_Elab_Tactic_elabGrindPattern_spec__0_spec__5_spec__5___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Meta_mkAuxTheorem(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_elabInitGrindNorm__1(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Elab_Tactic_mkGrindOnly_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at___Lean_Elab_Term_MVarErrorInfo_logError_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_setArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_resetEMatchTheoremsExt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Tactic_mkGrindOnly_spec__9_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Grind___hyg_5_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Elab_Tactic_elabGrindParams_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_elabGrindPattern__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindConfig___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Elab_Tactic_elabGrindParams_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Tactic_mkGrindOnly_spec__9_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Elab_Tactic_mkGrindOnly_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_ensureNonAmbiguous___at___Lean_resolveGlobalConstNoOverload___at___Lean_Elab_Tactic_elabGrindPattern_spec__0_spec__5_spec__5___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_ensureNonAmbiguous___at___Lean_resolveGlobalConstNoOverload___at___Lean_Elab_Tactic_elabGrindPattern_spec__0_spec__5_spec__5___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_foldlM___at___Lean_PersistentHashMap_foldl_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getDeclName_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback_unsafe__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withMainContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkEMatchEqTheoremsForDef_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Elab_Tactic_elabGrindParams_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkGrindOnly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_toList___at___Lean_Elab_Tactic_mkGrindOnly_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___Lean_PersistentHashSet_toList___at___Lean_Elab_Tactic_mkGrindOnly_spec__0_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_grind(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___Lean_Elab_Tactic_elabGrindParams_spec__1(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Tactic_mkGrindOnly_spec__7_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___Lean_Elab_Tactic_elabGrindParams_spec__1___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Result_toMessageData(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_elabGrindPattern_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Tactic_mkGrindOnly_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Grind___hyg_5____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___Lean_PersistentHashSet_toList___at___Lean_Elab_Tactic_mkGrindOnly_spec__0_spec__0(lean_object*, lean_object*);
lean_object* l_List_filterTR_loop___at___Lean_filterFieldList___at___Lean_realizeGlobalConstCore_spec__0_spec__0(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_validateCasesAttr(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConst___at_____private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback_unsafe__1_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___at___Lean_MetavarContext_addExprMVarDecl_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_ensureNotBuiltinCases(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConst___at_____private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback_unsafe__1_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindPattern___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___Lean_resolveGlobalConst___at___Lean_resolveGlobalConstNoOverload___at___Lean_Elab_Tactic_elabGrindPattern_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasSorry(lean_object*);
lean_object* l_Lean_Meta_mkAuxDefinition(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConstWithLevelParams___at___Lean_Elab_checkNotAlreadyDeclared___at___Lean_Elab_applyVisibility___at___Lean_Elab_mkDeclName___at___Lean_Elab_expandDeclId___at___Lean_Elab_Term_expandDeclId_spec__0_spec__1_spec__3_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGrindCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_seqRight(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Elab_Tactic_elabGrindParams_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftTermElabM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getGrindParams(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___Lean_PersistentHashSet_toList___at___Lean_Elab_Tactic_mkGrindOnly_spec__0_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_elabGrindParams_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabInitGrindNorm(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___Lean_filterFieldList___at_____private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___Lean_resolveGlobalConst___at___Lean_resolveGlobalConstNoOverload___at___Lean_Elab_Tactic_elabGrindPattern_spec__0_spec__0_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_setGrindParams___boxed(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Elab_Term_addTermInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___Lean_filterFieldList___at_____private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___Lean_resolveGlobalConst___at___Lean_resolveGlobalConstNoOverload___at___Lean_Elab_Tactic_elabGrindPattern_spec__0_spec__0_spec__0_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabInitGrindNorm___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwUnknownIdentifier___at___Lean_Elab_Term_resolveName_process_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback_unsafe__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___at___Lean_resolveGlobalConst___at___Lean_resolveGlobalConstNoOverload___at___Lean_Elab_Tactic_elabGrindPattern_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_isGrindOnly(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindPattern___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInductivePredicate_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindPattern(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_isGrindOnly___boxed(lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* l_Lean_Meta_withLCtx___at___Lean_Elab_Term_MVarErrorInfo_logError_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_throwErrorAt___at___Lean_Meta_Match_Alt_checkAndReplaceFVarId_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getGrindParams___boxed(lean_object*);
lean_object* l_Lean_addAndCompile(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTermAndSynthesize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_evalExpr_x27(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Elab_Tactic_elabGrindPattern_spec__8_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isCasesAttrPredicateCandidate_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
uint8_t l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_beqEMatchTheoremKind____x40_Lean_Meta_Tactic_Grind_EMatchTheorem___hyg_1361_(uint8_t, uint8_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___Lean_evalConst___at_____private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback_unsafe__1_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindPattern___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGrindTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_grind___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescope___at_____private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe___redArg____x40_Lean_Elab_Tactic_Grind___hyg_5_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
x_8 = lean_mk_string_unchecked("Grind", 5, 5);
x_9 = lean_mk_string_unchecked("Config", 6, 6);
x_10 = l_Lean_Name_mkStr3(x_7, x_8, x_9);
x_11 = lean_box(0);
x_12 = lean_unbox(x_11);
x_13 = l_Lean_Meta_evalExpr_x27(lean_box(0), x_10, x_1, x_12, x_2, x_3, x_4, x_5, x_6);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Grind___hyg_5_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Tactic_evalUnsafe___redArg____x40_Lean_Elab_Tactic_Grind___hyg_5_(x_1, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Grind___hyg_5____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Grind___hyg_5_(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindConfig___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; uint8_t x_68; 
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
x_64 = lean_mk_string_unchecked("Grind", 5, 5);
x_65 = lean_mk_string_unchecked("Config", 6, 6);
x_66 = l_Lean_Name_mkStr3(x_63, x_64, x_65);
x_67 = lean_unbox(x_40);
lean_inc(x_66);
x_68 = l_Lean_Environment_contains(x_62, x_66, x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
lean_dec(x_38);
x_69 = lean_mk_string_unchecked("error evaluating configuration, environment does not yet contain type ", 70, 70);
x_70 = l_Lean_stringToMessageData(x_69);
lean_dec(x_69);
x_71 = l_Lean_MessageData_ofName(x_66);
lean_ctor_set_tag(x_41, 7);
lean_ctor_set(x_41, 1, x_71);
lean_ctor_set(x_41, 0, x_70);
x_72 = lean_mk_string_unchecked("", 0, 0);
x_73 = l_Lean_stringToMessageData(x_72);
lean_dec(x_72);
x_74 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_74, 0, x_41);
lean_ctor_set(x_74, 1, x_73);
x_75 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_74, x_3, x_4, x_5, x_6, x_61, x_8, x_44);
lean_dec(x_8);
lean_dec(x_61);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_76 = !lean_is_exclusive(x_75);
if (x_76 == 0)
{
return x_75;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_75, 0);
x_78 = lean_ctor_get(x_75, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_75);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
else
{
lean_object* x_80; 
lean_free_object(x_41);
lean_inc(x_8);
lean_inc(x_61);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_80 = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_elabConfig(x_36, x_66, x_38, x_3, x_4, x_5, x_6, x_61, x_8, x_44);
if (lean_obj_tag(x_80) == 0)
{
uint8_t x_81; 
x_81 = !lean_is_exclusive(x_80);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_82 = lean_ctor_get(x_80, 0);
x_83 = lean_ctor_get(x_80, 1);
x_84 = l_Lean_Expr_hasSyntheticSorry(x_82);
if (x_84 == 0)
{
uint8_t x_85; 
lean_free_object(x_80);
x_85 = l_Lean_Expr_hasSorry(x_82);
if (x_85 == 0)
{
lean_object* x_86; 
lean_inc(x_8);
lean_inc(x_61);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_82);
x_86 = l_Lean_Elab_Tactic_evalUnsafe___redArg____x40_Lean_Elab_Tactic_Grind___hyg_5_(x_82, x_5, x_6, x_61, x_8, x_83);
if (lean_obj_tag(x_86) == 0)
{
lean_dec(x_82);
lean_dec(x_61);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_86;
}
else
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
x_89 = l_Lean_Exception_isInterrupt(x_87);
if (x_89 == 0)
{
uint8_t x_90; 
x_90 = l_Lean_Exception_isRuntime(x_87);
x_10 = x_87;
x_11 = x_61;
x_12 = x_3;
x_13 = x_82;
x_14 = x_4;
x_15 = x_88;
x_16 = x_6;
x_17 = x_86;
x_18 = x_8;
x_19 = x_5;
x_20 = x_90;
goto block_35;
}
else
{
x_10 = x_87;
x_11 = x_61;
x_12 = x_3;
x_13 = x_82;
x_14 = x_4;
x_15 = x_88;
x_16 = x_6;
x_17 = x_86;
x_18 = x_8;
x_19 = x_5;
x_20 = x_89;
goto block_35;
}
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; 
lean_dec(x_82);
x_91 = lean_mk_string_unchecked("configuration contains 'sorry'", 30, 30);
x_92 = l_Lean_stringToMessageData(x_91);
lean_dec(x_91);
x_93 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_92, x_3, x_4, x_5, x_6, x_61, x_8, x_83);
lean_dec(x_8);
lean_dec(x_61);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_94 = !lean_is_exclusive(x_93);
if (x_94 == 0)
{
return x_93;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_93, 0);
x_96 = lean_ctor_get(x_93, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_93);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_82);
lean_dec(x_61);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_98 = lean_unsigned_to_nat(8u);
x_99 = lean_unsigned_to_nat(5u);
x_100 = lean_unsigned_to_nat(1000u);
x_101 = lean_unsigned_to_nat(1u);
x_102 = lean_unsigned_to_nat(10000u);
x_103 = lean_alloc_ctor(0, 7, 18);
lean_ctor_set(x_103, 0, x_98);
lean_ctor_set(x_103, 1, x_99);
lean_ctor_set(x_103, 2, x_99);
lean_ctor_set(x_103, 3, x_100);
lean_ctor_set(x_103, 4, x_101);
lean_ctor_set(x_103, 5, x_100);
lean_ctor_set(x_103, 6, x_102);
lean_ctor_set_uint8(x_103, sizeof(void*)*7, x_39);
lean_ctor_set_uint8(x_103, sizeof(void*)*7 + 1, x_84);
lean_ctor_set_uint8(x_103, sizeof(void*)*7 + 2, x_84);
lean_ctor_set_uint8(x_103, sizeof(void*)*7 + 3, x_84);
lean_ctor_set_uint8(x_103, sizeof(void*)*7 + 4, x_39);
lean_ctor_set_uint8(x_103, sizeof(void*)*7 + 5, x_39);
lean_ctor_set_uint8(x_103, sizeof(void*)*7 + 6, x_84);
lean_ctor_set_uint8(x_103, sizeof(void*)*7 + 7, x_39);
lean_ctor_set_uint8(x_103, sizeof(void*)*7 + 8, x_84);
lean_ctor_set_uint8(x_103, sizeof(void*)*7 + 9, x_84);
lean_ctor_set_uint8(x_103, sizeof(void*)*7 + 10, x_84);
lean_ctor_set_uint8(x_103, sizeof(void*)*7 + 11, x_84);
lean_ctor_set_uint8(x_103, sizeof(void*)*7 + 12, x_39);
lean_ctor_set_uint8(x_103, sizeof(void*)*7 + 13, x_84);
lean_ctor_set_uint8(x_103, sizeof(void*)*7 + 14, x_84);
lean_ctor_set_uint8(x_103, sizeof(void*)*7 + 15, x_84);
lean_ctor_set_uint8(x_103, sizeof(void*)*7 + 16, x_39);
lean_ctor_set_uint8(x_103, sizeof(void*)*7 + 17, x_39);
lean_ctor_set(x_80, 0, x_103);
return x_80;
}
}
else
{
lean_object* x_104; lean_object* x_105; uint8_t x_106; 
x_104 = lean_ctor_get(x_80, 0);
x_105 = lean_ctor_get(x_80, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_80);
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
x_108 = l_Lean_Elab_Tactic_evalUnsafe___redArg____x40_Lean_Elab_Tactic_Grind___hyg_5_(x_104, x_5, x_6, x_61, x_8, x_105);
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
x_10 = x_109;
x_11 = x_61;
x_12 = x_3;
x_13 = x_104;
x_14 = x_4;
x_15 = x_110;
x_16 = x_6;
x_17 = x_108;
x_18 = x_8;
x_19 = x_5;
x_20 = x_112;
goto block_35;
}
else
{
x_10 = x_109;
x_11 = x_61;
x_12 = x_3;
x_13 = x_104;
x_14 = x_4;
x_15 = x_110;
x_16 = x_6;
x_17 = x_108;
x_18 = x_8;
x_19 = x_5;
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
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
lean_dec(x_104);
lean_dec(x_61);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_120 = lean_unsigned_to_nat(8u);
x_121 = lean_unsigned_to_nat(5u);
x_122 = lean_unsigned_to_nat(1000u);
x_123 = lean_unsigned_to_nat(1u);
x_124 = lean_unsigned_to_nat(10000u);
x_125 = lean_alloc_ctor(0, 7, 18);
lean_ctor_set(x_125, 0, x_120);
lean_ctor_set(x_125, 1, x_121);
lean_ctor_set(x_125, 2, x_121);
lean_ctor_set(x_125, 3, x_122);
lean_ctor_set(x_125, 4, x_123);
lean_ctor_set(x_125, 5, x_122);
lean_ctor_set(x_125, 6, x_124);
lean_ctor_set_uint8(x_125, sizeof(void*)*7, x_39);
lean_ctor_set_uint8(x_125, sizeof(void*)*7 + 1, x_106);
lean_ctor_set_uint8(x_125, sizeof(void*)*7 + 2, x_106);
lean_ctor_set_uint8(x_125, sizeof(void*)*7 + 3, x_106);
lean_ctor_set_uint8(x_125, sizeof(void*)*7 + 4, x_39);
lean_ctor_set_uint8(x_125, sizeof(void*)*7 + 5, x_39);
lean_ctor_set_uint8(x_125, sizeof(void*)*7 + 6, x_106);
lean_ctor_set_uint8(x_125, sizeof(void*)*7 + 7, x_39);
lean_ctor_set_uint8(x_125, sizeof(void*)*7 + 8, x_106);
lean_ctor_set_uint8(x_125, sizeof(void*)*7 + 9, x_106);
lean_ctor_set_uint8(x_125, sizeof(void*)*7 + 10, x_106);
lean_ctor_set_uint8(x_125, sizeof(void*)*7 + 11, x_106);
lean_ctor_set_uint8(x_125, sizeof(void*)*7 + 12, x_39);
lean_ctor_set_uint8(x_125, sizeof(void*)*7 + 13, x_106);
lean_ctor_set_uint8(x_125, sizeof(void*)*7 + 14, x_106);
lean_ctor_set_uint8(x_125, sizeof(void*)*7 + 15, x_106);
lean_ctor_set_uint8(x_125, sizeof(void*)*7 + 16, x_39);
lean_ctor_set_uint8(x_125, sizeof(void*)*7 + 17, x_39);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_105);
return x_126;
}
}
}
else
{
uint8_t x_127; 
lean_dec(x_61);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_127 = !lean_is_exclusive(x_80);
if (x_127 == 0)
{
return x_80;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_80, 0);
x_129 = lean_ctor_get(x_80, 1);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_80);
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
return x_130;
}
}
}
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; lean_object* x_146; uint8_t x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; uint8_t x_156; 
x_131 = lean_ctor_get(x_41, 0);
x_132 = lean_ctor_get(x_41, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_41);
x_133 = lean_ctor_get(x_7, 5);
x_134 = l_Lean_replaceRef(x_1, x_133);
lean_dec(x_1);
x_135 = lean_ctor_get(x_7, 0);
x_136 = lean_ctor_get(x_7, 1);
x_137 = lean_ctor_get(x_7, 2);
x_138 = lean_ctor_get(x_7, 3);
x_139 = lean_ctor_get(x_7, 4);
x_140 = lean_ctor_get(x_7, 6);
x_141 = lean_ctor_get(x_7, 7);
x_142 = lean_ctor_get(x_7, 8);
x_143 = lean_ctor_get(x_7, 9);
x_144 = lean_ctor_get(x_7, 10);
x_145 = lean_ctor_get_uint8(x_7, sizeof(void*)*13);
x_146 = lean_ctor_get(x_7, 11);
x_147 = lean_ctor_get_uint8(x_7, sizeof(void*)*13 + 1);
x_148 = lean_ctor_get(x_7, 12);
lean_inc(x_148);
lean_inc(x_146);
lean_inc(x_144);
lean_inc(x_143);
lean_inc(x_142);
lean_inc(x_141);
lean_inc(x_140);
lean_inc(x_139);
lean_inc(x_138);
lean_inc(x_137);
lean_inc(x_136);
lean_inc(x_135);
x_149 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_149, 0, x_135);
lean_ctor_set(x_149, 1, x_136);
lean_ctor_set(x_149, 2, x_137);
lean_ctor_set(x_149, 3, x_138);
lean_ctor_set(x_149, 4, x_139);
lean_ctor_set(x_149, 5, x_134);
lean_ctor_set(x_149, 6, x_140);
lean_ctor_set(x_149, 7, x_141);
lean_ctor_set(x_149, 8, x_142);
lean_ctor_set(x_149, 9, x_143);
lean_ctor_set(x_149, 10, x_144);
lean_ctor_set(x_149, 11, x_146);
lean_ctor_set(x_149, 12, x_148);
lean_ctor_set_uint8(x_149, sizeof(void*)*13, x_145);
lean_ctor_set_uint8(x_149, sizeof(void*)*13 + 1, x_147);
x_150 = lean_ctor_get(x_131, 0);
lean_inc(x_150);
lean_dec(x_131);
x_151 = lean_mk_string_unchecked("Lean", 4, 4);
x_152 = lean_mk_string_unchecked("Grind", 5, 5);
x_153 = lean_mk_string_unchecked("Config", 6, 6);
x_154 = l_Lean_Name_mkStr3(x_151, x_152, x_153);
x_155 = lean_unbox(x_40);
lean_inc(x_154);
x_156 = l_Lean_Environment_contains(x_150, x_154, x_155);
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
x_164 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_163, x_3, x_4, x_5, x_6, x_149, x_8, x_132);
lean_dec(x_8);
lean_dec(x_149);
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
lean_inc(x_149);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_169 = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_elabConfig(x_36, x_154, x_38, x_3, x_4, x_5, x_6, x_149, x_8, x_132);
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
lean_inc(x_149);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_170);
x_175 = l_Lean_Elab_Tactic_evalUnsafe___redArg____x40_Lean_Elab_Tactic_Grind___hyg_5_(x_170, x_5, x_6, x_149, x_8, x_171);
if (lean_obj_tag(x_175) == 0)
{
lean_dec(x_170);
lean_dec(x_149);
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
x_10 = x_176;
x_11 = x_149;
x_12 = x_3;
x_13 = x_170;
x_14 = x_4;
x_15 = x_177;
x_16 = x_6;
x_17 = x_175;
x_18 = x_8;
x_19 = x_5;
x_20 = x_179;
goto block_35;
}
else
{
x_10 = x_176;
x_11 = x_149;
x_12 = x_3;
x_13 = x_170;
x_14 = x_4;
x_15 = x_177;
x_16 = x_6;
x_17 = x_175;
x_18 = x_8;
x_19 = x_5;
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
x_182 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_181, x_3, x_4, x_5, x_6, x_149, x_8, x_171);
lean_dec(x_8);
lean_dec(x_149);
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
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
lean_dec(x_170);
lean_dec(x_149);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_187 = lean_unsigned_to_nat(8u);
x_188 = lean_unsigned_to_nat(5u);
x_189 = lean_unsigned_to_nat(1000u);
x_190 = lean_unsigned_to_nat(1u);
x_191 = lean_unsigned_to_nat(10000u);
x_192 = lean_alloc_ctor(0, 7, 18);
lean_ctor_set(x_192, 0, x_187);
lean_ctor_set(x_192, 1, x_188);
lean_ctor_set(x_192, 2, x_188);
lean_ctor_set(x_192, 3, x_189);
lean_ctor_set(x_192, 4, x_190);
lean_ctor_set(x_192, 5, x_189);
lean_ctor_set(x_192, 6, x_191);
lean_ctor_set_uint8(x_192, sizeof(void*)*7, x_39);
lean_ctor_set_uint8(x_192, sizeof(void*)*7 + 1, x_173);
lean_ctor_set_uint8(x_192, sizeof(void*)*7 + 2, x_173);
lean_ctor_set_uint8(x_192, sizeof(void*)*7 + 3, x_173);
lean_ctor_set_uint8(x_192, sizeof(void*)*7 + 4, x_39);
lean_ctor_set_uint8(x_192, sizeof(void*)*7 + 5, x_39);
lean_ctor_set_uint8(x_192, sizeof(void*)*7 + 6, x_173);
lean_ctor_set_uint8(x_192, sizeof(void*)*7 + 7, x_39);
lean_ctor_set_uint8(x_192, sizeof(void*)*7 + 8, x_173);
lean_ctor_set_uint8(x_192, sizeof(void*)*7 + 9, x_173);
lean_ctor_set_uint8(x_192, sizeof(void*)*7 + 10, x_173);
lean_ctor_set_uint8(x_192, sizeof(void*)*7 + 11, x_173);
lean_ctor_set_uint8(x_192, sizeof(void*)*7 + 12, x_39);
lean_ctor_set_uint8(x_192, sizeof(void*)*7 + 13, x_173);
lean_ctor_set_uint8(x_192, sizeof(void*)*7 + 14, x_173);
lean_ctor_set_uint8(x_192, sizeof(void*)*7 + 15, x_173);
lean_ctor_set_uint8(x_192, sizeof(void*)*7 + 16, x_39);
lean_ctor_set_uint8(x_192, sizeof(void*)*7 + 17, x_39);
if (lean_is_scalar(x_172)) {
 x_193 = lean_alloc_ctor(0, 2, 0);
} else {
 x_193 = x_172;
}
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_171);
return x_193;
}
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
lean_dec(x_149);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_194 = lean_ctor_get(x_169, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_169, 1);
lean_inc(x_195);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 lean_ctor_release(x_169, 1);
 x_196 = x_169;
} else {
 lean_dec_ref(x_169);
 x_196 = lean_box(0);
}
if (lean_is_scalar(x_196)) {
 x_197 = lean_alloc_ctor(1, 2, 0);
} else {
 x_197 = x_196;
}
lean_ctor_set(x_197, 0, x_194);
lean_ctor_set(x_197, 1, x_195);
return x_197;
}
}
}
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; uint8_t x_205; uint8_t x_206; uint8_t x_207; uint8_t x_208; uint8_t x_209; uint8_t x_210; uint8_t x_211; uint8_t x_212; uint8_t x_213; uint8_t x_214; uint8_t x_215; uint8_t x_216; uint8_t x_217; uint8_t x_218; uint8_t x_219; uint8_t x_220; uint8_t x_221; uint8_t x_222; lean_object* x_223; 
lean_dec(x_38);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_198 = lean_box(0);
x_199 = lean_unsigned_to_nat(8u);
x_200 = lean_unsigned_to_nat(5u);
x_201 = lean_unsigned_to_nat(1000u);
x_202 = lean_unsigned_to_nat(1u);
x_203 = lean_unsigned_to_nat(10000u);
x_204 = lean_alloc_ctor(0, 7, 18);
lean_ctor_set(x_204, 0, x_199);
lean_ctor_set(x_204, 1, x_200);
lean_ctor_set(x_204, 2, x_200);
lean_ctor_set(x_204, 3, x_201);
lean_ctor_set(x_204, 4, x_202);
lean_ctor_set(x_204, 5, x_201);
lean_ctor_set(x_204, 6, x_203);
x_205 = lean_unbox(x_198);
lean_ctor_set_uint8(x_204, sizeof(void*)*7, x_205);
x_206 = lean_unbox(x_40);
lean_ctor_set_uint8(x_204, sizeof(void*)*7 + 1, x_206);
x_207 = lean_unbox(x_40);
lean_ctor_set_uint8(x_204, sizeof(void*)*7 + 2, x_207);
x_208 = lean_unbox(x_40);
lean_ctor_set_uint8(x_204, sizeof(void*)*7 + 3, x_208);
x_209 = lean_unbox(x_198);
lean_ctor_set_uint8(x_204, sizeof(void*)*7 + 4, x_209);
x_210 = lean_unbox(x_198);
lean_ctor_set_uint8(x_204, sizeof(void*)*7 + 5, x_210);
x_211 = lean_unbox(x_40);
lean_ctor_set_uint8(x_204, sizeof(void*)*7 + 6, x_211);
x_212 = lean_unbox(x_198);
lean_ctor_set_uint8(x_204, sizeof(void*)*7 + 7, x_212);
x_213 = lean_unbox(x_40);
lean_ctor_set_uint8(x_204, sizeof(void*)*7 + 8, x_213);
x_214 = lean_unbox(x_40);
lean_ctor_set_uint8(x_204, sizeof(void*)*7 + 9, x_214);
x_215 = lean_unbox(x_40);
lean_ctor_set_uint8(x_204, sizeof(void*)*7 + 10, x_215);
x_216 = lean_unbox(x_40);
lean_ctor_set_uint8(x_204, sizeof(void*)*7 + 11, x_216);
x_217 = lean_unbox(x_198);
lean_ctor_set_uint8(x_204, sizeof(void*)*7 + 12, x_217);
x_218 = lean_unbox(x_40);
lean_ctor_set_uint8(x_204, sizeof(void*)*7 + 13, x_218);
x_219 = lean_unbox(x_40);
lean_ctor_set_uint8(x_204, sizeof(void*)*7 + 14, x_219);
x_220 = lean_unbox(x_40);
lean_ctor_set_uint8(x_204, sizeof(void*)*7 + 15, x_220);
x_221 = lean_unbox(x_198);
lean_ctor_set_uint8(x_204, sizeof(void*)*7 + 16, x_221);
x_222 = lean_unbox(x_198);
lean_ctor_set_uint8(x_204, sizeof(void*)*7 + 17, x_222);
x_223 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_223, 0, x_204);
lean_ctor_set(x_223, 1, x_9);
return x_223;
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
x_29 = l_Lean_Exception_toMessageData(x_10);
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_mk_string_unchecked("", 0, 0);
x_32 = l_Lean_stringToMessageData(x_31);
lean_dec(x_31);
x_33 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_33, x_12, x_14, x_19, x_16, x_11, x_18, x_15);
lean_dec(x_18);
lean_dec(x_11);
lean_dec(x_16);
lean_dec(x_19);
lean_dec(x_14);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindConfig(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_elabGrindConfig___redArg(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindConfig___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_elabGrindConfig___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindConfig___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_elabGrindConfig(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___Lean_filterFieldList___at_____private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___Lean_resolveGlobalConst___at___Lean_resolveGlobalConstNoOverload___at___Lean_Elab_Tactic_elabGrindPattern_spec__0_spec__0_spec__0_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_9 = lean_mk_string_unchecked("unknown constant '", 18, 18);
x_10 = l_Lean_stringToMessageData(x_9);
lean_dec(x_9);
x_11 = lean_box(0);
x_12 = lean_unbox(x_11);
x_13 = l_Lean_MessageData_ofConstName(x_1, x_12);
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_mk_string_unchecked("'", 1, 1);
x_16 = l_Lean_stringToMessageData(x_15);
lean_dec(x_15);
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_throwUnknownIdentifier___at___Lean_Elab_Term_resolveName_process_spec__0(lean_box(0), x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___Lean_filterFieldList___at_____private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___Lean_resolveGlobalConst___at___Lean_resolveGlobalConstNoOverload___at___Lean_Elab_Tactic_elabGrindPattern_spec__0_spec__0_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwUnknownConstant___at___Lean_filterFieldList___at_____private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___Lean_resolveGlobalConst___at___Lean_resolveGlobalConstNoOverload___at___Lean_Elab_Tactic_elabGrindPattern_spec__0_spec__0_spec__0_spec__0_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___at_____private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___Lean_resolveGlobalConst___at___Lean_resolveGlobalConstNoOverload___at___Lean_Elab_Tactic_elabGrindPattern_spec__0_spec__0_spec__0_spec__0___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_box(0);
x_11 = l_List_mapTR_loop___at___Lean_filterFieldList___at___Lean_realizeGlobalConstCore_spec__0_spec__1(x_1, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___at_____private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___Lean_resolveGlobalConst___at___Lean_resolveGlobalConstNoOverload___at___Lean_Elab_Tactic_elabGrindPattern_spec__0_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_box(0);
x_11 = l_List_filterTR_loop___at___Lean_filterFieldList___at___Lean_realizeGlobalConstCore_spec__0_spec__0(x_2, x_10);
x_12 = l_List_isEmpty___redArg(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_1);
x_13 = lean_box(0);
x_14 = l_Lean_filterFieldList___at_____private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___Lean_resolveGlobalConst___at___Lean_resolveGlobalConstNoOverload___at___Lean_Elab_Tactic_elabGrindPattern_spec__0_spec__0_spec__0_spec__0___lam__0(x_11, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
return x_14;
}
else
{
lean_object* x_15; uint8_t x_16; 
lean_dec(x_11);
x_15 = l_Lean_throwUnknownConstant___at___Lean_filterFieldList___at_____private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___Lean_resolveGlobalConst___at___Lean_resolveGlobalConstNoOverload___at___Lean_Elab_Tactic_elabGrindPattern_spec__0_spec__0_spec__0_spec__0_spec__0___redArg(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
return x_15;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_15);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___Lean_resolveGlobalConst___at___Lean_resolveGlobalConstNoOverload___at___Lean_Elab_Tactic_elabGrindPattern_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_inc(x_6);
lean_inc(x_1);
x_9 = l_Lean_resolveGlobalName___at___Lean_resolveLocalName_loop___at___Lean_resolveLocalName___at___Lean_Elab_Term_isLocalIdent_x3f_spec__0_spec__9_spec__9___redArg(x_1, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_filterFieldList___at_____private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___Lean_resolveGlobalConst___at___Lean_resolveGlobalConstNoOverload___at___Lean_Elab_Tactic_elabGrindPattern_spec__0_spec__0_spec__0_spec__0(x_1, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
lean_dec(x_6);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___at___Lean_resolveGlobalConst___at___Lean_resolveGlobalConstNoOverload___at___Lean_Elab_Tactic_elabGrindPattern_spec__0_spec__0_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_1) == 3)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 3);
lean_inc(x_11);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_mk_empty_array_with_capacity(x_12);
x_14 = l_List_filterMapTR_go___at___Lean_preprocessSyntaxAndResolve___at___Lean_realizeGlobalConst_spec__0_spec__0(x_11, x_13);
x_15 = l_List_isEmpty___redArg(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_9);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_14);
x_17 = lean_ctor_get(x_7, 5);
x_18 = l_Lean_replaceRef(x_1, x_17);
lean_dec(x_1);
x_19 = lean_ctor_get(x_7, 0);
x_20 = lean_ctor_get(x_7, 1);
x_21 = lean_ctor_get(x_7, 2);
x_22 = lean_ctor_get(x_7, 3);
x_23 = lean_ctor_get(x_7, 4);
x_24 = lean_ctor_get(x_7, 6);
x_25 = lean_ctor_get(x_7, 7);
x_26 = lean_ctor_get(x_7, 8);
x_27 = lean_ctor_get(x_7, 9);
x_28 = lean_ctor_get(x_7, 10);
x_29 = lean_ctor_get_uint8(x_7, sizeof(void*)*13);
x_30 = lean_ctor_get(x_7, 11);
x_31 = lean_ctor_get_uint8(x_7, sizeof(void*)*13 + 1);
x_32 = lean_ctor_get(x_7, 12);
lean_inc(x_32);
lean_inc(x_30);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
x_33 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_33, 0, x_19);
lean_ctor_set(x_33, 1, x_20);
lean_ctor_set(x_33, 2, x_21);
lean_ctor_set(x_33, 3, x_22);
lean_ctor_set(x_33, 4, x_23);
lean_ctor_set(x_33, 5, x_18);
lean_ctor_set(x_33, 6, x_24);
lean_ctor_set(x_33, 7, x_25);
lean_ctor_set(x_33, 8, x_26);
lean_ctor_set(x_33, 9, x_27);
lean_ctor_set(x_33, 10, x_28);
lean_ctor_set(x_33, 11, x_30);
lean_ctor_set(x_33, 12, x_32);
lean_ctor_set_uint8(x_33, sizeof(void*)*13, x_29);
lean_ctor_set_uint8(x_33, sizeof(void*)*13 + 1, x_31);
x_34 = lean_apply_8(x_2, x_10, x_3, x_4, x_5, x_6, x_33, x_8, x_9);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_2);
x_35 = lean_mk_string_unchecked("expected identifier", 19, 19);
x_36 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_37 = l_Lean_MessageData_ofFormat(x_36);
x_38 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__2___redArg(x_1, x_37, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_38;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst___at___Lean_resolveGlobalConstNoOverload___at___Lean_Elab_Tactic_elabGrindPattern_spec__0_spec__0___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___Lean_resolveGlobalConst___at___Lean_resolveGlobalConstNoOverload___at___Lean_Elab_Tactic_elabGrindPattern_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst___at___Lean_resolveGlobalConstNoOverload___at___Lean_Elab_Tactic_elabGrindPattern_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_closure((void*)(l_Lean_resolveGlobalConst___at___Lean_resolveGlobalConstNoOverload___at___Lean_Elab_Tactic_elabGrindPattern_spec__0_spec__0___lam__0___boxed), 8, 0);
x_10 = l_Lean_preprocessSyntaxAndResolve___at___Lean_resolveGlobalConst___at___Lean_resolveGlobalConstNoOverload___at___Lean_Elab_Tactic_elabGrindPattern_spec__0_spec__0_spec__3(x_1, x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_ensureNonAmbiguous___at___Lean_resolveGlobalConstNoOverload___at___Lean_Elab_Tactic_elabGrindPattern_spec__0_spec__5_spec__5___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_ensureNonAmbiguous___at___Lean_resolveGlobalConstNoOverload___at___Lean_Elab_Tactic_elabGrindPattern_spec__0_spec__5_spec__5___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_12 = lean_apply_7(x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_apply_8(x_4, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_16 = !lean_is_exclusive(x_12);
if (x_16 == 0)
{
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_12, 0);
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_12);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_ensureNonAmbiguous___at___Lean_resolveGlobalConstNoOverload___at___Lean_Elab_Tactic_elabGrindPattern_spec__0_spec__5_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_9 = lean_alloc_closure((void*)(l_panic___at___Lean_ensureNonAmbiguous___at___Lean_resolveGlobalConstNoOverload___at___Lean_Elab_Tactic_elabGrindPattern_spec__0_spec__5_spec__5___lam__0___boxed), 9, 0);
x_10 = lean_alloc_closure((void*)(l_panic___at___Lean_ensureNonAmbiguous___at___Lean_resolveGlobalConstNoOverload___at___Lean_Elab_Tactic_elabGrindPattern_spec__0_spec__5_spec__5___lam__1), 11, 0);
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__0___boxed), 7, 0);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__1), 9, 0);
x_13 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__0___boxed), 5, 0);
x_14 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__1), 7, 0);
x_15 = l_instMonadEIO(lean_box(0));
x_16 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
lean_inc(x_18);
x_19 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_19, 0, x_18);
x_20 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_20, 0, x_18);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_closure((void*)(l_instMonadEIO___lam__1), 5, 0);
x_23 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_23, 0, x_22);
x_24 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_24, 0, x_23);
x_25 = lean_alloc_closure((void*)(l_instMonadEIO___lam__2), 5, 0);
x_26 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_26, 0, x_25);
x_27 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_27, 0, x_26);
x_28 = lean_alloc_closure((void*)(l_EStateM_seqRight), 7, 2);
lean_closure_set(x_28, 0, lean_box(0));
lean_closure_set(x_28, 1, lean_box(0));
x_29 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_29, 0, x_28);
x_30 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_30, 0, x_29);
lean_inc(x_30);
lean_inc(x_27);
lean_inc(x_24);
x_31 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_31, 0, x_21);
lean_ctor_set(x_31, 1, x_13);
lean_ctor_set(x_31, 2, x_24);
lean_ctor_set(x_31, 3, x_27);
lean_ctor_set(x_31, 4, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_14);
x_33 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_32);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec(x_34);
lean_inc(x_35);
x_36 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_36, 0, x_35);
x_37 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_37, 0, x_35);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_39, 0, x_24);
x_40 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_40, 0, x_39);
x_41 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_41, 0, x_27);
x_42 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_42, 0, x_41);
x_43 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_43, 0, x_30);
x_44 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_44, 0, x_43);
lean_inc(x_44);
lean_inc(x_42);
lean_inc(x_40);
x_45 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_45, 0, x_38);
lean_ctor_set(x_45, 1, x_11);
lean_ctor_set(x_45, 2, x_40);
lean_ctor_set(x_45, 3, x_42);
lean_ctor_set(x_45, 4, x_44);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_12);
x_47 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_46);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
lean_dec(x_47);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
lean_dec(x_48);
lean_inc(x_49);
x_50 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_50, 0, x_49);
x_51 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_51, 0, x_49);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_53, 0, x_40);
x_54 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_54, 0, x_53);
x_55 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_55, 0, x_42);
x_56 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_56, 0, x_55);
x_57 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_57, 0, x_44);
x_58 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_58, 0, x_57);
x_59 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_59, 0, x_52);
lean_ctor_set(x_59, 1, x_9);
lean_ctor_set(x_59, 2, x_54);
lean_ctor_set(x_59, 3, x_56);
lean_ctor_set(x_59, 4, x_58);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_10);
x_61 = lean_box(0);
x_62 = l_instInhabitedOfMonad___redArg(x_60, x_61);
x_63 = lean_panic_fn(x_62, x_1);
x_64 = lean_apply_7(x_63, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_64;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNonAmbiguous___at___Lean_resolveGlobalConstNoOverload___at___Lean_Elab_Tactic_elabGrindPattern_spec__0_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_1);
x_10 = lean_mk_string_unchecked("Lean.ResolveName", 16, 16);
x_11 = lean_mk_string_unchecked("Lean.ensureNonAmbiguous", 23, 23);
x_12 = lean_unsigned_to_nat(367u);
x_13 = lean_unsigned_to_nat(11u);
x_14 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_15 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_10, x_11, x_12, x_13, x_14);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
x_16 = l_panic___at___Lean_ensureNonAmbiguous___at___Lean_resolveGlobalConstNoOverload___at___Lean_Elab_Tactic_elabGrindPattern_spec__0_spec__5_spec__5(x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_16;
}
else
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_2, 1);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_2);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_2, 1);
lean_dec(x_19);
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 1, x_9);
return x_2;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_2, 0);
lean_inc(x_20);
lean_dec(x_2);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_9);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_17);
x_22 = lean_mk_string_unchecked("ambiguous identifier '", 22, 22);
x_23 = lean_box(0);
x_24 = lean_box(0);
x_25 = lean_unbox(x_24);
lean_inc(x_1);
x_26 = l_Lean_Syntax_formatStx(x_1, x_23, x_25);
x_27 = lean_unsigned_to_nat(120u);
x_28 = lean_unsigned_to_nat(0u);
x_29 = lean_format_pretty(x_26, x_27, x_28, x_28);
x_30 = lean_string_append(x_22, x_29);
lean_dec(x_29);
x_31 = lean_mk_string_unchecked("', possible interpretations: ", 29, 29);
x_32 = lean_string_append(x_30, x_31);
lean_dec(x_31);
x_33 = lean_box(0);
x_34 = l_List_mapTR_loop___at___Lean_ensureNonAmbiguous___at___Lean_realizeGlobalConstNoOverload_spec__0_spec__1(x_2, x_33);
x_35 = l_List_toString___at___Lean_ensureNoOverload___at___Lean_realizeGlobalConstNoOverloadCore_spec__0_spec__1(x_34);
lean_dec(x_34);
x_36 = lean_string_append(x_32, x_35);
lean_dec(x_35);
x_37 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = l_Lean_MessageData_ofFormat(x_37);
x_39 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__2___redArg(x_1, x_38, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverload___at___Lean_Elab_Tactic_elabGrindPattern_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_9 = l_Lean_resolveGlobalConst___at___Lean_resolveGlobalConstNoOverload___at___Lean_Elab_Tactic_elabGrindPattern_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_ensureNonAmbiguous___at___Lean_resolveGlobalConstNoOverload___at___Lean_Elab_Tactic_elabGrindPattern_spec__0_spec__5(x_1, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = !lean_is_exclusive(x_9);
if (x_13 == 0)
{
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_9, 0);
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_9);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Elab_Tactic_elabGrindPattern_spec__8_spec__8(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_mk_string_unchecked("ident", 5, 5);
x_14 = lean_usize_dec_lt(x_4, x_3);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_5);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_31; lean_object* x_39; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = l_Lean_Syntax_getArg(x_1, x_16);
x_18 = l_Lean_Name_mkStr1(x_13);
x_19 = lean_box(0);
x_20 = l_Lean_Syntax_isOfKind(x_17, x_18);
lean_dec(x_18);
x_21 = lean_array_uget(x_5, x_4);
x_22 = lean_box(0);
x_23 = lean_array_uset(x_5, x_4, x_22);
lean_inc(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_39 = l_Lean_Elab_Term_elabTerm(x_21, x_19, x_20, x_20, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_42 = l_Lean_Elab_Term_synthesizeSyntheticMVarsUsingDefault(x_6, x_7, x_8, x_9, x_10, x_11, x_41);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_44 = l_Lean_instantiateMVars___at___Lean_Elab_Term_MVarErrorInfo_logError_spec__0___redArg(x_40, x_9, x_43);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_47 = l_Lean_Meta_Grind_preprocessPattern(x_45, x_20, x_8, x_9, x_10, x_11, x_46);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_expr_abstract(x_48, x_2);
lean_dec(x_48);
x_24 = x_50;
x_25 = x_49;
goto block_30;
}
else
{
x_31 = x_47;
goto block_38;
}
}
else
{
uint8_t x_51; 
lean_dec(x_40);
lean_dec(x_23);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_51 = !lean_is_exclusive(x_42);
if (x_51 == 0)
{
return x_42;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_42, 0);
x_53 = lean_ctor_get(x_42, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_42);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
x_31 = x_39;
goto block_38;
}
block_30:
{
size_t x_26; size_t x_27; lean_object* x_28; 
x_26 = lean_usize_of_nat(x_16);
x_27 = lean_usize_add(x_4, x_26);
x_28 = lean_array_uset(x_23, x_4, x_24);
x_4 = x_27;
x_5 = x_28;
x_12 = x_25;
goto _start;
}
block_38:
{
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_24 = x_32;
x_25 = x_33;
goto block_30;
}
else
{
uint8_t x_34; 
lean_dec(x_23);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_34 = !lean_is_exclusive(x_31);
if (x_34 == 0)
{
return x_31;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_31, 0);
x_36 = lean_ctor_get(x_31, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_31);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_elabGrindPattern_spec__8(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_mk_string_unchecked("ident", 5, 5);
x_14 = lean_usize_dec_lt(x_4, x_3);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_5);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_31; lean_object* x_39; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = l_Lean_Syntax_getArg(x_1, x_16);
x_18 = l_Lean_Name_mkStr1(x_13);
x_19 = lean_box(0);
x_20 = l_Lean_Syntax_isOfKind(x_17, x_18);
lean_dec(x_18);
x_21 = lean_array_uget(x_5, x_4);
x_22 = lean_box(0);
x_23 = lean_array_uset(x_5, x_4, x_22);
lean_inc(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_39 = l_Lean_Elab_Term_elabTerm(x_21, x_19, x_20, x_20, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_42 = l_Lean_Elab_Term_synthesizeSyntheticMVarsUsingDefault(x_6, x_7, x_8, x_9, x_10, x_11, x_41);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_44 = l_Lean_instantiateMVars___at___Lean_Elab_Term_MVarErrorInfo_logError_spec__0___redArg(x_40, x_9, x_43);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_47 = l_Lean_Meta_Grind_preprocessPattern(x_45, x_20, x_8, x_9, x_10, x_11, x_46);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_expr_abstract(x_48, x_2);
lean_dec(x_48);
x_24 = x_50;
x_25 = x_49;
goto block_30;
}
else
{
x_31 = x_47;
goto block_38;
}
}
else
{
uint8_t x_51; 
lean_dec(x_40);
lean_dec(x_23);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_51 = !lean_is_exclusive(x_42);
if (x_51 == 0)
{
return x_42;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_42, 0);
x_53 = lean_ctor_get(x_42, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_42);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
x_31 = x_39;
goto block_38;
}
block_30:
{
size_t x_26; size_t x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_usize_of_nat(x_16);
x_27 = lean_usize_add(x_4, x_26);
x_28 = lean_array_uset(x_23, x_4, x_24);
x_29 = l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Elab_Tactic_elabGrindPattern_spec__8_spec__8(x_1, x_2, x_3, x_27, x_28, x_6, x_7, x_8, x_9, x_10, x_11, x_25);
return x_29;
}
block_38:
{
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_24 = x_32;
x_25 = x_33;
goto block_30;
}
else
{
uint8_t x_34; 
lean_dec(x_23);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_34 = !lean_is_exclusive(x_31);
if (x_34 == 0)
{
return x_31;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_31, 0);
x_36 = lean_ctor_get(x_31, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_31);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindPattern___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; size_t x_14; lean_object* x_15; size_t x_16; lean_object* x_17; 
x_13 = l_Lean_Syntax_TSepArray_getElems___redArg(x_1);
x_14 = lean_array_size(x_13);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_usize_of_nat(x_15);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_17 = l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_elabGrindPattern_spec__8(x_2, x_4, x_14, x_16, x_13, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_array_get_size(x_4);
x_21 = lean_array_to_list(x_18);
x_22 = lean_box(9);
x_23 = lean_unbox(x_22);
x_24 = l_Lean_Meta_Grind_addEMatchTheorem(x_3, x_20, x_21, x_23, x_8, x_9, x_10, x_11, x_19);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
x_25 = !lean_is_exclusive(x_17);
if (x_25 == 0)
{
return x_17;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_17, 0);
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_17);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindPattern___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_11 = l_Lean_resolveGlobalConstNoOverload___at___Lean_Elab_Tactic_elabGrindPattern_spec__0(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_4);
lean_inc(x_12);
x_14 = l_Lean_mkConstWithLevelParams___at___Lean_Elab_checkNotAlreadyDeclared___at___Lean_Elab_applyVisibility___at___Lean_Elab_mkDeclName___at___Lean_Elab_expandDeclId___at___Lean_Elab_Term_expandDeclId_spec__0_spec__1_spec__3_spec__3_spec__3(x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_22; lean_object* x_23; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_box(0);
x_18 = lean_box(0);
x_19 = lean_box(0);
x_20 = lean_box(0);
x_21 = lean_unbox(x_20);
x_22 = lean_unbox(x_20);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_23 = l_Lean_Elab_Term_addTermInfo(x_1, x_15, x_17, x_18, x_19, x_21, x_22, x_4, x_5, x_6, x_7, x_8, x_9, x_16);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
lean_inc(x_4);
lean_inc(x_12);
x_25 = l_Lean_getConstInfo___at_____private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_elabConfig_spec__0(x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_elabGrindPattern___lam__0___boxed), 12, 3);
lean_closure_set(x_28, 0, x_2);
lean_closure_set(x_28, 1, x_3);
lean_closure_set(x_28, 2, x_12);
x_29 = l_Lean_ConstantInfo_type(x_26);
lean_dec(x_26);
x_30 = lean_unbox(x_20);
x_31 = l_Lean_Meta_forallTelescope___at_____private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial_spec__0___redArg(x_29, x_28, x_30, x_4, x_5, x_6, x_7, x_8, x_9, x_27);
return x_31;
}
else
{
uint8_t x_32; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_32 = !lean_is_exclusive(x_25);
if (x_32 == 0)
{
return x_25;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_25, 0);
x_34 = lean_ctor_get(x_25, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_25);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_36 = !lean_is_exclusive(x_23);
if (x_36 == 0)
{
return x_23;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_23, 0);
x_38 = lean_ctor_get(x_23, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_23);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_14);
if (x_40 == 0)
{
return x_14;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_14, 0);
x_42 = lean_ctor_get(x_14, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_14);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_11);
if (x_44 == 0)
{
return x_11;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_11, 0);
x_46 = lean_ctor_get(x_11, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_11);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindPattern(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_mk_string_unchecked("Lean", 4, 4);
x_6 = lean_mk_string_unchecked("Parser", 6, 6);
x_7 = lean_mk_string_unchecked("Command", 7, 7);
x_8 = lean_mk_string_unchecked("grindPattern", 12, 12);
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
x_14 = lean_mk_string_unchecked("ident", 5, 5);
x_15 = l_Lean_Name_mkStr1(x_14);
lean_inc(x_13);
x_16 = l_Lean_Syntax_isOfKind(x_13, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_13);
lean_dec(x_1);
x_17 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_2, x_3, x_4);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_unsigned_to_nat(3u);
x_19 = l_Lean_Syntax_getArg(x_1, x_18);
x_20 = l_Lean_Syntax_getArgs(x_19);
lean_dec(x_19);
x_21 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_elabGrindPattern___lam__1), 10, 3);
lean_closure_set(x_21, 0, x_13);
lean_closure_set(x_21, 1, x_20);
lean_closure_set(x_21, 2, x_1);
x_22 = l_Lean_Elab_Command_liftTermElabM___redArg(x_21, x_2, x_3, x_4);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___Lean_filterFieldList___at_____private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___Lean_resolveGlobalConst___at___Lean_resolveGlobalConstNoOverload___at___Lean_Elab_Tactic_elabGrindPattern_spec__0_spec__0_spec__0_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwUnknownConstant___at___Lean_filterFieldList___at_____private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___Lean_resolveGlobalConst___at___Lean_resolveGlobalConstNoOverload___at___Lean_Elab_Tactic_elabGrindPattern_spec__0_spec__0_spec__0_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___Lean_filterFieldList___at_____private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___Lean_resolveGlobalConst___at___Lean_resolveGlobalConstNoOverload___at___Lean_Elab_Tactic_elabGrindPattern_spec__0_spec__0_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwUnknownConstant___at___Lean_filterFieldList___at_____private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___Lean_resolveGlobalConst___at___Lean_resolveGlobalConstNoOverload___at___Lean_Elab_Tactic_elabGrindPattern_spec__0_spec__0_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___at_____private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___Lean_resolveGlobalConst___at___Lean_resolveGlobalConstNoOverload___at___Lean_Elab_Tactic_elabGrindPattern_spec__0_spec__0_spec__0_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_filterFieldList___at_____private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___Lean_resolveGlobalConst___at___Lean_resolveGlobalConstNoOverload___at___Lean_Elab_Tactic_elabGrindPattern_spec__0_spec__0_spec__0_spec__0___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Lean_filterFieldList___at_____private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___Lean_resolveGlobalConst___at___Lean_resolveGlobalConstNoOverload___at___Lean_Elab_Tactic_elabGrindPattern_spec__0_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_filterFieldList___at_____private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___Lean_resolveGlobalConst___at___Lean_resolveGlobalConstNoOverload___at___Lean_Elab_Tactic_elabGrindPattern_spec__0_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___Lean_resolveGlobalConst___at___Lean_resolveGlobalConstNoOverload___at___Lean_Elab_Tactic_elabGrindPattern_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___Lean_resolveGlobalConst___at___Lean_resolveGlobalConstNoOverload___at___Lean_Elab_Tactic_elabGrindPattern_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___at___Lean_resolveGlobalConst___at___Lean_resolveGlobalConstNoOverload___at___Lean_Elab_Tactic_elabGrindPattern_spec__0_spec__0_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_preprocessSyntaxAndResolve___at___Lean_resolveGlobalConst___at___Lean_resolveGlobalConstNoOverload___at___Lean_Elab_Tactic_elabGrindPattern_spec__0_spec__0_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst___at___Lean_resolveGlobalConstNoOverload___at___Lean_Elab_Tactic_elabGrindPattern_spec__0_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_resolveGlobalConst___at___Lean_resolveGlobalConstNoOverload___at___Lean_Elab_Tactic_elabGrindPattern_spec__0_spec__0___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst___at___Lean_resolveGlobalConstNoOverload___at___Lean_Elab_Tactic_elabGrindPattern_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_resolveGlobalConst___at___Lean_resolveGlobalConstNoOverload___at___Lean_Elab_Tactic_elabGrindPattern_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_ensureNonAmbiguous___at___Lean_resolveGlobalConstNoOverload___at___Lean_Elab_Tactic_elabGrindPattern_spec__0_spec__5_spec__5___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_panic___at___Lean_ensureNonAmbiguous___at___Lean_resolveGlobalConstNoOverload___at___Lean_Elab_Tactic_elabGrindPattern_spec__0_spec__5_spec__5___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Elab_Tactic_elabGrindPattern_spec__8_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Elab_Tactic_elabGrindPattern_spec__8_spec__8(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_elabGrindPattern_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_elabGrindPattern_spec__8(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindPattern___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Tactic_elabGrindPattern___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindPattern___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Tactic_elabGrindPattern(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_elabGrindPattern__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Command", 7, 7);
x_6 = lean_mk_string_unchecked("grindPattern", 12, 12);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("Elab", 4, 4);
x_9 = lean_mk_string_unchecked("Tactic", 6, 6);
x_10 = lean_mk_string_unchecked("elabGrindPattern", 16, 16);
x_11 = l_Lean_Name_mkStr4(x_3, x_8, x_9, x_10);
x_12 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_elabGrindPattern___boxed), 4, 0);
x_13 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_11, x_12, x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabResetGrindAttrs___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Lean_Meta_Grind_resetCasesExt___redArg(x_6, x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Lean_Meta_Grind_resetEMatchTheoremsExt(x_5, x_6, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabResetGrindAttrs___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_elabResetGrindAttrs___redArg___lam__0___boxed), 7, 0);
x_5 = l_Lean_Elab_Command_liftTermElabM___redArg(x_4, x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabResetGrindAttrs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Tactic_elabResetGrindAttrs___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabResetGrindAttrs___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Tactic_elabResetGrindAttrs___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabResetGrindAttrs___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Tactic_elabResetGrindAttrs___redArg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabResetGrindAttrs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Tactic_elabResetGrindAttrs(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_elabResetGrindAttrs__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("resetGrindAttrs", 15, 15);
lean_inc(x_3);
x_6 = l_Lean_Name_mkStr3(x_3, x_4, x_5);
x_7 = lean_mk_string_unchecked("Elab", 4, 4);
x_8 = lean_mk_string_unchecked("Tactic", 6, 6);
x_9 = lean_mk_string_unchecked("elabResetGrindAttrs", 19, 19);
x_10 = l_Lean_Name_mkStr4(x_3, x_7, x_8, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_elabResetGrindAttrs___boxed), 4, 0);
x_12 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_6, x_10, x_11, x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_elabInitGrindNorm_spec__0___redArg(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_2, x_1);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_5);
lean_dec(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_array_uget(x_3, x_2);
x_10 = lean_box(0);
lean_inc(x_5);
lean_inc(x_4);
x_11 = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(x_9, x_10, x_4, x_5, x_6);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_box(0);
x_15 = lean_array_uset(x_3, x_2, x_14);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_usize_of_nat(x_16);
x_18 = lean_usize_add(x_2, x_17);
x_19 = lean_array_uset(x_15, x_2, x_12);
x_2 = x_18;
x_3 = x_19;
x_6 = x_13;
goto _start;
}
else
{
uint8_t x_21; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_21 = !lean_is_exclusive(x_11);
if (x_21 == 0)
{
return x_11;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_11, 0);
x_23 = lean_ctor_get(x_11, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_11);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_elabInitGrindNorm_spec__0(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_elabInitGrindNorm_spec__0___redArg(x_1, x_2, x_3, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabInitGrindNorm___lam__0(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
x_12 = l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_elabInitGrindNorm_spec__0___redArg(x_1, x_2, x_3, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; size_t x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_array_size(x_4);
lean_inc(x_10);
lean_inc(x_9);
x_16 = l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_elabInitGrindNorm_spec__0___redArg(x_15, x_2, x_4, x_9, x_10, x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Meta_Grind_registerNormTheorems(x_13, x_17, x_7, x_8, x_9, x_10, x_18);
lean_dec(x_17);
lean_dec(x_13);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_20 = !lean_is_exclusive(x_16);
if (x_20 == 0)
{
return x_16;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_16, 0);
x_22 = lean_ctor_get(x_16, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_16);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
else
{
uint8_t x_24; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_24 = !lean_is_exclusive(x_12);
if (x_24 == 0)
{
return x_12;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_12, 0);
x_26 = lean_ctor_get(x_12, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_12);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabInitGrindNorm(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_mk_string_unchecked("Lean", 4, 4);
x_6 = lean_mk_string_unchecked("Parser", 6, 6);
x_7 = lean_mk_string_unchecked("Command", 7, 7);
x_8 = lean_mk_string_unchecked("initGrindNorm", 13, 13);
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; lean_object* x_19; size_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
x_14 = lean_unsigned_to_nat(3u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
lean_dec(x_1);
x_16 = l_Lean_Syntax_getArgs(x_15);
lean_dec(x_15);
x_17 = l_Lean_Syntax_getArgs(x_13);
lean_dec(x_13);
x_18 = lean_array_size(x_17);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_usize_of_nat(x_19);
x_21 = lean_box_usize(x_18);
x_22 = lean_box_usize(x_20);
x_23 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_elabInitGrindNorm___lam__0___boxed), 11, 4);
lean_closure_set(x_23, 0, x_21);
lean_closure_set(x_23, 1, x_22);
lean_closure_set(x_23, 2, x_17);
lean_closure_set(x_23, 3, x_16);
x_24 = l_Lean_Elab_Command_liftTermElabM___redArg(x_23, x_2, x_3, x_4);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_elabInitGrindNorm_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_elabInitGrindNorm_spec__0___redArg(x_7, x_8, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_elabInitGrindNorm_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_elabInitGrindNorm_spec__0(x_11, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabInitGrindNorm___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = l_Lean_Elab_Tactic_elabInitGrindNorm___lam__0(x_12, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabInitGrindNorm___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Tactic_elabInitGrindNorm(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_elabInitGrindNorm__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Command", 7, 7);
x_6 = lean_mk_string_unchecked("initGrindNorm", 13, 13);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("Elab", 4, 4);
x_9 = lean_mk_string_unchecked("Tactic", 6, 6);
x_10 = lean_mk_string_unchecked("elabInitGrindNorm", 17, 17);
x_11 = l_Lean_Name_mkStr4(x_3, x_8, x_9, x_10);
x_12 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_elabInitGrindNorm___boxed), 4, 0);
x_13 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_11, x_12, x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_54; 
lean_inc(x_2);
x_54 = l_Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0(x_2, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
switch (lean_obj_tag(x_55)) {
case 0:
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; uint8_t x_59; 
lean_dec(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = lean_box(2);
x_58 = lean_unbox(x_57);
x_59 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_beqEMatchTheoremKind____x40_Lean_Meta_Tactic_Grind_EMatchTheorem___hyg_1361_(x_3, x_58);
if (x_59 == 0)
{
lean_object* x_60; 
x_60 = l_Lean_Meta_Grind_mkEMatchTheoremForDecl(x_2, x_3, x_4, x_5, x_6, x_7, x_56);
if (lean_obj_tag(x_60) == 0)
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_62 = lean_ctor_get(x_60, 0);
x_63 = lean_ctor_get(x_1, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_1, 1);
lean_inc(x_64);
x_65 = lean_ctor_get(x_1, 2);
lean_inc(x_65);
x_66 = lean_ctor_get(x_1, 3);
lean_inc(x_66);
x_67 = l_Lean_PersistentArray_push___redArg(x_66, x_62);
x_68 = lean_ctor_get(x_1, 4);
lean_inc(x_68);
x_69 = lean_ctor_get(x_1, 5);
lean_inc(x_69);
lean_dec(x_1);
x_70 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_70, 0, x_63);
lean_ctor_set(x_70, 1, x_64);
lean_ctor_set(x_70, 2, x_65);
lean_ctor_set(x_70, 3, x_67);
lean_ctor_set(x_70, 4, x_68);
lean_ctor_set(x_70, 5, x_69);
lean_ctor_set(x_60, 0, x_70);
return x_60;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_71 = lean_ctor_get(x_60, 0);
x_72 = lean_ctor_get(x_60, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_60);
x_73 = lean_ctor_get(x_1, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_1, 1);
lean_inc(x_74);
x_75 = lean_ctor_get(x_1, 2);
lean_inc(x_75);
x_76 = lean_ctor_get(x_1, 3);
lean_inc(x_76);
x_77 = l_Lean_PersistentArray_push___redArg(x_76, x_71);
x_78 = lean_ctor_get(x_1, 4);
lean_inc(x_78);
x_79 = lean_ctor_get(x_1, 5);
lean_inc(x_79);
lean_dec(x_1);
x_80 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_80, 0, x_73);
lean_ctor_set(x_80, 1, x_74);
lean_ctor_set(x_80, 2, x_75);
lean_ctor_set(x_80, 3, x_77);
lean_ctor_set(x_80, 4, x_78);
lean_ctor_set(x_80, 5, x_79);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_72);
return x_81;
}
}
else
{
uint8_t x_82; 
lean_dec(x_1);
x_82 = !lean_is_exclusive(x_60);
if (x_82 == 0)
{
return x_60;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_60, 0);
x_84 = lean_ctor_get(x_60, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_60);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
else
{
lean_object* x_86; uint8_t x_87; lean_object* x_88; 
x_86 = lean_box(0);
x_87 = lean_unbox(x_86);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_88 = l_Lean_Meta_Grind_mkEMatchTheoremForDecl(x_2, x_87, x_4, x_5, x_6, x_7, x_56);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; lean_object* x_93; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
x_91 = lean_box(1);
x_92 = lean_unbox(x_91);
x_93 = l_Lean_Meta_Grind_mkEMatchTheoremForDecl(x_2, x_92, x_4, x_5, x_6, x_7, x_90);
if (lean_obj_tag(x_93) == 0)
{
uint8_t x_94; 
x_94 = !lean_is_exclusive(x_93);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_95 = lean_ctor_get(x_93, 0);
x_96 = lean_ctor_get(x_1, 3);
lean_inc(x_96);
x_97 = lean_ctor_get(x_1, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_1, 1);
lean_inc(x_98);
x_99 = lean_ctor_get(x_1, 2);
lean_inc(x_99);
x_100 = l_Lean_PersistentArray_push___redArg(x_96, x_89);
x_101 = lean_ctor_get(x_1, 4);
lean_inc(x_101);
x_102 = lean_ctor_get(x_1, 5);
lean_inc(x_102);
lean_dec(x_1);
x_103 = l_Lean_PersistentArray_push___redArg(x_100, x_95);
x_104 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_104, 0, x_97);
lean_ctor_set(x_104, 1, x_98);
lean_ctor_set(x_104, 2, x_99);
lean_ctor_set(x_104, 3, x_103);
lean_ctor_set(x_104, 4, x_101);
lean_ctor_set(x_104, 5, x_102);
lean_ctor_set(x_93, 0, x_104);
return x_93;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_105 = lean_ctor_get(x_93, 0);
x_106 = lean_ctor_get(x_93, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_93);
x_107 = lean_ctor_get(x_1, 3);
lean_inc(x_107);
x_108 = lean_ctor_get(x_1, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_1, 1);
lean_inc(x_109);
x_110 = lean_ctor_get(x_1, 2);
lean_inc(x_110);
x_111 = l_Lean_PersistentArray_push___redArg(x_107, x_89);
x_112 = lean_ctor_get(x_1, 4);
lean_inc(x_112);
x_113 = lean_ctor_get(x_1, 5);
lean_inc(x_113);
lean_dec(x_1);
x_114 = l_Lean_PersistentArray_push___redArg(x_111, x_105);
x_115 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_115, 0, x_108);
lean_ctor_set(x_115, 1, x_109);
lean_ctor_set(x_115, 2, x_110);
lean_ctor_set(x_115, 3, x_114);
lean_ctor_set(x_115, 4, x_112);
lean_ctor_set(x_115, 5, x_113);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_106);
return x_116;
}
}
else
{
uint8_t x_117; 
lean_dec(x_89);
lean_dec(x_1);
x_117 = !lean_is_exclusive(x_93);
if (x_117 == 0)
{
return x_93;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_93, 0);
x_119 = lean_ctor_get(x_93, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_93);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
return x_120;
}
}
}
else
{
uint8_t x_121; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_121 = !lean_is_exclusive(x_88);
if (x_121 == 0)
{
return x_88;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_88, 0);
x_123 = lean_ctor_get(x_88, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_88);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
return x_124;
}
}
}
}
case 1:
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; 
lean_dec(x_55);
x_125 = lean_ctor_get(x_54, 1);
lean_inc(x_125);
lean_dec(x_54);
lean_inc(x_2);
x_126 = l_Lean_isReducible___at_____private_Lean_Meta_Basic_0__Lean_Meta_getDefInfoTemp_spec__0(x_2, x_4, x_5, x_6, x_7, x_125);
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_unbox(x_127);
lean_dec(x_127);
if (x_128 == 0)
{
uint8_t x_129; 
x_129 = !lean_is_exclusive(x_126);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; uint8_t x_134; 
x_130 = lean_ctor_get(x_126, 1);
x_131 = lean_ctor_get(x_126, 0);
lean_dec(x_131);
x_132 = lean_box(0);
x_133 = lean_unbox(x_132);
x_134 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_beqEMatchTheoremKind____x40_Lean_Meta_Tactic_Grind_EMatchTheorem___hyg_1361_(x_3, x_133);
if (x_134 == 0)
{
lean_object* x_135; uint8_t x_136; uint8_t x_137; 
x_135 = lean_box(8);
x_136 = lean_unbox(x_135);
x_137 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_beqEMatchTheoremKind____x40_Lean_Meta_Tactic_Grind_EMatchTheorem___hyg_1361_(x_3, x_136);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; 
lean_dec(x_1);
x_138 = lean_mk_string_unchecked("invalid `grind` parameter, `", 28, 28);
x_139 = l_Lean_stringToMessageData(x_138);
lean_dec(x_138);
x_140 = l_Lean_MessageData_ofName(x_2);
lean_ctor_set_tag(x_126, 7);
lean_ctor_set(x_126, 1, x_140);
lean_ctor_set(x_126, 0, x_139);
x_141 = lean_mk_string_unchecked("` is a definition, the only acceptable (and redundant) modifier is '='", 70, 70);
x_142 = l_Lean_stringToMessageData(x_141);
lean_dec(x_141);
x_143 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_143, 0, x_126);
lean_ctor_set(x_143, 1, x_142);
x_144 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_143, x_4, x_5, x_6, x_7, x_130);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_145 = !lean_is_exclusive(x_144);
if (x_145 == 0)
{
return x_144;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_144, 0);
x_147 = lean_ctor_get(x_144, 1);
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_144);
x_148 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_147);
return x_148;
}
}
else
{
lean_free_object(x_126);
x_9 = x_4;
x_10 = x_5;
x_11 = x_6;
x_12 = x_7;
x_13 = x_130;
goto block_53;
}
}
else
{
lean_free_object(x_126);
x_9 = x_4;
x_10 = x_5;
x_11 = x_6;
x_12 = x_7;
x_13 = x_130;
goto block_53;
}
}
else
{
lean_object* x_149; lean_object* x_150; uint8_t x_151; uint8_t x_152; 
x_149 = lean_ctor_get(x_126, 1);
lean_inc(x_149);
lean_dec(x_126);
x_150 = lean_box(0);
x_151 = lean_unbox(x_150);
x_152 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_beqEMatchTheoremKind____x40_Lean_Meta_Tactic_Grind_EMatchTheorem___hyg_1361_(x_3, x_151);
if (x_152 == 0)
{
lean_object* x_153; uint8_t x_154; uint8_t x_155; 
x_153 = lean_box(8);
x_154 = lean_unbox(x_153);
x_155 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_beqEMatchTheoremKind____x40_Lean_Meta_Tactic_Grind_EMatchTheorem___hyg_1361_(x_3, x_154);
if (x_155 == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
lean_dec(x_1);
x_156 = lean_mk_string_unchecked("invalid `grind` parameter, `", 28, 28);
x_157 = l_Lean_stringToMessageData(x_156);
lean_dec(x_156);
x_158 = l_Lean_MessageData_ofName(x_2);
x_159 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_159, 0, x_157);
lean_ctor_set(x_159, 1, x_158);
x_160 = lean_mk_string_unchecked("` is a definition, the only acceptable (and redundant) modifier is '='", 70, 70);
x_161 = l_Lean_stringToMessageData(x_160);
lean_dec(x_160);
x_162 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_162, 0, x_159);
lean_ctor_set(x_162, 1, x_161);
x_163 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_162, x_4, x_5, x_6, x_7, x_149);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_163, 1);
lean_inc(x_165);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 lean_ctor_release(x_163, 1);
 x_166 = x_163;
} else {
 lean_dec_ref(x_163);
 x_166 = lean_box(0);
}
if (lean_is_scalar(x_166)) {
 x_167 = lean_alloc_ctor(1, 2, 0);
} else {
 x_167 = x_166;
}
lean_ctor_set(x_167, 0, x_164);
lean_ctor_set(x_167, 1, x_165);
return x_167;
}
else
{
x_9 = x_4;
x_10 = x_5;
x_11 = x_6;
x_12 = x_7;
x_13 = x_149;
goto block_53;
}
}
else
{
x_9 = x_4;
x_10 = x_5;
x_11 = x_6;
x_12 = x_7;
x_13 = x_149;
goto block_53;
}
}
}
else
{
uint8_t x_168; 
lean_dec(x_1);
x_168 = !lean_is_exclusive(x_126);
if (x_168 == 0)
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; uint8_t x_178; 
x_169 = lean_ctor_get(x_126, 1);
x_170 = lean_ctor_get(x_126, 0);
lean_dec(x_170);
x_171 = lean_mk_string_unchecked("`", 1, 1);
x_172 = l_Lean_stringToMessageData(x_171);
lean_dec(x_171);
x_173 = l_Lean_MessageData_ofName(x_2);
lean_ctor_set_tag(x_126, 7);
lean_ctor_set(x_126, 1, x_173);
lean_ctor_set(x_126, 0, x_172);
x_174 = lean_mk_string_unchecked("` is a reducible definition, `grind` automatically unfolds them", 63, 63);
x_175 = l_Lean_stringToMessageData(x_174);
lean_dec(x_174);
x_176 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_176, 0, x_126);
lean_ctor_set(x_176, 1, x_175);
x_177 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_176, x_4, x_5, x_6, x_7, x_169);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_178 = !lean_is_exclusive(x_177);
if (x_178 == 0)
{
return x_177;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_179 = lean_ctor_get(x_177, 0);
x_180 = lean_ctor_get(x_177, 1);
lean_inc(x_180);
lean_inc(x_179);
lean_dec(x_177);
x_181 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_181, 0, x_179);
lean_ctor_set(x_181, 1, x_180);
return x_181;
}
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_182 = lean_ctor_get(x_126, 1);
lean_inc(x_182);
lean_dec(x_126);
x_183 = lean_mk_string_unchecked("`", 1, 1);
x_184 = l_Lean_stringToMessageData(x_183);
lean_dec(x_183);
x_185 = l_Lean_MessageData_ofName(x_2);
x_186 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_186, 0, x_184);
lean_ctor_set(x_186, 1, x_185);
x_187 = lean_mk_string_unchecked("` is a reducible definition, `grind` automatically unfolds them", 63, 63);
x_188 = l_Lean_stringToMessageData(x_187);
lean_dec(x_187);
x_189 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_189, 0, x_186);
lean_ctor_set(x_189, 1, x_188);
x_190 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_189, x_4, x_5, x_6, x_7, x_182);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_190, 1);
lean_inc(x_192);
if (lean_is_exclusive(x_190)) {
 lean_ctor_release(x_190, 0);
 lean_ctor_release(x_190, 1);
 x_193 = x_190;
} else {
 lean_dec_ref(x_190);
 x_193 = lean_box(0);
}
if (lean_is_scalar(x_193)) {
 x_194 = lean_alloc_ctor(1, 2, 0);
} else {
 x_194 = x_193;
}
lean_ctor_set(x_194, 0, x_191);
lean_ctor_set(x_194, 1, x_192);
return x_194;
}
}
}
case 2:
{
lean_object* x_195; lean_object* x_196; uint8_t x_197; uint8_t x_198; 
lean_dec(x_55);
x_195 = lean_ctor_get(x_54, 1);
lean_inc(x_195);
lean_dec(x_54);
x_196 = lean_box(2);
x_197 = lean_unbox(x_196);
x_198 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_beqEMatchTheoremKind____x40_Lean_Meta_Tactic_Grind_EMatchTheorem___hyg_1361_(x_3, x_197);
if (x_198 == 0)
{
lean_object* x_199; 
x_199 = l_Lean_Meta_Grind_mkEMatchTheoremForDecl(x_2, x_3, x_4, x_5, x_6, x_7, x_195);
if (lean_obj_tag(x_199) == 0)
{
uint8_t x_200; 
x_200 = !lean_is_exclusive(x_199);
if (x_200 == 0)
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_201 = lean_ctor_get(x_199, 0);
x_202 = lean_ctor_get(x_1, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_1, 1);
lean_inc(x_203);
x_204 = lean_ctor_get(x_1, 2);
lean_inc(x_204);
x_205 = lean_ctor_get(x_1, 3);
lean_inc(x_205);
x_206 = l_Lean_PersistentArray_push___redArg(x_205, x_201);
x_207 = lean_ctor_get(x_1, 4);
lean_inc(x_207);
x_208 = lean_ctor_get(x_1, 5);
lean_inc(x_208);
lean_dec(x_1);
x_209 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_209, 0, x_202);
lean_ctor_set(x_209, 1, x_203);
lean_ctor_set(x_209, 2, x_204);
lean_ctor_set(x_209, 3, x_206);
lean_ctor_set(x_209, 4, x_207);
lean_ctor_set(x_209, 5, x_208);
lean_ctor_set(x_199, 0, x_209);
return x_199;
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_210 = lean_ctor_get(x_199, 0);
x_211 = lean_ctor_get(x_199, 1);
lean_inc(x_211);
lean_inc(x_210);
lean_dec(x_199);
x_212 = lean_ctor_get(x_1, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_1, 1);
lean_inc(x_213);
x_214 = lean_ctor_get(x_1, 2);
lean_inc(x_214);
x_215 = lean_ctor_get(x_1, 3);
lean_inc(x_215);
x_216 = l_Lean_PersistentArray_push___redArg(x_215, x_210);
x_217 = lean_ctor_get(x_1, 4);
lean_inc(x_217);
x_218 = lean_ctor_get(x_1, 5);
lean_inc(x_218);
lean_dec(x_1);
x_219 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_219, 0, x_212);
lean_ctor_set(x_219, 1, x_213);
lean_ctor_set(x_219, 2, x_214);
lean_ctor_set(x_219, 3, x_216);
lean_ctor_set(x_219, 4, x_217);
lean_ctor_set(x_219, 5, x_218);
x_220 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_220, 0, x_219);
lean_ctor_set(x_220, 1, x_211);
return x_220;
}
}
else
{
uint8_t x_221; 
lean_dec(x_1);
x_221 = !lean_is_exclusive(x_199);
if (x_221 == 0)
{
return x_199;
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_222 = lean_ctor_get(x_199, 0);
x_223 = lean_ctor_get(x_199, 1);
lean_inc(x_223);
lean_inc(x_222);
lean_dec(x_199);
x_224 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_224, 0, x_222);
lean_ctor_set(x_224, 1, x_223);
return x_224;
}
}
}
else
{
lean_object* x_225; uint8_t x_226; lean_object* x_227; 
x_225 = lean_box(0);
x_226 = lean_unbox(x_225);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_227 = l_Lean_Meta_Grind_mkEMatchTheoremForDecl(x_2, x_226, x_4, x_5, x_6, x_7, x_195);
if (lean_obj_tag(x_227) == 0)
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; uint8_t x_231; lean_object* x_232; 
x_228 = lean_ctor_get(x_227, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_227, 1);
lean_inc(x_229);
lean_dec(x_227);
x_230 = lean_box(1);
x_231 = lean_unbox(x_230);
x_232 = l_Lean_Meta_Grind_mkEMatchTheoremForDecl(x_2, x_231, x_4, x_5, x_6, x_7, x_229);
if (lean_obj_tag(x_232) == 0)
{
uint8_t x_233; 
x_233 = !lean_is_exclusive(x_232);
if (x_233 == 0)
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
x_234 = lean_ctor_get(x_232, 0);
x_235 = lean_ctor_get(x_1, 3);
lean_inc(x_235);
x_236 = lean_ctor_get(x_1, 0);
lean_inc(x_236);
x_237 = lean_ctor_get(x_1, 1);
lean_inc(x_237);
x_238 = lean_ctor_get(x_1, 2);
lean_inc(x_238);
x_239 = l_Lean_PersistentArray_push___redArg(x_235, x_228);
x_240 = lean_ctor_get(x_1, 4);
lean_inc(x_240);
x_241 = lean_ctor_get(x_1, 5);
lean_inc(x_241);
lean_dec(x_1);
x_242 = l_Lean_PersistentArray_push___redArg(x_239, x_234);
x_243 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_243, 0, x_236);
lean_ctor_set(x_243, 1, x_237);
lean_ctor_set(x_243, 2, x_238);
lean_ctor_set(x_243, 3, x_242);
lean_ctor_set(x_243, 4, x_240);
lean_ctor_set(x_243, 5, x_241);
lean_ctor_set(x_232, 0, x_243);
return x_232;
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; 
x_244 = lean_ctor_get(x_232, 0);
x_245 = lean_ctor_get(x_232, 1);
lean_inc(x_245);
lean_inc(x_244);
lean_dec(x_232);
x_246 = lean_ctor_get(x_1, 3);
lean_inc(x_246);
x_247 = lean_ctor_get(x_1, 0);
lean_inc(x_247);
x_248 = lean_ctor_get(x_1, 1);
lean_inc(x_248);
x_249 = lean_ctor_get(x_1, 2);
lean_inc(x_249);
x_250 = l_Lean_PersistentArray_push___redArg(x_246, x_228);
x_251 = lean_ctor_get(x_1, 4);
lean_inc(x_251);
x_252 = lean_ctor_get(x_1, 5);
lean_inc(x_252);
lean_dec(x_1);
x_253 = l_Lean_PersistentArray_push___redArg(x_250, x_244);
x_254 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_254, 0, x_247);
lean_ctor_set(x_254, 1, x_248);
lean_ctor_set(x_254, 2, x_249);
lean_ctor_set(x_254, 3, x_253);
lean_ctor_set(x_254, 4, x_251);
lean_ctor_set(x_254, 5, x_252);
x_255 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_255, 0, x_254);
lean_ctor_set(x_255, 1, x_245);
return x_255;
}
}
else
{
uint8_t x_256; 
lean_dec(x_228);
lean_dec(x_1);
x_256 = !lean_is_exclusive(x_232);
if (x_256 == 0)
{
return x_232;
}
else
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; 
x_257 = lean_ctor_get(x_232, 0);
x_258 = lean_ctor_get(x_232, 1);
lean_inc(x_258);
lean_inc(x_257);
lean_dec(x_232);
x_259 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_259, 0, x_257);
lean_ctor_set(x_259, 1, x_258);
return x_259;
}
}
}
else
{
uint8_t x_260; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_260 = !lean_is_exclusive(x_227);
if (x_260 == 0)
{
return x_227;
}
else
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; 
x_261 = lean_ctor_get(x_227, 0);
x_262 = lean_ctor_get(x_227, 1);
lean_inc(x_262);
lean_inc(x_261);
lean_dec(x_227);
x_263 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_263, 0, x_261);
lean_ctor_set(x_263, 1, x_262);
return x_263;
}
}
}
}
case 6:
{
lean_object* x_264; lean_object* x_265; uint8_t x_266; uint8_t x_267; 
lean_dec(x_55);
x_264 = lean_ctor_get(x_54, 1);
lean_inc(x_264);
lean_dec(x_54);
x_265 = lean_box(2);
x_266 = lean_unbox(x_265);
x_267 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_beqEMatchTheoremKind____x40_Lean_Meta_Tactic_Grind_EMatchTheorem___hyg_1361_(x_3, x_266);
if (x_267 == 0)
{
lean_object* x_268; 
x_268 = l_Lean_Meta_Grind_mkEMatchTheoremForDecl(x_2, x_3, x_4, x_5, x_6, x_7, x_264);
if (lean_obj_tag(x_268) == 0)
{
uint8_t x_269; 
x_269 = !lean_is_exclusive(x_268);
if (x_269 == 0)
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_270 = lean_ctor_get(x_268, 0);
x_271 = lean_ctor_get(x_1, 0);
lean_inc(x_271);
x_272 = lean_ctor_get(x_1, 1);
lean_inc(x_272);
x_273 = lean_ctor_get(x_1, 2);
lean_inc(x_273);
x_274 = lean_ctor_get(x_1, 3);
lean_inc(x_274);
x_275 = l_Lean_PersistentArray_push___redArg(x_274, x_270);
x_276 = lean_ctor_get(x_1, 4);
lean_inc(x_276);
x_277 = lean_ctor_get(x_1, 5);
lean_inc(x_277);
lean_dec(x_1);
x_278 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_278, 0, x_271);
lean_ctor_set(x_278, 1, x_272);
lean_ctor_set(x_278, 2, x_273);
lean_ctor_set(x_278, 3, x_275);
lean_ctor_set(x_278, 4, x_276);
lean_ctor_set(x_278, 5, x_277);
lean_ctor_set(x_268, 0, x_278);
return x_268;
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; 
x_279 = lean_ctor_get(x_268, 0);
x_280 = lean_ctor_get(x_268, 1);
lean_inc(x_280);
lean_inc(x_279);
lean_dec(x_268);
x_281 = lean_ctor_get(x_1, 0);
lean_inc(x_281);
x_282 = lean_ctor_get(x_1, 1);
lean_inc(x_282);
x_283 = lean_ctor_get(x_1, 2);
lean_inc(x_283);
x_284 = lean_ctor_get(x_1, 3);
lean_inc(x_284);
x_285 = l_Lean_PersistentArray_push___redArg(x_284, x_279);
x_286 = lean_ctor_get(x_1, 4);
lean_inc(x_286);
x_287 = lean_ctor_get(x_1, 5);
lean_inc(x_287);
lean_dec(x_1);
x_288 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_288, 0, x_281);
lean_ctor_set(x_288, 1, x_282);
lean_ctor_set(x_288, 2, x_283);
lean_ctor_set(x_288, 3, x_285);
lean_ctor_set(x_288, 4, x_286);
lean_ctor_set(x_288, 5, x_287);
x_289 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_289, 0, x_288);
lean_ctor_set(x_289, 1, x_280);
return x_289;
}
}
else
{
uint8_t x_290; 
lean_dec(x_1);
x_290 = !lean_is_exclusive(x_268);
if (x_290 == 0)
{
return x_268;
}
else
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; 
x_291 = lean_ctor_get(x_268, 0);
x_292 = lean_ctor_get(x_268, 1);
lean_inc(x_292);
lean_inc(x_291);
lean_dec(x_268);
x_293 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_293, 0, x_291);
lean_ctor_set(x_293, 1, x_292);
return x_293;
}
}
}
else
{
lean_object* x_294; uint8_t x_295; lean_object* x_296; 
x_294 = lean_box(0);
x_295 = lean_unbox(x_294);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_296 = l_Lean_Meta_Grind_mkEMatchTheoremForDecl(x_2, x_295, x_4, x_5, x_6, x_7, x_264);
if (lean_obj_tag(x_296) == 0)
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; uint8_t x_300; lean_object* x_301; 
x_297 = lean_ctor_get(x_296, 0);
lean_inc(x_297);
x_298 = lean_ctor_get(x_296, 1);
lean_inc(x_298);
lean_dec(x_296);
x_299 = lean_box(1);
x_300 = lean_unbox(x_299);
x_301 = l_Lean_Meta_Grind_mkEMatchTheoremForDecl(x_2, x_300, x_4, x_5, x_6, x_7, x_298);
if (lean_obj_tag(x_301) == 0)
{
uint8_t x_302; 
x_302 = !lean_is_exclusive(x_301);
if (x_302 == 0)
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; 
x_303 = lean_ctor_get(x_301, 0);
x_304 = lean_ctor_get(x_1, 3);
lean_inc(x_304);
x_305 = lean_ctor_get(x_1, 0);
lean_inc(x_305);
x_306 = lean_ctor_get(x_1, 1);
lean_inc(x_306);
x_307 = lean_ctor_get(x_1, 2);
lean_inc(x_307);
x_308 = l_Lean_PersistentArray_push___redArg(x_304, x_297);
x_309 = lean_ctor_get(x_1, 4);
lean_inc(x_309);
x_310 = lean_ctor_get(x_1, 5);
lean_inc(x_310);
lean_dec(x_1);
x_311 = l_Lean_PersistentArray_push___redArg(x_308, x_303);
x_312 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_312, 0, x_305);
lean_ctor_set(x_312, 1, x_306);
lean_ctor_set(x_312, 2, x_307);
lean_ctor_set(x_312, 3, x_311);
lean_ctor_set(x_312, 4, x_309);
lean_ctor_set(x_312, 5, x_310);
lean_ctor_set(x_301, 0, x_312);
return x_301;
}
else
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; 
x_313 = lean_ctor_get(x_301, 0);
x_314 = lean_ctor_get(x_301, 1);
lean_inc(x_314);
lean_inc(x_313);
lean_dec(x_301);
x_315 = lean_ctor_get(x_1, 3);
lean_inc(x_315);
x_316 = lean_ctor_get(x_1, 0);
lean_inc(x_316);
x_317 = lean_ctor_get(x_1, 1);
lean_inc(x_317);
x_318 = lean_ctor_get(x_1, 2);
lean_inc(x_318);
x_319 = l_Lean_PersistentArray_push___redArg(x_315, x_297);
x_320 = lean_ctor_get(x_1, 4);
lean_inc(x_320);
x_321 = lean_ctor_get(x_1, 5);
lean_inc(x_321);
lean_dec(x_1);
x_322 = l_Lean_PersistentArray_push___redArg(x_319, x_313);
x_323 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_323, 0, x_316);
lean_ctor_set(x_323, 1, x_317);
lean_ctor_set(x_323, 2, x_318);
lean_ctor_set(x_323, 3, x_322);
lean_ctor_set(x_323, 4, x_320);
lean_ctor_set(x_323, 5, x_321);
x_324 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_324, 0, x_323);
lean_ctor_set(x_324, 1, x_314);
return x_324;
}
}
else
{
uint8_t x_325; 
lean_dec(x_297);
lean_dec(x_1);
x_325 = !lean_is_exclusive(x_301);
if (x_325 == 0)
{
return x_301;
}
else
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; 
x_326 = lean_ctor_get(x_301, 0);
x_327 = lean_ctor_get(x_301, 1);
lean_inc(x_327);
lean_inc(x_326);
lean_dec(x_301);
x_328 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_328, 0, x_326);
lean_ctor_set(x_328, 1, x_327);
return x_328;
}
}
}
else
{
uint8_t x_329; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_329 = !lean_is_exclusive(x_296);
if (x_329 == 0)
{
return x_296;
}
else
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; 
x_330 = lean_ctor_get(x_296, 0);
x_331 = lean_ctor_get(x_296, 1);
lean_inc(x_331);
lean_inc(x_330);
lean_dec(x_296);
x_332 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_332, 0, x_330);
lean_ctor_set(x_332, 1, x_331);
return x_332;
}
}
}
}
default: 
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; 
lean_dec(x_55);
lean_dec(x_1);
x_333 = lean_ctor_get(x_54, 1);
lean_inc(x_333);
lean_dec(x_54);
x_334 = lean_mk_string_unchecked("invalid `grind` parameter, `", 28, 28);
x_335 = l_Lean_stringToMessageData(x_334);
lean_dec(x_334);
x_336 = l_Lean_MessageData_ofName(x_2);
x_337 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_337, 0, x_335);
lean_ctor_set(x_337, 1, x_336);
x_338 = lean_mk_string_unchecked("` is not a theorem, definition, or inductive type", 49, 49);
x_339 = l_Lean_stringToMessageData(x_338);
lean_dec(x_338);
x_340 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_340, 0, x_337);
lean_ctor_set(x_340, 1, x_339);
x_341 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_340, x_4, x_5, x_6, x_7, x_333);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_341;
}
}
}
else
{
uint8_t x_342; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_342 = !lean_is_exclusive(x_54);
if (x_342 == 0)
{
return x_54;
}
else
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; 
x_343 = lean_ctor_get(x_54, 0);
x_344 = lean_ctor_get(x_54, 1);
lean_inc(x_344);
lean_inc(x_343);
lean_dec(x_54);
x_345 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_345, 0, x_343);
lean_ctor_set(x_345, 1, x_344);
return x_345;
}
}
block_53:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_2);
x_14 = l_Lean_Meta_Grind_mkEMatchEqTheoremsForDef_x3f(x_2, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_1);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_mk_string_unchecked("failed to generate equation theorems for `", 42, 42);
x_18 = l_Lean_stringToMessageData(x_17);
lean_dec(x_17);
x_19 = l_Lean_MessageData_ofName(x_2);
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_mk_string_unchecked("`", 1, 1);
x_22 = l_Lean_stringToMessageData(x_21);
lean_dec(x_21);
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_23, x_9, x_10, x_11, x_12, x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_2);
x_25 = !lean_is_exclusive(x_14);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_26 = lean_ctor_get(x_14, 0);
lean_dec(x_26);
x_27 = lean_ctor_get(x_15, 0);
lean_inc(x_27);
lean_dec(x_15);
x_28 = lean_ctor_get(x_1, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_1, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_1, 2);
lean_inc(x_30);
x_31 = lean_ctor_get(x_1, 3);
lean_inc(x_31);
x_32 = l_Array_toPArray_x27___redArg(x_27);
lean_dec(x_27);
x_33 = l_Lean_PersistentArray_append___redArg(x_31, x_32);
lean_dec(x_32);
x_34 = lean_ctor_get(x_1, 4);
lean_inc(x_34);
x_35 = lean_ctor_get(x_1, 5);
lean_inc(x_35);
lean_dec(x_1);
x_36 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_36, 0, x_28);
lean_ctor_set(x_36, 1, x_29);
lean_ctor_set(x_36, 2, x_30);
lean_ctor_set(x_36, 3, x_33);
lean_ctor_set(x_36, 4, x_34);
lean_ctor_set(x_36, 5, x_35);
lean_ctor_set(x_14, 0, x_36);
return x_14;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_37 = lean_ctor_get(x_14, 1);
lean_inc(x_37);
lean_dec(x_14);
x_38 = lean_ctor_get(x_15, 0);
lean_inc(x_38);
lean_dec(x_15);
x_39 = lean_ctor_get(x_1, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_1, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_1, 2);
lean_inc(x_41);
x_42 = lean_ctor_get(x_1, 3);
lean_inc(x_42);
x_43 = l_Array_toPArray_x27___redArg(x_38);
lean_dec(x_38);
x_44 = l_Lean_PersistentArray_append___redArg(x_42, x_43);
lean_dec(x_43);
x_45 = lean_ctor_get(x_1, 4);
lean_inc(x_45);
x_46 = lean_ctor_get(x_1, 5);
lean_inc(x_46);
lean_dec(x_1);
x_47 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_47, 0, x_39);
lean_ctor_set(x_47, 1, x_40);
lean_ctor_set(x_47, 2, x_41);
lean_ctor_set(x_47, 3, x_44);
lean_ctor_set(x_47, 4, x_45);
lean_ctor_set(x_47, 5, x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_37);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_14);
if (x_49 == 0)
{
return x_14;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_14, 0);
x_51 = lean_ctor_get(x_14, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_14);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Elab_Tactic_elabGrindParams_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_9; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_box(8);
x_13 = lean_ctor_get(x_6, 5);
x_14 = l_Lean_replaceRef(x_1, x_13);
x_15 = lean_ctor_get(x_6, 0);
x_16 = lean_ctor_get(x_6, 1);
x_17 = lean_ctor_get(x_6, 2);
x_18 = lean_ctor_get(x_6, 3);
x_19 = lean_ctor_get(x_6, 4);
x_20 = lean_ctor_get(x_6, 6);
x_21 = lean_ctor_get(x_6, 7);
x_22 = lean_ctor_get(x_6, 8);
x_23 = lean_ctor_get(x_6, 9);
x_24 = lean_ctor_get(x_6, 10);
x_25 = lean_ctor_get_uint8(x_6, sizeof(void*)*13);
x_26 = lean_ctor_get(x_6, 11);
x_27 = lean_ctor_get_uint8(x_6, sizeof(void*)*13 + 1);
x_28 = lean_ctor_get(x_6, 12);
lean_inc(x_28);
lean_inc(x_26);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_29 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_29, 0, x_15);
lean_ctor_set(x_29, 1, x_16);
lean_ctor_set(x_29, 2, x_17);
lean_ctor_set(x_29, 3, x_18);
lean_ctor_set(x_29, 4, x_19);
lean_ctor_set(x_29, 5, x_14);
lean_ctor_set(x_29, 6, x_20);
lean_ctor_set(x_29, 7, x_21);
lean_ctor_set(x_29, 8, x_22);
lean_ctor_set(x_29, 9, x_23);
lean_ctor_set(x_29, 10, x_24);
lean_ctor_set(x_29, 11, x_26);
lean_ctor_set(x_29, 12, x_28);
lean_ctor_set_uint8(x_29, sizeof(void*)*13, x_25);
lean_ctor_set_uint8(x_29, sizeof(void*)*13 + 1, x_27);
x_30 = lean_unbox(x_12);
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_4);
x_31 = l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem(x_3, x_10, x_30, x_4, x_5, x_29, x_7, x_8);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_2 = x_11;
x_3 = x_32;
x_8 = x_33;
goto _start;
}
else
{
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Elab_Tactic_elabGrindParams_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_List_forIn_x27_loop___at___Lean_Elab_Tactic_elabGrindParams_spec__0___redArg(x_1, x_3, x_4, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___Lean_Elab_Tactic_elabGrindParams_spec__1(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
x_4 = l_List_reverse___redArg(x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get_uint8(x_6, sizeof(void*)*6);
x_9 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_beqEMatchTheoremKind____x40_Lean_Meta_Tactic_Grind_EMatchTheorem___hyg_1361_(x_8, x_1);
if (x_9 == 0)
{
lean_free_object(x_2);
lean_dec(x_6);
x_2 = x_7;
goto _start;
}
else
{
lean_ctor_set(x_2, 1, x_3);
{
lean_object* _tmp_1 = x_7;
lean_object* _tmp_2 = x_2;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_2);
x_14 = lean_ctor_get_uint8(x_12, sizeof(void*)*6);
x_15 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_beqEMatchTheoremKind____x40_Lean_Meta_Tactic_Grind_EMatchTheorem___hyg_1361_(x_14, x_1);
if (x_15 == 0)
{
lean_dec(x_12);
x_2 = x_13;
goto _start;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_3);
x_2 = x_13;
x_3 = x_17;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Elab_Tactic_elabGrindParams_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 3);
lean_inc(x_10);
x_11 = l_Lean_PersistentArray_push___redArg(x_10, x_5);
x_12 = lean_ctor_get(x_2, 4);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 5);
lean_inc(x_13);
lean_dec(x_2);
x_14 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_8);
lean_ctor_set(x_14, 2, x_9);
lean_ctor_set(x_14, 3, x_11);
lean_ctor_set(x_14, 4, x_12);
lean_ctor_set(x_14, 5, x_13);
x_1 = x_6;
x_2 = x_14;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Elab_Tactic_elabGrindParams_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_List_forIn_x27_loop___at___Lean_Elab_Tactic_elabGrindParams_spec__2___redArg(x_2, x_3, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_elabGrindParams_spec__3_spec__3(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_29; 
x_29 = lean_usize_dec_lt(x_4, x_3);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_5);
lean_ctor_set(x_30, 1, x_10);
return x_30;
}
else
{
lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_31 = lean_array_uget(x_2, x_4);
x_80 = lean_mk_string_unchecked("Lean", 4, 4);
x_81 = lean_mk_string_unchecked("Parser", 6, 6);
x_82 = lean_mk_string_unchecked("Tactic", 6, 6);
x_83 = lean_mk_string_unchecked("grindParam", 10, 10);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
x_84 = l_Lean_Name_mkStr4(x_80, x_81, x_82, x_83);
lean_inc(x_31);
x_85 = l_Lean_Syntax_isOfKind(x_31, x_84);
lean_dec(x_84);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; 
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_5);
x_86 = lean_mk_string_unchecked("unexpected `grind` parameter", 28, 28);
x_87 = l_Lean_stringToMessageData(x_86);
lean_dec(x_86);
x_88 = l_Lean_MessageData_ofSyntax(x_31);
x_89 = l_Lean_indentD(x_88);
x_90 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_90, 0, x_87);
lean_ctor_set(x_90, 1, x_89);
x_91 = lean_mk_string_unchecked("", 0, 0);
x_92 = l_Lean_stringToMessageData(x_91);
lean_dec(x_91);
x_93 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_93, 0, x_90);
lean_ctor_set(x_93, 1, x_92);
x_94 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_93, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
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
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_99 = lean_unsigned_to_nat(0u);
x_100 = l_Lean_Syntax_getArg(x_31, x_99);
x_101 = lean_mk_string_unchecked("grindErase", 10, 10);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
x_102 = l_Lean_Name_mkStr4(x_80, x_81, x_82, x_101);
lean_inc(x_100);
x_103 = l_Lean_Syntax_isOfKind(x_100, x_102);
lean_dec(x_102);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; uint8_t x_106; 
x_104 = lean_mk_string_unchecked("grindLemma", 10, 10);
lean_inc(x_81);
lean_inc(x_80);
x_105 = l_Lean_Name_mkStr4(x_80, x_81, x_82, x_104);
lean_inc(x_100);
x_106 = l_Lean_Syntax_isOfKind(x_100, x_105);
lean_dec(x_105);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; 
lean_dec(x_100);
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_5);
x_107 = lean_mk_string_unchecked("unexpected `grind` parameter", 28, 28);
x_108 = l_Lean_stringToMessageData(x_107);
lean_dec(x_107);
x_109 = l_Lean_MessageData_ofSyntax(x_31);
x_110 = l_Lean_indentD(x_109);
x_111 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_111, 0, x_108);
lean_ctor_set(x_111, 1, x_110);
x_112 = lean_mk_string_unchecked("", 0, 0);
x_113 = l_Lean_stringToMessageData(x_112);
lean_dec(x_112);
x_114 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_114, 0, x_111);
lean_ctor_set(x_114, 1, x_113);
x_115 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_114, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_116 = !lean_is_exclusive(x_115);
if (x_116 == 0)
{
return x_115;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_115, 0);
x_118 = lean_ctor_get(x_115, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_115);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
return x_119;
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_337; uint8_t x_338; 
x_337 = l_Lean_Syntax_getArg(x_100, x_99);
x_338 = l_Lean_Syntax_isNone(x_337);
if (x_338 == 0)
{
lean_object* x_339; uint8_t x_340; 
x_339 = lean_unsigned_to_nat(1u);
lean_inc(x_337);
x_340 = l_Lean_Syntax_matchesNull(x_337, x_339);
if (x_340 == 0)
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; uint8_t x_350; 
lean_dec(x_337);
lean_dec(x_100);
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_5);
x_341 = lean_mk_string_unchecked("unexpected `grind` parameter", 28, 28);
x_342 = l_Lean_stringToMessageData(x_341);
lean_dec(x_341);
x_343 = l_Lean_MessageData_ofSyntax(x_31);
x_344 = l_Lean_indentD(x_343);
x_345 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_345, 0, x_342);
lean_ctor_set(x_345, 1, x_344);
x_346 = lean_mk_string_unchecked("", 0, 0);
x_347 = l_Lean_stringToMessageData(x_346);
lean_dec(x_346);
x_348 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_348, 0, x_345);
lean_ctor_set(x_348, 1, x_347);
x_349 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_348, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_350 = !lean_is_exclusive(x_349);
if (x_350 == 0)
{
return x_349;
}
else
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; 
x_351 = lean_ctor_get(x_349, 0);
x_352 = lean_ctor_get(x_349, 1);
lean_inc(x_352);
lean_inc(x_351);
lean_dec(x_349);
x_353 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_353, 0, x_351);
lean_ctor_set(x_353, 1, x_352);
return x_353;
}
}
else
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; uint8_t x_358; 
x_354 = l_Lean_Syntax_getArg(x_337, x_99);
lean_dec(x_337);
x_355 = lean_mk_string_unchecked("Attr", 4, 4);
x_356 = lean_mk_string_unchecked("grindMod", 8, 8);
x_357 = l_Lean_Name_mkStr4(x_80, x_81, x_355, x_356);
lean_inc(x_354);
x_358 = l_Lean_Syntax_isOfKind(x_354, x_357);
lean_dec(x_357);
if (x_358 == 0)
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; uint8_t x_368; 
lean_dec(x_354);
lean_dec(x_100);
lean_dec(x_5);
x_359 = lean_mk_string_unchecked("unexpected `grind` parameter", 28, 28);
x_360 = l_Lean_stringToMessageData(x_359);
lean_dec(x_359);
x_361 = l_Lean_MessageData_ofSyntax(x_31);
x_362 = l_Lean_indentD(x_361);
x_363 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_363, 0, x_360);
lean_ctor_set(x_363, 1, x_362);
x_364 = lean_mk_string_unchecked("", 0, 0);
x_365 = l_Lean_stringToMessageData(x_364);
lean_dec(x_364);
x_366 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_366, 0, x_363);
lean_ctor_set(x_366, 1, x_365);
x_367 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_366, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_368 = !lean_is_exclusive(x_367);
if (x_368 == 0)
{
return x_367;
}
else
{
lean_object* x_369; lean_object* x_370; lean_object* x_371; 
x_369 = lean_ctor_get(x_367, 0);
x_370 = lean_ctor_get(x_367, 1);
lean_inc(x_370);
lean_inc(x_369);
lean_dec(x_367);
x_371 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_371, 0, x_369);
lean_ctor_set(x_371, 1, x_370);
return x_371;
}
}
else
{
lean_object* x_372; 
x_372 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_372, 0, x_354);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_180 = x_372;
x_181 = x_6;
x_182 = x_7;
x_183 = x_8;
x_184 = x_9;
x_185 = x_10;
goto block_336;
}
}
}
else
{
lean_object* x_373; 
lean_dec(x_337);
lean_dec(x_81);
lean_dec(x_80);
x_373 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_180 = x_373;
x_181 = x_6;
x_182 = x_7;
x_183 = x_8;
x_184 = x_9;
x_185 = x_10;
goto block_336;
}
block_179:
{
lean_object* x_127; 
lean_inc(x_125);
lean_inc(x_124);
lean_inc(x_120);
x_127 = l_Lean_Meta_Grind_isCasesAttrCandidate_x3f(x_120, x_103, x_124, x_125, x_126);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; lean_object* x_144; uint8_t x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; lean_object* x_149; 
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec(x_127);
x_130 = lean_box(8);
x_131 = lean_ctor_get(x_124, 5);
lean_inc(x_131);
x_132 = l_Lean_replaceRef(x_31, x_131);
lean_dec(x_131);
lean_dec(x_31);
x_133 = lean_ctor_get(x_124, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_124, 1);
lean_inc(x_134);
x_135 = lean_ctor_get(x_124, 2);
lean_inc(x_135);
x_136 = lean_ctor_get(x_124, 3);
lean_inc(x_136);
x_137 = lean_ctor_get(x_124, 4);
lean_inc(x_137);
x_138 = lean_ctor_get(x_124, 6);
lean_inc(x_138);
x_139 = lean_ctor_get(x_124, 7);
lean_inc(x_139);
x_140 = lean_ctor_get(x_124, 8);
lean_inc(x_140);
x_141 = lean_ctor_get(x_124, 9);
lean_inc(x_141);
x_142 = lean_ctor_get(x_124, 10);
lean_inc(x_142);
x_143 = lean_ctor_get_uint8(x_124, sizeof(void*)*13);
x_144 = lean_ctor_get(x_124, 11);
lean_inc(x_144);
x_145 = lean_ctor_get_uint8(x_124, sizeof(void*)*13 + 1);
x_146 = lean_ctor_get(x_124, 12);
lean_inc(x_146);
lean_dec(x_124);
x_147 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_147, 0, x_133);
lean_ctor_set(x_147, 1, x_134);
lean_ctor_set(x_147, 2, x_135);
lean_ctor_set(x_147, 3, x_136);
lean_ctor_set(x_147, 4, x_137);
lean_ctor_set(x_147, 5, x_132);
lean_ctor_set(x_147, 6, x_138);
lean_ctor_set(x_147, 7, x_139);
lean_ctor_set(x_147, 8, x_140);
lean_ctor_set(x_147, 9, x_141);
lean_ctor_set(x_147, 10, x_142);
lean_ctor_set(x_147, 11, x_144);
lean_ctor_set(x_147, 12, x_146);
lean_ctor_set_uint8(x_147, sizeof(void*)*13, x_143);
lean_ctor_set_uint8(x_147, sizeof(void*)*13 + 1, x_145);
x_148 = lean_unbox(x_130);
x_149 = l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem(x_121, x_120, x_148, x_122, x_123, x_147, x_125, x_129);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; 
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_149, 1);
lean_inc(x_151);
lean_dec(x_149);
x_11 = x_150;
x_12 = x_151;
goto block_17;
}
else
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_149;
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
lean_dec(x_120);
x_152 = lean_ctor_get(x_127, 1);
lean_inc(x_152);
lean_dec(x_127);
x_153 = lean_ctor_get(x_128, 0);
lean_inc(x_153);
lean_dec(x_128);
lean_inc(x_125);
lean_inc(x_124);
lean_inc(x_123);
lean_inc(x_122);
lean_inc(x_153);
x_154 = l_Lean_Meta_isInductivePredicate_x3f(x_153, x_122, x_123, x_124, x_125, x_152);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_154, 1);
lean_inc(x_156);
lean_dec(x_154);
x_157 = lean_ctor_get(x_121, 2);
lean_inc(x_157);
x_158 = lean_ctor_get(x_121, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_121, 1);
lean_inc(x_159);
x_160 = lean_box(x_103);
x_161 = l_Lean_PersistentHashMap_insert___at___Lean_MetavarContext_addExprMVarDecl_spec__0(lean_box(0), x_157, x_153, x_160);
x_162 = lean_ctor_get(x_121, 3);
lean_inc(x_162);
x_163 = lean_ctor_get(x_121, 4);
lean_inc(x_163);
x_164 = lean_ctor_get(x_121, 5);
lean_inc(x_164);
lean_dec(x_121);
x_165 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_165, 0, x_158);
lean_ctor_set(x_165, 1, x_159);
lean_ctor_set(x_165, 2, x_161);
lean_ctor_set(x_165, 3, x_162);
lean_ctor_set(x_165, 4, x_163);
lean_ctor_set(x_165, 5, x_164);
if (lean_obj_tag(x_155) == 0)
{
lean_dec(x_125);
lean_dec(x_124);
lean_dec(x_123);
lean_dec(x_122);
lean_dec(x_31);
x_11 = x_165;
x_12 = x_156;
goto block_17;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_155, 0);
lean_inc(x_166);
lean_dec(x_155);
x_167 = lean_ctor_get(x_166, 4);
lean_inc(x_167);
lean_dec(x_166);
x_168 = l_List_forIn_x27_loop___at___Lean_Elab_Tactic_elabGrindParams_spec__0___redArg(x_31, x_167, x_165, x_122, x_123, x_124, x_125, x_156);
lean_dec(x_124);
lean_dec(x_31);
if (lean_obj_tag(x_168) == 0)
{
lean_object* x_169; lean_object* x_170; 
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_168, 1);
lean_inc(x_170);
lean_dec(x_168);
x_11 = x_169;
x_12 = x_170;
goto block_17;
}
else
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_168;
}
}
}
else
{
uint8_t x_171; 
lean_dec(x_153);
lean_dec(x_125);
lean_dec(x_124);
lean_dec(x_123);
lean_dec(x_122);
lean_dec(x_121);
lean_dec(x_31);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_171 = !lean_is_exclusive(x_154);
if (x_171 == 0)
{
return x_154;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_172 = lean_ctor_get(x_154, 0);
x_173 = lean_ctor_get(x_154, 1);
lean_inc(x_173);
lean_inc(x_172);
lean_dec(x_154);
x_174 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_174, 0, x_172);
lean_ctor_set(x_174, 1, x_173);
return x_174;
}
}
}
}
else
{
uint8_t x_175; 
lean_dec(x_125);
lean_dec(x_124);
lean_dec(x_123);
lean_dec(x_122);
lean_dec(x_121);
lean_dec(x_120);
lean_dec(x_31);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_175 = !lean_is_exclusive(x_127);
if (x_175 == 0)
{
return x_127;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_176 = lean_ctor_get(x_127, 0);
x_177 = lean_ctor_get(x_127, 1);
lean_inc(x_177);
lean_inc(x_176);
lean_dec(x_127);
x_178 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_178, 0, x_176);
lean_ctor_set(x_178, 1, x_177);
return x_178;
}
}
}
block_336:
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; uint8_t x_190; 
x_186 = lean_unsigned_to_nat(1u);
x_187 = l_Lean_Syntax_getArg(x_100, x_186);
lean_dec(x_100);
x_188 = lean_mk_string_unchecked("ident", 5, 5);
x_189 = l_Lean_Name_mkStr1(x_188);
lean_inc(x_187);
x_190 = l_Lean_Syntax_isOfKind(x_187, x_189);
lean_dec(x_189);
if (x_190 == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; uint8_t x_200; 
lean_dec(x_187);
lean_dec(x_180);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_191 = lean_mk_string_unchecked("unexpected `grind` parameter", 28, 28);
x_192 = l_Lean_stringToMessageData(x_191);
lean_dec(x_191);
x_193 = l_Lean_MessageData_ofSyntax(x_31);
x_194 = l_Lean_indentD(x_193);
x_195 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_195, 0, x_192);
lean_ctor_set(x_195, 1, x_194);
x_196 = lean_mk_string_unchecked("", 0, 0);
x_197 = l_Lean_stringToMessageData(x_196);
lean_dec(x_196);
x_198 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_198, 0, x_195);
lean_ctor_set(x_198, 1, x_197);
x_199 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_198, x_181, x_182, x_183, x_184, x_185);
lean_dec(x_184);
lean_dec(x_183);
lean_dec(x_182);
lean_dec(x_181);
x_200 = !lean_is_exclusive(x_199);
if (x_200 == 0)
{
return x_199;
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_201 = lean_ctor_get(x_199, 0);
x_202 = lean_ctor_get(x_199, 1);
lean_inc(x_202);
lean_inc(x_201);
lean_dec(x_199);
x_203 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_203, 0, x_201);
lean_ctor_set(x_203, 1, x_202);
return x_203;
}
}
else
{
lean_object* x_204; lean_object* x_205; 
x_204 = lean_box(0);
lean_inc(x_184);
lean_inc(x_183);
x_205 = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(x_187, x_204, x_183, x_184, x_185);
if (lean_obj_tag(x_205) == 0)
{
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_206; lean_object* x_207; 
x_206 = lean_ctor_get(x_205, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_205, 1);
lean_inc(x_207);
lean_dec(x_205);
x_120 = x_206;
x_121 = x_5;
x_122 = x_181;
x_123 = x_182;
x_124 = x_183;
x_125 = x_184;
x_126 = x_207;
goto block_179;
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_208 = lean_ctor_get(x_205, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_205, 1);
lean_inc(x_209);
lean_dec(x_205);
x_210 = lean_ctor_get(x_180, 0);
lean_inc(x_210);
lean_dec(x_180);
x_211 = l_Lean_Meta_Grind_getAttrKindCore(x_210, x_183, x_184, x_209);
if (lean_obj_tag(x_211) == 0)
{
lean_object* x_212; 
x_212 = lean_ctor_get(x_211, 0);
lean_inc(x_212);
switch (lean_obj_tag(x_212)) {
case 0:
{
uint8_t x_213; lean_object* x_214; 
x_213 = lean_ctor_get_uint8(x_212, 0);
lean_dec(x_212);
x_214 = lean_box(x_213);
if (lean_obj_tag(x_214) == 9)
{
if (x_1 == 0)
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; uint8_t x_228; lean_object* x_229; uint8_t x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; uint8_t x_234; 
lean_dec(x_208);
lean_dec(x_182);
lean_dec(x_181);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_215 = lean_ctor_get(x_211, 1);
lean_inc(x_215);
lean_dec(x_211);
x_216 = lean_ctor_get(x_183, 5);
lean_inc(x_216);
x_217 = l_Lean_replaceRef(x_31, x_216);
lean_dec(x_216);
lean_dec(x_31);
x_218 = lean_ctor_get(x_183, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_183, 1);
lean_inc(x_219);
x_220 = lean_ctor_get(x_183, 2);
lean_inc(x_220);
x_221 = lean_ctor_get(x_183, 3);
lean_inc(x_221);
x_222 = lean_ctor_get(x_183, 4);
lean_inc(x_222);
x_223 = lean_ctor_get(x_183, 6);
lean_inc(x_223);
x_224 = lean_ctor_get(x_183, 7);
lean_inc(x_224);
x_225 = lean_ctor_get(x_183, 8);
lean_inc(x_225);
x_226 = lean_ctor_get(x_183, 9);
lean_inc(x_226);
x_227 = lean_ctor_get(x_183, 10);
lean_inc(x_227);
x_228 = lean_ctor_get_uint8(x_183, sizeof(void*)*13);
x_229 = lean_ctor_get(x_183, 11);
lean_inc(x_229);
x_230 = lean_ctor_get_uint8(x_183, sizeof(void*)*13 + 1);
x_231 = lean_ctor_get(x_183, 12);
lean_inc(x_231);
lean_dec(x_183);
x_232 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_232, 0, x_218);
lean_ctor_set(x_232, 1, x_219);
lean_ctor_set(x_232, 2, x_220);
lean_ctor_set(x_232, 3, x_221);
lean_ctor_set(x_232, 4, x_222);
lean_ctor_set(x_232, 5, x_217);
lean_ctor_set(x_232, 6, x_223);
lean_ctor_set(x_232, 7, x_224);
lean_ctor_set(x_232, 8, x_225);
lean_ctor_set(x_232, 9, x_226);
lean_ctor_set(x_232, 10, x_227);
lean_ctor_set(x_232, 11, x_229);
lean_ctor_set(x_232, 12, x_231);
lean_ctor_set_uint8(x_232, sizeof(void*)*13, x_228);
lean_ctor_set_uint8(x_232, sizeof(void*)*13 + 1, x_230);
x_233 = l_Lean_Meta_Grind_throwInvalidUsrModifier(lean_box(0), x_232, x_184, x_215);
lean_dec(x_184);
lean_dec(x_232);
x_234 = !lean_is_exclusive(x_233);
if (x_234 == 0)
{
return x_233;
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_235 = lean_ctor_get(x_233, 0);
x_236 = lean_ctor_get(x_233, 1);
lean_inc(x_236);
lean_inc(x_235);
lean_dec(x_233);
x_237 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_237, 0, x_235);
lean_ctor_set(x_237, 1, x_236);
return x_237;
}
}
else
{
lean_object* x_238; 
x_238 = lean_ctor_get(x_211, 1);
lean_inc(x_238);
lean_dec(x_211);
x_32 = x_213;
x_33 = x_208;
x_34 = x_5;
x_35 = x_181;
x_36 = x_182;
x_37 = x_183;
x_38 = x_184;
x_39 = x_238;
goto block_79;
}
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; uint8_t x_252; lean_object* x_253; uint8_t x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
lean_dec(x_214);
x_239 = lean_ctor_get(x_211, 1);
lean_inc(x_239);
lean_dec(x_211);
x_240 = lean_ctor_get(x_183, 5);
lean_inc(x_240);
x_241 = l_Lean_replaceRef(x_31, x_240);
lean_dec(x_240);
lean_dec(x_31);
x_242 = lean_ctor_get(x_183, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_183, 1);
lean_inc(x_243);
x_244 = lean_ctor_get(x_183, 2);
lean_inc(x_244);
x_245 = lean_ctor_get(x_183, 3);
lean_inc(x_245);
x_246 = lean_ctor_get(x_183, 4);
lean_inc(x_246);
x_247 = lean_ctor_get(x_183, 6);
lean_inc(x_247);
x_248 = lean_ctor_get(x_183, 7);
lean_inc(x_248);
x_249 = lean_ctor_get(x_183, 8);
lean_inc(x_249);
x_250 = lean_ctor_get(x_183, 9);
lean_inc(x_250);
x_251 = lean_ctor_get(x_183, 10);
lean_inc(x_251);
x_252 = lean_ctor_get_uint8(x_183, sizeof(void*)*13);
x_253 = lean_ctor_get(x_183, 11);
lean_inc(x_253);
x_254 = lean_ctor_get_uint8(x_183, sizeof(void*)*13 + 1);
x_255 = lean_ctor_get(x_183, 12);
lean_inc(x_255);
lean_dec(x_183);
x_256 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_256, 0, x_242);
lean_ctor_set(x_256, 1, x_243);
lean_ctor_set(x_256, 2, x_244);
lean_ctor_set(x_256, 3, x_245);
lean_ctor_set(x_256, 4, x_246);
lean_ctor_set(x_256, 5, x_241);
lean_ctor_set(x_256, 6, x_247);
lean_ctor_set(x_256, 7, x_248);
lean_ctor_set(x_256, 8, x_249);
lean_ctor_set(x_256, 9, x_250);
lean_ctor_set(x_256, 10, x_251);
lean_ctor_set(x_256, 11, x_253);
lean_ctor_set(x_256, 12, x_255);
lean_ctor_set_uint8(x_256, sizeof(void*)*13, x_252);
lean_ctor_set_uint8(x_256, sizeof(void*)*13 + 1, x_254);
x_257 = l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem(x_5, x_208, x_213, x_181, x_182, x_256, x_184, x_239);
if (lean_obj_tag(x_257) == 0)
{
lean_object* x_258; lean_object* x_259; 
x_258 = lean_ctor_get(x_257, 0);
lean_inc(x_258);
x_259 = lean_ctor_get(x_257, 1);
lean_inc(x_259);
lean_dec(x_257);
x_11 = x_258;
x_12 = x_259;
goto block_17;
}
else
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_257;
}
}
}
case 1:
{
lean_object* x_260; uint8_t x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; uint8_t x_274; lean_object* x_275; uint8_t x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; 
lean_dec(x_182);
lean_dec(x_181);
x_260 = lean_ctor_get(x_211, 1);
lean_inc(x_260);
lean_dec(x_211);
x_261 = lean_ctor_get_uint8(x_212, 0);
lean_dec(x_212);
x_262 = lean_ctor_get(x_183, 5);
lean_inc(x_262);
x_263 = l_Lean_replaceRef(x_31, x_262);
lean_dec(x_262);
lean_dec(x_31);
x_264 = lean_ctor_get(x_183, 0);
lean_inc(x_264);
x_265 = lean_ctor_get(x_183, 1);
lean_inc(x_265);
x_266 = lean_ctor_get(x_183, 2);
lean_inc(x_266);
x_267 = lean_ctor_get(x_183, 3);
lean_inc(x_267);
x_268 = lean_ctor_get(x_183, 4);
lean_inc(x_268);
x_269 = lean_ctor_get(x_183, 6);
lean_inc(x_269);
x_270 = lean_ctor_get(x_183, 7);
lean_inc(x_270);
x_271 = lean_ctor_get(x_183, 8);
lean_inc(x_271);
x_272 = lean_ctor_get(x_183, 9);
lean_inc(x_272);
x_273 = lean_ctor_get(x_183, 10);
lean_inc(x_273);
x_274 = lean_ctor_get_uint8(x_183, sizeof(void*)*13);
x_275 = lean_ctor_get(x_183, 11);
lean_inc(x_275);
x_276 = lean_ctor_get_uint8(x_183, sizeof(void*)*13 + 1);
x_277 = lean_ctor_get(x_183, 12);
lean_inc(x_277);
lean_dec(x_183);
x_278 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_278, 0, x_264);
lean_ctor_set(x_278, 1, x_265);
lean_ctor_set(x_278, 2, x_266);
lean_ctor_set(x_278, 3, x_267);
lean_ctor_set(x_278, 4, x_268);
lean_ctor_set(x_278, 5, x_263);
lean_ctor_set(x_278, 6, x_269);
lean_ctor_set(x_278, 7, x_270);
lean_ctor_set(x_278, 8, x_271);
lean_ctor_set(x_278, 9, x_272);
lean_ctor_set(x_278, 10, x_273);
lean_ctor_set(x_278, 11, x_275);
lean_ctor_set(x_278, 12, x_277);
lean_ctor_set_uint8(x_278, sizeof(void*)*13, x_274);
lean_ctor_set_uint8(x_278, sizeof(void*)*13 + 1, x_276);
lean_inc(x_208);
x_279 = l_Lean_Meta_Grind_validateCasesAttr(x_208, x_261, x_278, x_184, x_260);
if (lean_obj_tag(x_279) == 0)
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; 
x_280 = lean_ctor_get(x_279, 1);
lean_inc(x_280);
lean_dec(x_279);
x_281 = lean_ctor_get(x_5, 0);
lean_inc(x_281);
x_282 = lean_ctor_get(x_5, 1);
lean_inc(x_282);
x_283 = lean_ctor_get(x_5, 2);
lean_inc(x_283);
x_284 = lean_box(x_261);
x_285 = l_Lean_PersistentHashMap_insert___at___Lean_MetavarContext_addExprMVarDecl_spec__0(lean_box(0), x_283, x_208, x_284);
x_286 = lean_ctor_get(x_5, 3);
lean_inc(x_286);
x_287 = lean_ctor_get(x_5, 4);
lean_inc(x_287);
x_288 = lean_ctor_get(x_5, 5);
lean_inc(x_288);
lean_dec(x_5);
x_289 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_289, 0, x_281);
lean_ctor_set(x_289, 1, x_282);
lean_ctor_set(x_289, 2, x_285);
lean_ctor_set(x_289, 3, x_286);
lean_ctor_set(x_289, 4, x_287);
lean_ctor_set(x_289, 5, x_288);
x_11 = x_289;
x_12 = x_280;
goto block_17;
}
else
{
uint8_t x_290; 
lean_dec(x_208);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_290 = !lean_is_exclusive(x_279);
if (x_290 == 0)
{
return x_279;
}
else
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; 
x_291 = lean_ctor_get(x_279, 0);
x_292 = lean_ctor_get(x_279, 1);
lean_inc(x_292);
lean_inc(x_291);
lean_dec(x_279);
x_293 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_293, 0, x_291);
lean_ctor_set(x_293, 1, x_292);
return x_293;
}
}
}
case 2:
{
lean_object* x_294; lean_object* x_295; 
x_294 = lean_ctor_get(x_211, 1);
lean_inc(x_294);
lean_dec(x_211);
lean_inc(x_184);
lean_inc(x_183);
lean_inc(x_182);
lean_inc(x_181);
lean_inc(x_208);
x_295 = l_Lean_Meta_Grind_isCasesAttrPredicateCandidate_x3f(x_208, x_103, x_181, x_182, x_183, x_184, x_294);
if (lean_obj_tag(x_295) == 0)
{
lean_object* x_296; 
x_296 = lean_ctor_get(x_295, 0);
lean_inc(x_296);
if (lean_obj_tag(x_296) == 0)
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; uint8_t x_306; 
lean_dec(x_31);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_297 = lean_ctor_get(x_295, 1);
lean_inc(x_297);
lean_dec(x_295);
x_298 = lean_mk_string_unchecked("invalid use of `intro` modifier, `", 34, 34);
x_299 = l_Lean_stringToMessageData(x_298);
lean_dec(x_298);
x_300 = l_Lean_MessageData_ofName(x_208);
x_301 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_301, 0, x_299);
lean_ctor_set(x_301, 1, x_300);
x_302 = lean_mk_string_unchecked("` is not an inductive predicate", 31, 31);
x_303 = l_Lean_stringToMessageData(x_302);
lean_dec(x_302);
x_304 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_304, 0, x_301);
lean_ctor_set(x_304, 1, x_303);
x_305 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_304, x_181, x_182, x_183, x_184, x_297);
lean_dec(x_184);
lean_dec(x_183);
lean_dec(x_182);
lean_dec(x_181);
x_306 = !lean_is_exclusive(x_305);
if (x_306 == 0)
{
return x_305;
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_307 = lean_ctor_get(x_305, 0);
x_308 = lean_ctor_get(x_305, 1);
lean_inc(x_308);
lean_inc(x_307);
lean_dec(x_305);
x_309 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_309, 0, x_307);
lean_ctor_set(x_309, 1, x_308);
return x_309;
}
}
else
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; 
lean_dec(x_208);
x_310 = lean_ctor_get(x_295, 1);
lean_inc(x_310);
lean_dec(x_295);
x_311 = lean_ctor_get(x_296, 0);
lean_inc(x_311);
lean_dec(x_296);
x_312 = lean_ctor_get(x_311, 4);
lean_inc(x_312);
lean_dec(x_311);
x_313 = l_List_forIn_x27_loop___at___Lean_Elab_Tactic_elabGrindParams_spec__0___redArg(x_31, x_312, x_5, x_181, x_182, x_183, x_184, x_310);
lean_dec(x_183);
lean_dec(x_31);
if (lean_obj_tag(x_313) == 0)
{
lean_object* x_314; lean_object* x_315; 
x_314 = lean_ctor_get(x_313, 0);
lean_inc(x_314);
x_315 = lean_ctor_get(x_313, 1);
lean_inc(x_315);
lean_dec(x_313);
x_11 = x_314;
x_12 = x_315;
goto block_17;
}
else
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_313;
}
}
}
else
{
uint8_t x_316; 
lean_dec(x_208);
lean_dec(x_184);
lean_dec(x_183);
lean_dec(x_182);
lean_dec(x_181);
lean_dec(x_31);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_316 = !lean_is_exclusive(x_295);
if (x_316 == 0)
{
return x_295;
}
else
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; 
x_317 = lean_ctor_get(x_295, 0);
x_318 = lean_ctor_get(x_295, 1);
lean_inc(x_318);
lean_inc(x_317);
lean_dec(x_295);
x_319 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_319, 0, x_317);
lean_ctor_set(x_319, 1, x_318);
return x_319;
}
}
}
default: 
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; uint8_t x_324; 
lean_dec(x_208);
lean_dec(x_31);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_320 = lean_ctor_get(x_211, 1);
lean_inc(x_320);
lean_dec(x_211);
x_321 = lean_mk_string_unchecked("`[grind ext]` cannot be set using parameters", 44, 44);
x_322 = l_Lean_stringToMessageData(x_321);
lean_dec(x_321);
x_323 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_322, x_181, x_182, x_183, x_184, x_320);
lean_dec(x_184);
lean_dec(x_183);
lean_dec(x_182);
lean_dec(x_181);
x_324 = !lean_is_exclusive(x_323);
if (x_324 == 0)
{
return x_323;
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; 
x_325 = lean_ctor_get(x_323, 0);
x_326 = lean_ctor_get(x_323, 1);
lean_inc(x_326);
lean_inc(x_325);
lean_dec(x_323);
x_327 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_327, 0, x_325);
lean_ctor_set(x_327, 1, x_326);
return x_327;
}
}
}
}
else
{
uint8_t x_328; 
lean_dec(x_208);
lean_dec(x_184);
lean_dec(x_183);
lean_dec(x_182);
lean_dec(x_181);
lean_dec(x_31);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_328 = !lean_is_exclusive(x_211);
if (x_328 == 0)
{
return x_211;
}
else
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; 
x_329 = lean_ctor_get(x_211, 0);
x_330 = lean_ctor_get(x_211, 1);
lean_inc(x_330);
lean_inc(x_329);
lean_dec(x_211);
x_331 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_331, 0, x_329);
lean_ctor_set(x_331, 1, x_330);
return x_331;
}
}
}
}
else
{
uint8_t x_332; 
lean_dec(x_184);
lean_dec(x_183);
lean_dec(x_182);
lean_dec(x_181);
lean_dec(x_180);
lean_dec(x_31);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_332 = !lean_is_exclusive(x_205);
if (x_332 == 0)
{
return x_205;
}
else
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; 
x_333 = lean_ctor_get(x_205, 0);
x_334 = lean_ctor_get(x_205, 1);
lean_inc(x_334);
lean_inc(x_333);
lean_dec(x_205);
x_335 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_335, 0, x_333);
lean_ctor_set(x_335, 1, x_334);
return x_335;
}
}
}
}
}
}
else
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; uint8_t x_378; 
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_80);
x_374 = lean_unsigned_to_nat(1u);
x_375 = l_Lean_Syntax_getArg(x_100, x_374);
lean_dec(x_100);
x_376 = lean_mk_string_unchecked("ident", 5, 5);
x_377 = l_Lean_Name_mkStr1(x_376);
lean_inc(x_375);
x_378 = l_Lean_Syntax_isOfKind(x_375, x_377);
lean_dec(x_377);
if (x_378 == 0)
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; uint8_t x_388; 
lean_dec(x_375);
lean_dec(x_5);
x_379 = lean_mk_string_unchecked("unexpected `grind` parameter", 28, 28);
x_380 = l_Lean_stringToMessageData(x_379);
lean_dec(x_379);
x_381 = l_Lean_MessageData_ofSyntax(x_31);
x_382 = l_Lean_indentD(x_381);
x_383 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_383, 0, x_380);
lean_ctor_set(x_383, 1, x_382);
x_384 = lean_mk_string_unchecked("", 0, 0);
x_385 = l_Lean_stringToMessageData(x_384);
lean_dec(x_384);
x_386 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_386, 0, x_383);
lean_ctor_set(x_386, 1, x_385);
x_387 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_386, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_388 = !lean_is_exclusive(x_387);
if (x_388 == 0)
{
return x_387;
}
else
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; 
x_389 = lean_ctor_get(x_387, 0);
x_390 = lean_ctor_get(x_387, 1);
lean_inc(x_390);
lean_inc(x_389);
lean_dec(x_387);
x_391 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_391, 0, x_389);
lean_ctor_set(x_391, 1, x_390);
return x_391;
}
}
else
{
lean_object* x_392; lean_object* x_393; 
lean_dec(x_31);
x_392 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
x_393 = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(x_375, x_392, x_8, x_9, x_10);
if (lean_obj_tag(x_393) == 0)
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; uint8_t x_397; lean_object* x_398; 
x_394 = lean_ctor_get(x_393, 0);
lean_inc(x_394);
x_395 = lean_ctor_get(x_393, 1);
lean_inc(x_395);
lean_dec(x_393);
x_396 = lean_box(0);
x_397 = lean_unbox(x_396);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_394);
x_398 = l_Lean_Meta_Grind_isCasesAttrCandidate_x3f(x_394, x_397, x_8, x_9, x_395);
if (lean_obj_tag(x_398) == 0)
{
lean_object* x_399; 
x_399 = lean_ctor_get(x_398, 0);
lean_inc(x_399);
if (lean_obj_tag(x_399) == 0)
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; 
x_400 = lean_ctor_get(x_398, 1);
lean_inc(x_400);
lean_dec(x_398);
x_401 = lean_ctor_get(x_5, 1);
lean_inc(x_401);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_402 = l_Lean_Meta_Grind_EMatchTheorems_eraseDecl(x_401, x_394, x_6, x_7, x_8, x_9, x_400);
if (lean_obj_tag(x_402) == 0)
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; 
x_403 = lean_ctor_get(x_402, 0);
lean_inc(x_403);
x_404 = lean_ctor_get(x_402, 1);
lean_inc(x_404);
lean_dec(x_402);
x_405 = lean_ctor_get(x_5, 0);
lean_inc(x_405);
x_406 = lean_ctor_get(x_5, 2);
lean_inc(x_406);
x_407 = lean_ctor_get(x_5, 3);
lean_inc(x_407);
x_408 = lean_ctor_get(x_5, 4);
lean_inc(x_408);
x_409 = lean_ctor_get(x_5, 5);
lean_inc(x_409);
lean_dec(x_5);
x_410 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_410, 0, x_405);
lean_ctor_set(x_410, 1, x_403);
lean_ctor_set(x_410, 2, x_406);
lean_ctor_set(x_410, 3, x_407);
lean_ctor_set(x_410, 4, x_408);
lean_ctor_set(x_410, 5, x_409);
x_11 = x_410;
x_12 = x_404;
goto block_17;
}
else
{
uint8_t x_411; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_411 = !lean_is_exclusive(x_402);
if (x_411 == 0)
{
return x_402;
}
else
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; 
x_412 = lean_ctor_get(x_402, 0);
x_413 = lean_ctor_get(x_402, 1);
lean_inc(x_413);
lean_inc(x_412);
lean_dec(x_402);
x_414 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_414, 0, x_412);
lean_ctor_set(x_414, 1, x_413);
return x_414;
}
}
}
else
{
lean_object* x_415; lean_object* x_416; lean_object* x_417; 
lean_dec(x_394);
x_415 = lean_ctor_get(x_398, 1);
lean_inc(x_415);
lean_dec(x_398);
x_416 = lean_ctor_get(x_399, 0);
lean_inc(x_416);
lean_dec(x_399);
lean_inc(x_416);
x_417 = l_Lean_Meta_Grind_ensureNotBuiltinCases(x_416, x_8, x_9, x_415);
if (lean_obj_tag(x_417) == 0)
{
lean_object* x_418; lean_object* x_419; lean_object* x_420; 
x_418 = lean_ctor_get(x_417, 1);
lean_inc(x_418);
lean_dec(x_417);
x_419 = lean_ctor_get(x_5, 2);
lean_inc(x_419);
x_420 = l_Lean_Meta_Grind_CasesTypes_eraseDecl(x_419, x_416, x_8, x_9, x_418);
if (lean_obj_tag(x_420) == 0)
{
lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; 
x_421 = lean_ctor_get(x_420, 0);
lean_inc(x_421);
x_422 = lean_ctor_get(x_420, 1);
lean_inc(x_422);
lean_dec(x_420);
x_423 = lean_ctor_get(x_5, 0);
lean_inc(x_423);
x_424 = lean_ctor_get(x_5, 1);
lean_inc(x_424);
x_425 = lean_ctor_get(x_5, 3);
lean_inc(x_425);
x_426 = lean_ctor_get(x_5, 4);
lean_inc(x_426);
x_427 = lean_ctor_get(x_5, 5);
lean_inc(x_427);
lean_dec(x_5);
x_428 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_428, 0, x_423);
lean_ctor_set(x_428, 1, x_424);
lean_ctor_set(x_428, 2, x_421);
lean_ctor_set(x_428, 3, x_425);
lean_ctor_set(x_428, 4, x_426);
lean_ctor_set(x_428, 5, x_427);
x_11 = x_428;
x_12 = x_422;
goto block_17;
}
else
{
uint8_t x_429; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_429 = !lean_is_exclusive(x_420);
if (x_429 == 0)
{
return x_420;
}
else
{
lean_object* x_430; lean_object* x_431; lean_object* x_432; 
x_430 = lean_ctor_get(x_420, 0);
x_431 = lean_ctor_get(x_420, 1);
lean_inc(x_431);
lean_inc(x_430);
lean_dec(x_420);
x_432 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_432, 0, x_430);
lean_ctor_set(x_432, 1, x_431);
return x_432;
}
}
}
else
{
uint8_t x_433; 
lean_dec(x_416);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_433 = !lean_is_exclusive(x_417);
if (x_433 == 0)
{
return x_417;
}
else
{
lean_object* x_434; lean_object* x_435; lean_object* x_436; 
x_434 = lean_ctor_get(x_417, 0);
x_435 = lean_ctor_get(x_417, 1);
lean_inc(x_435);
lean_inc(x_434);
lean_dec(x_417);
x_436 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_436, 0, x_434);
lean_ctor_set(x_436, 1, x_435);
return x_436;
}
}
}
}
else
{
uint8_t x_437; 
lean_dec(x_394);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_437 = !lean_is_exclusive(x_398);
if (x_437 == 0)
{
return x_398;
}
else
{
lean_object* x_438; lean_object* x_439; lean_object* x_440; 
x_438 = lean_ctor_get(x_398, 0);
x_439 = lean_ctor_get(x_398, 1);
lean_inc(x_439);
lean_inc(x_438);
lean_dec(x_398);
x_440 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_440, 0, x_438);
lean_ctor_set(x_440, 1, x_439);
return x_440;
}
}
}
else
{
uint8_t x_441; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_441 = !lean_is_exclusive(x_393);
if (x_441 == 0)
{
return x_393;
}
else
{
lean_object* x_442; lean_object* x_443; lean_object* x_444; 
x_442 = lean_ctor_get(x_393, 0);
x_443 = lean_ctor_get(x_393, 1);
lean_inc(x_443);
lean_inc(x_442);
lean_dec(x_393);
x_444 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_444, 0, x_442);
lean_ctor_set(x_444, 1, x_443);
return x_444;
}
}
}
}
}
block_79:
{
lean_object* x_40; uint8_t x_41; 
x_40 = l_Lean_Meta_Grind_getEMatchTheorems___redArg(x_38, x_39);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_42 = lean_ctor_get(x_40, 0);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_33);
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_33);
x_45 = l_Lean_Meta_Grind_EMatchTheorems_find(x_42, x_44);
lean_dec(x_44);
x_46 = lean_box(0);
x_47 = l_List_filterTR_loop___at___Lean_Elab_Tactic_elabGrindParams_spec__1(x_32, x_45, x_46);
x_48 = l_List_isEmpty___redArg(x_47);
if (x_48 == 0)
{
lean_free_object(x_40);
lean_dec(x_33);
lean_dec(x_31);
x_18 = x_47;
x_19 = x_34;
x_20 = x_35;
x_21 = x_36;
x_22 = x_37;
x_23 = x_38;
x_24 = x_43;
goto block_28;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
lean_dec(x_47);
lean_dec(x_34);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_49 = lean_mk_string_unchecked("invalid use of `usr` modifier, `", 32, 32);
x_50 = l_Lean_stringToMessageData(x_49);
lean_dec(x_49);
x_51 = l_Lean_MessageData_ofName(x_33);
lean_ctor_set_tag(x_40, 7);
lean_ctor_set(x_40, 1, x_51);
lean_ctor_set(x_40, 0, x_50);
x_52 = lean_mk_string_unchecked("` does not have patterns specified with the command `grind_pattern`", 67, 67);
x_53 = l_Lean_stringToMessageData(x_52);
lean_dec(x_52);
x_54 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_54, 0, x_40);
lean_ctor_set(x_54, 1, x_53);
x_55 = l_Lean_throwErrorAt___at___Lean_Meta_Match_Alt_checkAndReplaceFVarId_spec__0___redArg(x_31, x_54, x_35, x_36, x_37, x_38, x_43);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_31);
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
return x_55;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_55, 0);
x_58 = lean_ctor_get(x_55, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_55);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_60 = lean_ctor_get(x_40, 0);
x_61 = lean_ctor_get(x_40, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_40);
lean_inc(x_33);
x_62 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_62, 0, x_33);
x_63 = l_Lean_Meta_Grind_EMatchTheorems_find(x_60, x_62);
lean_dec(x_62);
x_64 = lean_box(0);
x_65 = l_List_filterTR_loop___at___Lean_Elab_Tactic_elabGrindParams_spec__1(x_32, x_63, x_64);
x_66 = l_List_isEmpty___redArg(x_65);
if (x_66 == 0)
{
lean_dec(x_33);
lean_dec(x_31);
x_18 = x_65;
x_19 = x_34;
x_20 = x_35;
x_21 = x_36;
x_22 = x_37;
x_23 = x_38;
x_24 = x_61;
goto block_28;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_65);
lean_dec(x_34);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_67 = lean_mk_string_unchecked("invalid use of `usr` modifier, `", 32, 32);
x_68 = l_Lean_stringToMessageData(x_67);
lean_dec(x_67);
x_69 = l_Lean_MessageData_ofName(x_33);
x_70 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
x_71 = lean_mk_string_unchecked("` does not have patterns specified with the command `grind_pattern`", 67, 67);
x_72 = l_Lean_stringToMessageData(x_71);
lean_dec(x_71);
x_73 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_73, 0, x_70);
lean_ctor_set(x_73, 1, x_72);
x_74 = l_Lean_throwErrorAt___at___Lean_Meta_Match_Alt_checkAndReplaceFVarId_spec__0___redArg(x_31, x_73, x_35, x_36, x_37, x_38, x_61);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_31);
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
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(1, 2, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
}
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
block_28:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
x_25 = l_List_forIn_x27_loop___at___Lean_Elab_Tactic_elabGrindParams_spec__2___redArg(x_18, x_19, x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_11 = x_26;
x_12 = x_27;
goto block_17;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_elabGrindParams_spec__3(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_29; 
x_29 = lean_usize_dec_lt(x_4, x_3);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_5);
lean_ctor_set(x_30, 1, x_10);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_31 = lean_array_uget(x_2, x_4);
x_80 = lean_mk_string_unchecked("Lean", 4, 4);
x_81 = lean_mk_string_unchecked("Parser", 6, 6);
x_82 = lean_mk_string_unchecked("Tactic", 6, 6);
x_83 = lean_mk_string_unchecked("grindParam", 10, 10);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
x_84 = l_Lean_Name_mkStr4(x_80, x_81, x_82, x_83);
lean_inc(x_31);
x_85 = l_Lean_Syntax_isOfKind(x_31, x_84);
lean_dec(x_84);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; 
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_5);
x_86 = lean_mk_string_unchecked("unexpected `grind` parameter", 28, 28);
x_87 = l_Lean_stringToMessageData(x_86);
lean_dec(x_86);
x_88 = l_Lean_MessageData_ofSyntax(x_31);
x_89 = l_Lean_indentD(x_88);
x_90 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_90, 0, x_87);
lean_ctor_set(x_90, 1, x_89);
x_91 = lean_mk_string_unchecked("", 0, 0);
x_92 = l_Lean_stringToMessageData(x_91);
lean_dec(x_91);
x_93 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_93, 0, x_90);
lean_ctor_set(x_93, 1, x_92);
x_94 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_93, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
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
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_99 = lean_unsigned_to_nat(0u);
x_100 = l_Lean_Syntax_getArg(x_31, x_99);
x_101 = lean_mk_string_unchecked("grindErase", 10, 10);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
x_102 = l_Lean_Name_mkStr4(x_80, x_81, x_82, x_101);
lean_inc(x_100);
x_103 = l_Lean_Syntax_isOfKind(x_100, x_102);
lean_dec(x_102);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; uint8_t x_106; 
x_104 = lean_mk_string_unchecked("grindLemma", 10, 10);
lean_inc(x_81);
lean_inc(x_80);
x_105 = l_Lean_Name_mkStr4(x_80, x_81, x_82, x_104);
lean_inc(x_100);
x_106 = l_Lean_Syntax_isOfKind(x_100, x_105);
lean_dec(x_105);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; 
lean_dec(x_100);
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_5);
x_107 = lean_mk_string_unchecked("unexpected `grind` parameter", 28, 28);
x_108 = l_Lean_stringToMessageData(x_107);
lean_dec(x_107);
x_109 = l_Lean_MessageData_ofSyntax(x_31);
x_110 = l_Lean_indentD(x_109);
x_111 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_111, 0, x_108);
lean_ctor_set(x_111, 1, x_110);
x_112 = lean_mk_string_unchecked("", 0, 0);
x_113 = l_Lean_stringToMessageData(x_112);
lean_dec(x_112);
x_114 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_114, 0, x_111);
lean_ctor_set(x_114, 1, x_113);
x_115 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_114, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_116 = !lean_is_exclusive(x_115);
if (x_116 == 0)
{
return x_115;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_115, 0);
x_118 = lean_ctor_get(x_115, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_115);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
return x_119;
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_337; uint8_t x_338; 
x_337 = l_Lean_Syntax_getArg(x_100, x_99);
x_338 = l_Lean_Syntax_isNone(x_337);
if (x_338 == 0)
{
lean_object* x_339; uint8_t x_340; 
x_339 = lean_unsigned_to_nat(1u);
lean_inc(x_337);
x_340 = l_Lean_Syntax_matchesNull(x_337, x_339);
if (x_340 == 0)
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; uint8_t x_350; 
lean_dec(x_337);
lean_dec(x_100);
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_5);
x_341 = lean_mk_string_unchecked("unexpected `grind` parameter", 28, 28);
x_342 = l_Lean_stringToMessageData(x_341);
lean_dec(x_341);
x_343 = l_Lean_MessageData_ofSyntax(x_31);
x_344 = l_Lean_indentD(x_343);
x_345 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_345, 0, x_342);
lean_ctor_set(x_345, 1, x_344);
x_346 = lean_mk_string_unchecked("", 0, 0);
x_347 = l_Lean_stringToMessageData(x_346);
lean_dec(x_346);
x_348 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_348, 0, x_345);
lean_ctor_set(x_348, 1, x_347);
x_349 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_348, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_350 = !lean_is_exclusive(x_349);
if (x_350 == 0)
{
return x_349;
}
else
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; 
x_351 = lean_ctor_get(x_349, 0);
x_352 = lean_ctor_get(x_349, 1);
lean_inc(x_352);
lean_inc(x_351);
lean_dec(x_349);
x_353 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_353, 0, x_351);
lean_ctor_set(x_353, 1, x_352);
return x_353;
}
}
else
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; uint8_t x_358; 
x_354 = l_Lean_Syntax_getArg(x_337, x_99);
lean_dec(x_337);
x_355 = lean_mk_string_unchecked("Attr", 4, 4);
x_356 = lean_mk_string_unchecked("grindMod", 8, 8);
x_357 = l_Lean_Name_mkStr4(x_80, x_81, x_355, x_356);
lean_inc(x_354);
x_358 = l_Lean_Syntax_isOfKind(x_354, x_357);
lean_dec(x_357);
if (x_358 == 0)
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; uint8_t x_368; 
lean_dec(x_354);
lean_dec(x_100);
lean_dec(x_5);
x_359 = lean_mk_string_unchecked("unexpected `grind` parameter", 28, 28);
x_360 = l_Lean_stringToMessageData(x_359);
lean_dec(x_359);
x_361 = l_Lean_MessageData_ofSyntax(x_31);
x_362 = l_Lean_indentD(x_361);
x_363 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_363, 0, x_360);
lean_ctor_set(x_363, 1, x_362);
x_364 = lean_mk_string_unchecked("", 0, 0);
x_365 = l_Lean_stringToMessageData(x_364);
lean_dec(x_364);
x_366 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_366, 0, x_363);
lean_ctor_set(x_366, 1, x_365);
x_367 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_366, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_368 = !lean_is_exclusive(x_367);
if (x_368 == 0)
{
return x_367;
}
else
{
lean_object* x_369; lean_object* x_370; lean_object* x_371; 
x_369 = lean_ctor_get(x_367, 0);
x_370 = lean_ctor_get(x_367, 1);
lean_inc(x_370);
lean_inc(x_369);
lean_dec(x_367);
x_371 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_371, 0, x_369);
lean_ctor_set(x_371, 1, x_370);
return x_371;
}
}
else
{
lean_object* x_372; 
x_372 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_372, 0, x_354);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_180 = x_372;
x_181 = x_6;
x_182 = x_7;
x_183 = x_8;
x_184 = x_9;
x_185 = x_10;
goto block_336;
}
}
}
else
{
lean_object* x_373; 
lean_dec(x_337);
lean_dec(x_81);
lean_dec(x_80);
x_373 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_180 = x_373;
x_181 = x_6;
x_182 = x_7;
x_183 = x_8;
x_184 = x_9;
x_185 = x_10;
goto block_336;
}
block_179:
{
lean_object* x_127; 
lean_inc(x_125);
lean_inc(x_124);
lean_inc(x_120);
x_127 = l_Lean_Meta_Grind_isCasesAttrCandidate_x3f(x_120, x_103, x_124, x_125, x_126);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; lean_object* x_144; uint8_t x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; lean_object* x_149; 
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec(x_127);
x_130 = lean_box(8);
x_131 = lean_ctor_get(x_124, 5);
lean_inc(x_131);
x_132 = l_Lean_replaceRef(x_31, x_131);
lean_dec(x_131);
lean_dec(x_31);
x_133 = lean_ctor_get(x_124, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_124, 1);
lean_inc(x_134);
x_135 = lean_ctor_get(x_124, 2);
lean_inc(x_135);
x_136 = lean_ctor_get(x_124, 3);
lean_inc(x_136);
x_137 = lean_ctor_get(x_124, 4);
lean_inc(x_137);
x_138 = lean_ctor_get(x_124, 6);
lean_inc(x_138);
x_139 = lean_ctor_get(x_124, 7);
lean_inc(x_139);
x_140 = lean_ctor_get(x_124, 8);
lean_inc(x_140);
x_141 = lean_ctor_get(x_124, 9);
lean_inc(x_141);
x_142 = lean_ctor_get(x_124, 10);
lean_inc(x_142);
x_143 = lean_ctor_get_uint8(x_124, sizeof(void*)*13);
x_144 = lean_ctor_get(x_124, 11);
lean_inc(x_144);
x_145 = lean_ctor_get_uint8(x_124, sizeof(void*)*13 + 1);
x_146 = lean_ctor_get(x_124, 12);
lean_inc(x_146);
lean_dec(x_124);
x_147 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_147, 0, x_133);
lean_ctor_set(x_147, 1, x_134);
lean_ctor_set(x_147, 2, x_135);
lean_ctor_set(x_147, 3, x_136);
lean_ctor_set(x_147, 4, x_137);
lean_ctor_set(x_147, 5, x_132);
lean_ctor_set(x_147, 6, x_138);
lean_ctor_set(x_147, 7, x_139);
lean_ctor_set(x_147, 8, x_140);
lean_ctor_set(x_147, 9, x_141);
lean_ctor_set(x_147, 10, x_142);
lean_ctor_set(x_147, 11, x_144);
lean_ctor_set(x_147, 12, x_146);
lean_ctor_set_uint8(x_147, sizeof(void*)*13, x_143);
lean_ctor_set_uint8(x_147, sizeof(void*)*13 + 1, x_145);
x_148 = lean_unbox(x_130);
x_149 = l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem(x_121, x_120, x_148, x_122, x_123, x_147, x_125, x_129);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; 
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_149, 1);
lean_inc(x_151);
lean_dec(x_149);
x_11 = x_150;
x_12 = x_151;
goto block_17;
}
else
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_149;
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
lean_dec(x_120);
x_152 = lean_ctor_get(x_127, 1);
lean_inc(x_152);
lean_dec(x_127);
x_153 = lean_ctor_get(x_128, 0);
lean_inc(x_153);
lean_dec(x_128);
lean_inc(x_125);
lean_inc(x_124);
lean_inc(x_123);
lean_inc(x_122);
lean_inc(x_153);
x_154 = l_Lean_Meta_isInductivePredicate_x3f(x_153, x_122, x_123, x_124, x_125, x_152);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_154, 1);
lean_inc(x_156);
lean_dec(x_154);
x_157 = lean_ctor_get(x_121, 2);
lean_inc(x_157);
x_158 = lean_ctor_get(x_121, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_121, 1);
lean_inc(x_159);
x_160 = lean_box(x_103);
x_161 = l_Lean_PersistentHashMap_insert___at___Lean_MetavarContext_addExprMVarDecl_spec__0(lean_box(0), x_157, x_153, x_160);
x_162 = lean_ctor_get(x_121, 3);
lean_inc(x_162);
x_163 = lean_ctor_get(x_121, 4);
lean_inc(x_163);
x_164 = lean_ctor_get(x_121, 5);
lean_inc(x_164);
lean_dec(x_121);
x_165 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_165, 0, x_158);
lean_ctor_set(x_165, 1, x_159);
lean_ctor_set(x_165, 2, x_161);
lean_ctor_set(x_165, 3, x_162);
lean_ctor_set(x_165, 4, x_163);
lean_ctor_set(x_165, 5, x_164);
if (lean_obj_tag(x_155) == 0)
{
lean_dec(x_125);
lean_dec(x_124);
lean_dec(x_123);
lean_dec(x_122);
lean_dec(x_31);
x_11 = x_165;
x_12 = x_156;
goto block_17;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_155, 0);
lean_inc(x_166);
lean_dec(x_155);
x_167 = lean_ctor_get(x_166, 4);
lean_inc(x_167);
lean_dec(x_166);
x_168 = l_List_forIn_x27_loop___at___Lean_Elab_Tactic_elabGrindParams_spec__0___redArg(x_31, x_167, x_165, x_122, x_123, x_124, x_125, x_156);
lean_dec(x_124);
lean_dec(x_31);
if (lean_obj_tag(x_168) == 0)
{
lean_object* x_169; lean_object* x_170; 
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_168, 1);
lean_inc(x_170);
lean_dec(x_168);
x_11 = x_169;
x_12 = x_170;
goto block_17;
}
else
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_168;
}
}
}
else
{
uint8_t x_171; 
lean_dec(x_153);
lean_dec(x_125);
lean_dec(x_124);
lean_dec(x_123);
lean_dec(x_122);
lean_dec(x_121);
lean_dec(x_31);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_171 = !lean_is_exclusive(x_154);
if (x_171 == 0)
{
return x_154;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_172 = lean_ctor_get(x_154, 0);
x_173 = lean_ctor_get(x_154, 1);
lean_inc(x_173);
lean_inc(x_172);
lean_dec(x_154);
x_174 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_174, 0, x_172);
lean_ctor_set(x_174, 1, x_173);
return x_174;
}
}
}
}
else
{
uint8_t x_175; 
lean_dec(x_125);
lean_dec(x_124);
lean_dec(x_123);
lean_dec(x_122);
lean_dec(x_121);
lean_dec(x_120);
lean_dec(x_31);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_175 = !lean_is_exclusive(x_127);
if (x_175 == 0)
{
return x_127;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_176 = lean_ctor_get(x_127, 0);
x_177 = lean_ctor_get(x_127, 1);
lean_inc(x_177);
lean_inc(x_176);
lean_dec(x_127);
x_178 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_178, 0, x_176);
lean_ctor_set(x_178, 1, x_177);
return x_178;
}
}
}
block_336:
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; uint8_t x_190; 
x_186 = lean_unsigned_to_nat(1u);
x_187 = l_Lean_Syntax_getArg(x_100, x_186);
lean_dec(x_100);
x_188 = lean_mk_string_unchecked("ident", 5, 5);
x_189 = l_Lean_Name_mkStr1(x_188);
lean_inc(x_187);
x_190 = l_Lean_Syntax_isOfKind(x_187, x_189);
lean_dec(x_189);
if (x_190 == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; uint8_t x_200; 
lean_dec(x_187);
lean_dec(x_180);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_191 = lean_mk_string_unchecked("unexpected `grind` parameter", 28, 28);
x_192 = l_Lean_stringToMessageData(x_191);
lean_dec(x_191);
x_193 = l_Lean_MessageData_ofSyntax(x_31);
x_194 = l_Lean_indentD(x_193);
x_195 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_195, 0, x_192);
lean_ctor_set(x_195, 1, x_194);
x_196 = lean_mk_string_unchecked("", 0, 0);
x_197 = l_Lean_stringToMessageData(x_196);
lean_dec(x_196);
x_198 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_198, 0, x_195);
lean_ctor_set(x_198, 1, x_197);
x_199 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_198, x_181, x_182, x_183, x_184, x_185);
lean_dec(x_184);
lean_dec(x_183);
lean_dec(x_182);
lean_dec(x_181);
x_200 = !lean_is_exclusive(x_199);
if (x_200 == 0)
{
return x_199;
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_201 = lean_ctor_get(x_199, 0);
x_202 = lean_ctor_get(x_199, 1);
lean_inc(x_202);
lean_inc(x_201);
lean_dec(x_199);
x_203 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_203, 0, x_201);
lean_ctor_set(x_203, 1, x_202);
return x_203;
}
}
else
{
lean_object* x_204; lean_object* x_205; 
x_204 = lean_box(0);
lean_inc(x_184);
lean_inc(x_183);
x_205 = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(x_187, x_204, x_183, x_184, x_185);
if (lean_obj_tag(x_205) == 0)
{
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_206; lean_object* x_207; 
x_206 = lean_ctor_get(x_205, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_205, 1);
lean_inc(x_207);
lean_dec(x_205);
x_120 = x_206;
x_121 = x_5;
x_122 = x_181;
x_123 = x_182;
x_124 = x_183;
x_125 = x_184;
x_126 = x_207;
goto block_179;
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_208 = lean_ctor_get(x_205, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_205, 1);
lean_inc(x_209);
lean_dec(x_205);
x_210 = lean_ctor_get(x_180, 0);
lean_inc(x_210);
lean_dec(x_180);
x_211 = l_Lean_Meta_Grind_getAttrKindCore(x_210, x_183, x_184, x_209);
if (lean_obj_tag(x_211) == 0)
{
lean_object* x_212; 
x_212 = lean_ctor_get(x_211, 0);
lean_inc(x_212);
switch (lean_obj_tag(x_212)) {
case 0:
{
uint8_t x_213; lean_object* x_214; 
x_213 = lean_ctor_get_uint8(x_212, 0);
lean_dec(x_212);
x_214 = lean_box(x_213);
if (lean_obj_tag(x_214) == 9)
{
if (x_1 == 0)
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; uint8_t x_228; lean_object* x_229; uint8_t x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; uint8_t x_234; 
lean_dec(x_208);
lean_dec(x_182);
lean_dec(x_181);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_215 = lean_ctor_get(x_211, 1);
lean_inc(x_215);
lean_dec(x_211);
x_216 = lean_ctor_get(x_183, 5);
lean_inc(x_216);
x_217 = l_Lean_replaceRef(x_31, x_216);
lean_dec(x_216);
lean_dec(x_31);
x_218 = lean_ctor_get(x_183, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_183, 1);
lean_inc(x_219);
x_220 = lean_ctor_get(x_183, 2);
lean_inc(x_220);
x_221 = lean_ctor_get(x_183, 3);
lean_inc(x_221);
x_222 = lean_ctor_get(x_183, 4);
lean_inc(x_222);
x_223 = lean_ctor_get(x_183, 6);
lean_inc(x_223);
x_224 = lean_ctor_get(x_183, 7);
lean_inc(x_224);
x_225 = lean_ctor_get(x_183, 8);
lean_inc(x_225);
x_226 = lean_ctor_get(x_183, 9);
lean_inc(x_226);
x_227 = lean_ctor_get(x_183, 10);
lean_inc(x_227);
x_228 = lean_ctor_get_uint8(x_183, sizeof(void*)*13);
x_229 = lean_ctor_get(x_183, 11);
lean_inc(x_229);
x_230 = lean_ctor_get_uint8(x_183, sizeof(void*)*13 + 1);
x_231 = lean_ctor_get(x_183, 12);
lean_inc(x_231);
lean_dec(x_183);
x_232 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_232, 0, x_218);
lean_ctor_set(x_232, 1, x_219);
lean_ctor_set(x_232, 2, x_220);
lean_ctor_set(x_232, 3, x_221);
lean_ctor_set(x_232, 4, x_222);
lean_ctor_set(x_232, 5, x_217);
lean_ctor_set(x_232, 6, x_223);
lean_ctor_set(x_232, 7, x_224);
lean_ctor_set(x_232, 8, x_225);
lean_ctor_set(x_232, 9, x_226);
lean_ctor_set(x_232, 10, x_227);
lean_ctor_set(x_232, 11, x_229);
lean_ctor_set(x_232, 12, x_231);
lean_ctor_set_uint8(x_232, sizeof(void*)*13, x_228);
lean_ctor_set_uint8(x_232, sizeof(void*)*13 + 1, x_230);
x_233 = l_Lean_Meta_Grind_throwInvalidUsrModifier(lean_box(0), x_232, x_184, x_215);
lean_dec(x_184);
lean_dec(x_232);
x_234 = !lean_is_exclusive(x_233);
if (x_234 == 0)
{
return x_233;
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_235 = lean_ctor_get(x_233, 0);
x_236 = lean_ctor_get(x_233, 1);
lean_inc(x_236);
lean_inc(x_235);
lean_dec(x_233);
x_237 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_237, 0, x_235);
lean_ctor_set(x_237, 1, x_236);
return x_237;
}
}
else
{
lean_object* x_238; 
x_238 = lean_ctor_get(x_211, 1);
lean_inc(x_238);
lean_dec(x_211);
x_32 = x_208;
x_33 = x_213;
x_34 = x_5;
x_35 = x_181;
x_36 = x_182;
x_37 = x_183;
x_38 = x_184;
x_39 = x_238;
goto block_79;
}
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; uint8_t x_252; lean_object* x_253; uint8_t x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
lean_dec(x_214);
x_239 = lean_ctor_get(x_211, 1);
lean_inc(x_239);
lean_dec(x_211);
x_240 = lean_ctor_get(x_183, 5);
lean_inc(x_240);
x_241 = l_Lean_replaceRef(x_31, x_240);
lean_dec(x_240);
lean_dec(x_31);
x_242 = lean_ctor_get(x_183, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_183, 1);
lean_inc(x_243);
x_244 = lean_ctor_get(x_183, 2);
lean_inc(x_244);
x_245 = lean_ctor_get(x_183, 3);
lean_inc(x_245);
x_246 = lean_ctor_get(x_183, 4);
lean_inc(x_246);
x_247 = lean_ctor_get(x_183, 6);
lean_inc(x_247);
x_248 = lean_ctor_get(x_183, 7);
lean_inc(x_248);
x_249 = lean_ctor_get(x_183, 8);
lean_inc(x_249);
x_250 = lean_ctor_get(x_183, 9);
lean_inc(x_250);
x_251 = lean_ctor_get(x_183, 10);
lean_inc(x_251);
x_252 = lean_ctor_get_uint8(x_183, sizeof(void*)*13);
x_253 = lean_ctor_get(x_183, 11);
lean_inc(x_253);
x_254 = lean_ctor_get_uint8(x_183, sizeof(void*)*13 + 1);
x_255 = lean_ctor_get(x_183, 12);
lean_inc(x_255);
lean_dec(x_183);
x_256 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_256, 0, x_242);
lean_ctor_set(x_256, 1, x_243);
lean_ctor_set(x_256, 2, x_244);
lean_ctor_set(x_256, 3, x_245);
lean_ctor_set(x_256, 4, x_246);
lean_ctor_set(x_256, 5, x_241);
lean_ctor_set(x_256, 6, x_247);
lean_ctor_set(x_256, 7, x_248);
lean_ctor_set(x_256, 8, x_249);
lean_ctor_set(x_256, 9, x_250);
lean_ctor_set(x_256, 10, x_251);
lean_ctor_set(x_256, 11, x_253);
lean_ctor_set(x_256, 12, x_255);
lean_ctor_set_uint8(x_256, sizeof(void*)*13, x_252);
lean_ctor_set_uint8(x_256, sizeof(void*)*13 + 1, x_254);
x_257 = l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem(x_5, x_208, x_213, x_181, x_182, x_256, x_184, x_239);
if (lean_obj_tag(x_257) == 0)
{
lean_object* x_258; lean_object* x_259; 
x_258 = lean_ctor_get(x_257, 0);
lean_inc(x_258);
x_259 = lean_ctor_get(x_257, 1);
lean_inc(x_259);
lean_dec(x_257);
x_11 = x_258;
x_12 = x_259;
goto block_17;
}
else
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_257;
}
}
}
case 1:
{
lean_object* x_260; uint8_t x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; uint8_t x_274; lean_object* x_275; uint8_t x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; 
lean_dec(x_182);
lean_dec(x_181);
x_260 = lean_ctor_get(x_211, 1);
lean_inc(x_260);
lean_dec(x_211);
x_261 = lean_ctor_get_uint8(x_212, 0);
lean_dec(x_212);
x_262 = lean_ctor_get(x_183, 5);
lean_inc(x_262);
x_263 = l_Lean_replaceRef(x_31, x_262);
lean_dec(x_262);
lean_dec(x_31);
x_264 = lean_ctor_get(x_183, 0);
lean_inc(x_264);
x_265 = lean_ctor_get(x_183, 1);
lean_inc(x_265);
x_266 = lean_ctor_get(x_183, 2);
lean_inc(x_266);
x_267 = lean_ctor_get(x_183, 3);
lean_inc(x_267);
x_268 = lean_ctor_get(x_183, 4);
lean_inc(x_268);
x_269 = lean_ctor_get(x_183, 6);
lean_inc(x_269);
x_270 = lean_ctor_get(x_183, 7);
lean_inc(x_270);
x_271 = lean_ctor_get(x_183, 8);
lean_inc(x_271);
x_272 = lean_ctor_get(x_183, 9);
lean_inc(x_272);
x_273 = lean_ctor_get(x_183, 10);
lean_inc(x_273);
x_274 = lean_ctor_get_uint8(x_183, sizeof(void*)*13);
x_275 = lean_ctor_get(x_183, 11);
lean_inc(x_275);
x_276 = lean_ctor_get_uint8(x_183, sizeof(void*)*13 + 1);
x_277 = lean_ctor_get(x_183, 12);
lean_inc(x_277);
lean_dec(x_183);
x_278 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_278, 0, x_264);
lean_ctor_set(x_278, 1, x_265);
lean_ctor_set(x_278, 2, x_266);
lean_ctor_set(x_278, 3, x_267);
lean_ctor_set(x_278, 4, x_268);
lean_ctor_set(x_278, 5, x_263);
lean_ctor_set(x_278, 6, x_269);
lean_ctor_set(x_278, 7, x_270);
lean_ctor_set(x_278, 8, x_271);
lean_ctor_set(x_278, 9, x_272);
lean_ctor_set(x_278, 10, x_273);
lean_ctor_set(x_278, 11, x_275);
lean_ctor_set(x_278, 12, x_277);
lean_ctor_set_uint8(x_278, sizeof(void*)*13, x_274);
lean_ctor_set_uint8(x_278, sizeof(void*)*13 + 1, x_276);
lean_inc(x_208);
x_279 = l_Lean_Meta_Grind_validateCasesAttr(x_208, x_261, x_278, x_184, x_260);
if (lean_obj_tag(x_279) == 0)
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; 
x_280 = lean_ctor_get(x_279, 1);
lean_inc(x_280);
lean_dec(x_279);
x_281 = lean_ctor_get(x_5, 0);
lean_inc(x_281);
x_282 = lean_ctor_get(x_5, 1);
lean_inc(x_282);
x_283 = lean_ctor_get(x_5, 2);
lean_inc(x_283);
x_284 = lean_box(x_261);
x_285 = l_Lean_PersistentHashMap_insert___at___Lean_MetavarContext_addExprMVarDecl_spec__0(lean_box(0), x_283, x_208, x_284);
x_286 = lean_ctor_get(x_5, 3);
lean_inc(x_286);
x_287 = lean_ctor_get(x_5, 4);
lean_inc(x_287);
x_288 = lean_ctor_get(x_5, 5);
lean_inc(x_288);
lean_dec(x_5);
x_289 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_289, 0, x_281);
lean_ctor_set(x_289, 1, x_282);
lean_ctor_set(x_289, 2, x_285);
lean_ctor_set(x_289, 3, x_286);
lean_ctor_set(x_289, 4, x_287);
lean_ctor_set(x_289, 5, x_288);
x_11 = x_289;
x_12 = x_280;
goto block_17;
}
else
{
uint8_t x_290; 
lean_dec(x_208);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_290 = !lean_is_exclusive(x_279);
if (x_290 == 0)
{
return x_279;
}
else
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; 
x_291 = lean_ctor_get(x_279, 0);
x_292 = lean_ctor_get(x_279, 1);
lean_inc(x_292);
lean_inc(x_291);
lean_dec(x_279);
x_293 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_293, 0, x_291);
lean_ctor_set(x_293, 1, x_292);
return x_293;
}
}
}
case 2:
{
lean_object* x_294; lean_object* x_295; 
x_294 = lean_ctor_get(x_211, 1);
lean_inc(x_294);
lean_dec(x_211);
lean_inc(x_184);
lean_inc(x_183);
lean_inc(x_182);
lean_inc(x_181);
lean_inc(x_208);
x_295 = l_Lean_Meta_Grind_isCasesAttrPredicateCandidate_x3f(x_208, x_103, x_181, x_182, x_183, x_184, x_294);
if (lean_obj_tag(x_295) == 0)
{
lean_object* x_296; 
x_296 = lean_ctor_get(x_295, 0);
lean_inc(x_296);
if (lean_obj_tag(x_296) == 0)
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; uint8_t x_306; 
lean_dec(x_31);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_297 = lean_ctor_get(x_295, 1);
lean_inc(x_297);
lean_dec(x_295);
x_298 = lean_mk_string_unchecked("invalid use of `intro` modifier, `", 34, 34);
x_299 = l_Lean_stringToMessageData(x_298);
lean_dec(x_298);
x_300 = l_Lean_MessageData_ofName(x_208);
x_301 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_301, 0, x_299);
lean_ctor_set(x_301, 1, x_300);
x_302 = lean_mk_string_unchecked("` is not an inductive predicate", 31, 31);
x_303 = l_Lean_stringToMessageData(x_302);
lean_dec(x_302);
x_304 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_304, 0, x_301);
lean_ctor_set(x_304, 1, x_303);
x_305 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_304, x_181, x_182, x_183, x_184, x_297);
lean_dec(x_184);
lean_dec(x_183);
lean_dec(x_182);
lean_dec(x_181);
x_306 = !lean_is_exclusive(x_305);
if (x_306 == 0)
{
return x_305;
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_307 = lean_ctor_get(x_305, 0);
x_308 = lean_ctor_get(x_305, 1);
lean_inc(x_308);
lean_inc(x_307);
lean_dec(x_305);
x_309 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_309, 0, x_307);
lean_ctor_set(x_309, 1, x_308);
return x_309;
}
}
else
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; 
lean_dec(x_208);
x_310 = lean_ctor_get(x_295, 1);
lean_inc(x_310);
lean_dec(x_295);
x_311 = lean_ctor_get(x_296, 0);
lean_inc(x_311);
lean_dec(x_296);
x_312 = lean_ctor_get(x_311, 4);
lean_inc(x_312);
lean_dec(x_311);
x_313 = l_List_forIn_x27_loop___at___Lean_Elab_Tactic_elabGrindParams_spec__0___redArg(x_31, x_312, x_5, x_181, x_182, x_183, x_184, x_310);
lean_dec(x_183);
lean_dec(x_31);
if (lean_obj_tag(x_313) == 0)
{
lean_object* x_314; lean_object* x_315; 
x_314 = lean_ctor_get(x_313, 0);
lean_inc(x_314);
x_315 = lean_ctor_get(x_313, 1);
lean_inc(x_315);
lean_dec(x_313);
x_11 = x_314;
x_12 = x_315;
goto block_17;
}
else
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_313;
}
}
}
else
{
uint8_t x_316; 
lean_dec(x_208);
lean_dec(x_184);
lean_dec(x_183);
lean_dec(x_182);
lean_dec(x_181);
lean_dec(x_31);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_316 = !lean_is_exclusive(x_295);
if (x_316 == 0)
{
return x_295;
}
else
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; 
x_317 = lean_ctor_get(x_295, 0);
x_318 = lean_ctor_get(x_295, 1);
lean_inc(x_318);
lean_inc(x_317);
lean_dec(x_295);
x_319 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_319, 0, x_317);
lean_ctor_set(x_319, 1, x_318);
return x_319;
}
}
}
default: 
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; uint8_t x_324; 
lean_dec(x_208);
lean_dec(x_31);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_320 = lean_ctor_get(x_211, 1);
lean_inc(x_320);
lean_dec(x_211);
x_321 = lean_mk_string_unchecked("`[grind ext]` cannot be set using parameters", 44, 44);
x_322 = l_Lean_stringToMessageData(x_321);
lean_dec(x_321);
x_323 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_322, x_181, x_182, x_183, x_184, x_320);
lean_dec(x_184);
lean_dec(x_183);
lean_dec(x_182);
lean_dec(x_181);
x_324 = !lean_is_exclusive(x_323);
if (x_324 == 0)
{
return x_323;
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; 
x_325 = lean_ctor_get(x_323, 0);
x_326 = lean_ctor_get(x_323, 1);
lean_inc(x_326);
lean_inc(x_325);
lean_dec(x_323);
x_327 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_327, 0, x_325);
lean_ctor_set(x_327, 1, x_326);
return x_327;
}
}
}
}
else
{
uint8_t x_328; 
lean_dec(x_208);
lean_dec(x_184);
lean_dec(x_183);
lean_dec(x_182);
lean_dec(x_181);
lean_dec(x_31);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_328 = !lean_is_exclusive(x_211);
if (x_328 == 0)
{
return x_211;
}
else
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; 
x_329 = lean_ctor_get(x_211, 0);
x_330 = lean_ctor_get(x_211, 1);
lean_inc(x_330);
lean_inc(x_329);
lean_dec(x_211);
x_331 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_331, 0, x_329);
lean_ctor_set(x_331, 1, x_330);
return x_331;
}
}
}
}
else
{
uint8_t x_332; 
lean_dec(x_184);
lean_dec(x_183);
lean_dec(x_182);
lean_dec(x_181);
lean_dec(x_180);
lean_dec(x_31);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_332 = !lean_is_exclusive(x_205);
if (x_332 == 0)
{
return x_205;
}
else
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; 
x_333 = lean_ctor_get(x_205, 0);
x_334 = lean_ctor_get(x_205, 1);
lean_inc(x_334);
lean_inc(x_333);
lean_dec(x_205);
x_335 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_335, 0, x_333);
lean_ctor_set(x_335, 1, x_334);
return x_335;
}
}
}
}
}
}
else
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; uint8_t x_378; 
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_80);
x_374 = lean_unsigned_to_nat(1u);
x_375 = l_Lean_Syntax_getArg(x_100, x_374);
lean_dec(x_100);
x_376 = lean_mk_string_unchecked("ident", 5, 5);
x_377 = l_Lean_Name_mkStr1(x_376);
lean_inc(x_375);
x_378 = l_Lean_Syntax_isOfKind(x_375, x_377);
lean_dec(x_377);
if (x_378 == 0)
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; uint8_t x_388; 
lean_dec(x_375);
lean_dec(x_5);
x_379 = lean_mk_string_unchecked("unexpected `grind` parameter", 28, 28);
x_380 = l_Lean_stringToMessageData(x_379);
lean_dec(x_379);
x_381 = l_Lean_MessageData_ofSyntax(x_31);
x_382 = l_Lean_indentD(x_381);
x_383 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_383, 0, x_380);
lean_ctor_set(x_383, 1, x_382);
x_384 = lean_mk_string_unchecked("", 0, 0);
x_385 = l_Lean_stringToMessageData(x_384);
lean_dec(x_384);
x_386 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_386, 0, x_383);
lean_ctor_set(x_386, 1, x_385);
x_387 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_386, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_388 = !lean_is_exclusive(x_387);
if (x_388 == 0)
{
return x_387;
}
else
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; 
x_389 = lean_ctor_get(x_387, 0);
x_390 = lean_ctor_get(x_387, 1);
lean_inc(x_390);
lean_inc(x_389);
lean_dec(x_387);
x_391 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_391, 0, x_389);
lean_ctor_set(x_391, 1, x_390);
return x_391;
}
}
else
{
lean_object* x_392; lean_object* x_393; 
lean_dec(x_31);
x_392 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
x_393 = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(x_375, x_392, x_8, x_9, x_10);
if (lean_obj_tag(x_393) == 0)
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; uint8_t x_397; lean_object* x_398; 
x_394 = lean_ctor_get(x_393, 0);
lean_inc(x_394);
x_395 = lean_ctor_get(x_393, 1);
lean_inc(x_395);
lean_dec(x_393);
x_396 = lean_box(0);
x_397 = lean_unbox(x_396);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_394);
x_398 = l_Lean_Meta_Grind_isCasesAttrCandidate_x3f(x_394, x_397, x_8, x_9, x_395);
if (lean_obj_tag(x_398) == 0)
{
lean_object* x_399; 
x_399 = lean_ctor_get(x_398, 0);
lean_inc(x_399);
if (lean_obj_tag(x_399) == 0)
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; 
x_400 = lean_ctor_get(x_398, 1);
lean_inc(x_400);
lean_dec(x_398);
x_401 = lean_ctor_get(x_5, 1);
lean_inc(x_401);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_402 = l_Lean_Meta_Grind_EMatchTheorems_eraseDecl(x_401, x_394, x_6, x_7, x_8, x_9, x_400);
if (lean_obj_tag(x_402) == 0)
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; 
x_403 = lean_ctor_get(x_402, 0);
lean_inc(x_403);
x_404 = lean_ctor_get(x_402, 1);
lean_inc(x_404);
lean_dec(x_402);
x_405 = lean_ctor_get(x_5, 0);
lean_inc(x_405);
x_406 = lean_ctor_get(x_5, 2);
lean_inc(x_406);
x_407 = lean_ctor_get(x_5, 3);
lean_inc(x_407);
x_408 = lean_ctor_get(x_5, 4);
lean_inc(x_408);
x_409 = lean_ctor_get(x_5, 5);
lean_inc(x_409);
lean_dec(x_5);
x_410 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_410, 0, x_405);
lean_ctor_set(x_410, 1, x_403);
lean_ctor_set(x_410, 2, x_406);
lean_ctor_set(x_410, 3, x_407);
lean_ctor_set(x_410, 4, x_408);
lean_ctor_set(x_410, 5, x_409);
x_11 = x_410;
x_12 = x_404;
goto block_17;
}
else
{
uint8_t x_411; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_411 = !lean_is_exclusive(x_402);
if (x_411 == 0)
{
return x_402;
}
else
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; 
x_412 = lean_ctor_get(x_402, 0);
x_413 = lean_ctor_get(x_402, 1);
lean_inc(x_413);
lean_inc(x_412);
lean_dec(x_402);
x_414 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_414, 0, x_412);
lean_ctor_set(x_414, 1, x_413);
return x_414;
}
}
}
else
{
lean_object* x_415; lean_object* x_416; lean_object* x_417; 
lean_dec(x_394);
x_415 = lean_ctor_get(x_398, 1);
lean_inc(x_415);
lean_dec(x_398);
x_416 = lean_ctor_get(x_399, 0);
lean_inc(x_416);
lean_dec(x_399);
lean_inc(x_416);
x_417 = l_Lean_Meta_Grind_ensureNotBuiltinCases(x_416, x_8, x_9, x_415);
if (lean_obj_tag(x_417) == 0)
{
lean_object* x_418; lean_object* x_419; lean_object* x_420; 
x_418 = lean_ctor_get(x_417, 1);
lean_inc(x_418);
lean_dec(x_417);
x_419 = lean_ctor_get(x_5, 2);
lean_inc(x_419);
x_420 = l_Lean_Meta_Grind_CasesTypes_eraseDecl(x_419, x_416, x_8, x_9, x_418);
if (lean_obj_tag(x_420) == 0)
{
lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; 
x_421 = lean_ctor_get(x_420, 0);
lean_inc(x_421);
x_422 = lean_ctor_get(x_420, 1);
lean_inc(x_422);
lean_dec(x_420);
x_423 = lean_ctor_get(x_5, 0);
lean_inc(x_423);
x_424 = lean_ctor_get(x_5, 1);
lean_inc(x_424);
x_425 = lean_ctor_get(x_5, 3);
lean_inc(x_425);
x_426 = lean_ctor_get(x_5, 4);
lean_inc(x_426);
x_427 = lean_ctor_get(x_5, 5);
lean_inc(x_427);
lean_dec(x_5);
x_428 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_428, 0, x_423);
lean_ctor_set(x_428, 1, x_424);
lean_ctor_set(x_428, 2, x_421);
lean_ctor_set(x_428, 3, x_425);
lean_ctor_set(x_428, 4, x_426);
lean_ctor_set(x_428, 5, x_427);
x_11 = x_428;
x_12 = x_422;
goto block_17;
}
else
{
uint8_t x_429; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_429 = !lean_is_exclusive(x_420);
if (x_429 == 0)
{
return x_420;
}
else
{
lean_object* x_430; lean_object* x_431; lean_object* x_432; 
x_430 = lean_ctor_get(x_420, 0);
x_431 = lean_ctor_get(x_420, 1);
lean_inc(x_431);
lean_inc(x_430);
lean_dec(x_420);
x_432 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_432, 0, x_430);
lean_ctor_set(x_432, 1, x_431);
return x_432;
}
}
}
else
{
uint8_t x_433; 
lean_dec(x_416);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_433 = !lean_is_exclusive(x_417);
if (x_433 == 0)
{
return x_417;
}
else
{
lean_object* x_434; lean_object* x_435; lean_object* x_436; 
x_434 = lean_ctor_get(x_417, 0);
x_435 = lean_ctor_get(x_417, 1);
lean_inc(x_435);
lean_inc(x_434);
lean_dec(x_417);
x_436 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_436, 0, x_434);
lean_ctor_set(x_436, 1, x_435);
return x_436;
}
}
}
}
else
{
uint8_t x_437; 
lean_dec(x_394);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_437 = !lean_is_exclusive(x_398);
if (x_437 == 0)
{
return x_398;
}
else
{
lean_object* x_438; lean_object* x_439; lean_object* x_440; 
x_438 = lean_ctor_get(x_398, 0);
x_439 = lean_ctor_get(x_398, 1);
lean_inc(x_439);
lean_inc(x_438);
lean_dec(x_398);
x_440 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_440, 0, x_438);
lean_ctor_set(x_440, 1, x_439);
return x_440;
}
}
}
else
{
uint8_t x_441; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_441 = !lean_is_exclusive(x_393);
if (x_441 == 0)
{
return x_393;
}
else
{
lean_object* x_442; lean_object* x_443; lean_object* x_444; 
x_442 = lean_ctor_get(x_393, 0);
x_443 = lean_ctor_get(x_393, 1);
lean_inc(x_443);
lean_inc(x_442);
lean_dec(x_393);
x_444 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_444, 0, x_442);
lean_ctor_set(x_444, 1, x_443);
return x_444;
}
}
}
}
}
block_79:
{
lean_object* x_40; uint8_t x_41; 
x_40 = l_Lean_Meta_Grind_getEMatchTheorems___redArg(x_38, x_39);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_42 = lean_ctor_get(x_40, 0);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_32);
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_32);
x_45 = l_Lean_Meta_Grind_EMatchTheorems_find(x_42, x_44);
lean_dec(x_44);
x_46 = lean_box(0);
x_47 = l_List_filterTR_loop___at___Lean_Elab_Tactic_elabGrindParams_spec__1(x_33, x_45, x_46);
x_48 = l_List_isEmpty___redArg(x_47);
if (x_48 == 0)
{
lean_free_object(x_40);
lean_dec(x_32);
lean_dec(x_31);
x_18 = x_47;
x_19 = x_34;
x_20 = x_35;
x_21 = x_36;
x_22 = x_37;
x_23 = x_38;
x_24 = x_43;
goto block_28;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
lean_dec(x_47);
lean_dec(x_34);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_49 = lean_mk_string_unchecked("invalid use of `usr` modifier, `", 32, 32);
x_50 = l_Lean_stringToMessageData(x_49);
lean_dec(x_49);
x_51 = l_Lean_MessageData_ofName(x_32);
lean_ctor_set_tag(x_40, 7);
lean_ctor_set(x_40, 1, x_51);
lean_ctor_set(x_40, 0, x_50);
x_52 = lean_mk_string_unchecked("` does not have patterns specified with the command `grind_pattern`", 67, 67);
x_53 = l_Lean_stringToMessageData(x_52);
lean_dec(x_52);
x_54 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_54, 0, x_40);
lean_ctor_set(x_54, 1, x_53);
x_55 = l_Lean_throwErrorAt___at___Lean_Meta_Match_Alt_checkAndReplaceFVarId_spec__0___redArg(x_31, x_54, x_35, x_36, x_37, x_38, x_43);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_31);
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
return x_55;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_55, 0);
x_58 = lean_ctor_get(x_55, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_55);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_60 = lean_ctor_get(x_40, 0);
x_61 = lean_ctor_get(x_40, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_40);
lean_inc(x_32);
x_62 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_62, 0, x_32);
x_63 = l_Lean_Meta_Grind_EMatchTheorems_find(x_60, x_62);
lean_dec(x_62);
x_64 = lean_box(0);
x_65 = l_List_filterTR_loop___at___Lean_Elab_Tactic_elabGrindParams_spec__1(x_33, x_63, x_64);
x_66 = l_List_isEmpty___redArg(x_65);
if (x_66 == 0)
{
lean_dec(x_32);
lean_dec(x_31);
x_18 = x_65;
x_19 = x_34;
x_20 = x_35;
x_21 = x_36;
x_22 = x_37;
x_23 = x_38;
x_24 = x_61;
goto block_28;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_65);
lean_dec(x_34);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_67 = lean_mk_string_unchecked("invalid use of `usr` modifier, `", 32, 32);
x_68 = l_Lean_stringToMessageData(x_67);
lean_dec(x_67);
x_69 = l_Lean_MessageData_ofName(x_32);
x_70 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
x_71 = lean_mk_string_unchecked("` does not have patterns specified with the command `grind_pattern`", 67, 67);
x_72 = l_Lean_stringToMessageData(x_71);
lean_dec(x_71);
x_73 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_73, 0, x_70);
lean_ctor_set(x_73, 1, x_72);
x_74 = l_Lean_throwErrorAt___at___Lean_Meta_Match_Alt_checkAndReplaceFVarId_spec__0___redArg(x_31, x_73, x_35, x_36, x_37, x_38, x_61);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_31);
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
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(1, 2, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
}
}
}
block_17:
{
lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_usize_of_nat(x_13);
x_15 = lean_usize_add(x_4, x_14);
x_16 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_elabGrindParams_spec__3_spec__3(x_1, x_2, x_3, x_15, x_11, x_6, x_7, x_8, x_9, x_12);
return x_16;
}
block_28:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
x_25 = l_List_forIn_x27_loop___at___Lean_Elab_Tactic_elabGrindParams_spec__2___redArg(x_18, x_19, x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_11 = x_26;
x_12 = x_27;
goto block_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindParams(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; lean_object* x_10; size_t x_11; lean_object* x_12; 
x_9 = lean_array_size(x_2);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_usize_of_nat(x_10);
x_12 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_elabGrindParams_spec__3(x_3, x_2, x_9, x_11, x_1, x_4, x_5, x_6, x_7, x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Elab_Tactic_elabGrindParams_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_forIn_x27_loop___at___Lean_Elab_Tactic_elabGrindParams_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Elab_Tactic_elabGrindParams_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_List_forIn_x27_loop___at___Lean_Elab_Tactic_elabGrindParams_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___Lean_Elab_Tactic_elabGrindParams_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_List_filterTR_loop___at___Lean_Elab_Tactic_elabGrindParams_spec__1(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Elab_Tactic_elabGrindParams_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_List_forIn_x27_loop___at___Lean_Elab_Tactic_elabGrindParams_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_elabGrindParams_spec__3_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_elabGrindParams_spec__3_spec__3(x_11, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_elabGrindParams_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_elabGrindParams_spec__3(x_11, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindParams___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lean_Elab_Tactic_elabGrindParams(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkGrindParams(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Grind_mkParams(x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
if (x_2 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = l_Lean_Meta_Grind_getEMatchTheorems___redArg(x_7, x_11);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_26 = x_39;
x_27 = x_4;
x_28 = x_5;
x_29 = x_6;
x_30 = x_7;
x_31 = x_40;
goto block_37;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_41 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_41);
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_41);
x_43 = l_Lean_PersistentHashMap_empty___at___Lean_Meta_Grind_initFn____x40_Lean_Meta_Tactic_Grind_EMatchTheorem___hyg_2570__spec__0(lean_box(0));
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_41);
lean_inc(x_43);
x_45 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_43);
lean_ctor_set(x_45, 2, x_43);
lean_ctor_set(x_45, 3, x_44);
x_26 = x_45;
x_27 = x_4;
x_28 = x_5;
x_29 = x_6;
x_30 = x_7;
x_31 = x_11;
goto block_37;
}
block_25:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_10, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_10, 3);
lean_inc(x_20);
x_21 = lean_ctor_get(x_10, 4);
lean_inc(x_21);
x_22 = lean_ctor_get(x_10, 5);
lean_inc(x_22);
lean_dec(x_10);
x_23 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_23, 0, x_19);
lean_ctor_set(x_23, 1, x_12);
lean_ctor_set(x_23, 2, x_13);
lean_ctor_set(x_23, 3, x_20);
lean_ctor_set(x_23, 4, x_21);
lean_ctor_set(x_23, 5, x_22);
x_24 = l_Lean_Elab_Tactic_elabGrindParams(x_23, x_3, x_2, x_14, x_15, x_16, x_17, x_18);
return x_24;
}
block_37:
{
if (x_2 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = l_Lean_Meta_Grind_getCasesTypes(x_29, x_30, x_31);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_12 = x_26;
x_13 = x_33;
x_14 = x_27;
x_15 = x_28;
x_16 = x_29;
x_17 = x_30;
x_18 = x_34;
goto block_25;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_36 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_12 = x_26;
x_13 = x_36;
x_14 = x_27;
x_15 = x_28;
x_16 = x_29;
x_17 = x_30;
x_18 = x_31;
goto block_25;
}
}
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkGrindParams___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_Lean_Elab_Tactic_mkGrindParams(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_grind___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_16 = l_Lean_Elab_Tactic_mkGrindParams(x_1, x_2, x_3, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_4);
x_19 = l_Lean_MVarId_getType(x_4, x_11, x_12, x_13, x_14, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_box(0);
lean_inc(x_11);
lean_inc(x_20);
x_23 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_20, x_22, x_11, x_12, x_13, x_14, x_21);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_23, 1);
x_27 = l_Lean_Expr_mvarId_x21(x_25);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_5);
x_28 = l_Lean_Meta_Grind_main(x_27, x_17, x_5, x_6, x_11, x_12, x_13, x_14, x_26);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_49; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_49 = l_Lean_Meta_Grind_Result_hasFailures(x_29);
if (x_49 == 0)
{
lean_object* x_50; 
lean_free_object(x_23);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_20);
x_50 = l_Lean_Meta_isProp(x_20, x_11, x_12, x_13, x_14, x_30);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_box(1);
x_54 = lean_unbox(x_51);
lean_dec(x_51);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_5);
x_55 = lean_mk_string_unchecked("grind", 5, 5);
x_56 = l_Lean_Name_mkStr1(x_55);
lean_inc(x_9);
x_57 = l_Lean_Elab_Term_mkAuxName(x_56, x_9, x_10, x_11, x_12, x_13, x_14, x_52);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_60 = l_Lean_Elab_instantiateMVarsProfiling(x_25, x_11, x_12, x_13, x_14, x_59);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; uint8_t x_64; lean_object* x_65; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = lean_unbox(x_53);
x_64 = lean_unbox(x_53);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_65 = l_Lean_Meta_mkAuxDefinition(x_58, x_20, x_61, x_63, x_64, x_11, x_12, x_13, x_14, x_62);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_31 = x_66;
x_32 = x_7;
x_33 = x_8;
x_34 = x_9;
x_35 = x_10;
x_36 = x_11;
x_37 = x_12;
x_38 = x_13;
x_39 = x_14;
x_40 = x_67;
goto block_48;
}
else
{
uint8_t x_68; 
lean_dec(x_29);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_4);
x_68 = !lean_is_exclusive(x_65);
if (x_68 == 0)
{
return x_65;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_65, 0);
x_70 = lean_ctor_get(x_65, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_65);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
else
{
uint8_t x_72; 
lean_dec(x_58);
lean_dec(x_29);
lean_dec(x_20);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_4);
x_72 = !lean_is_exclusive(x_60);
if (x_72 == 0)
{
return x_60;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_60, 0);
x_74 = lean_ctor_get(x_60, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_60);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
else
{
lean_object* x_76; 
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_76 = l_Lean_Elab_instantiateMVarsProfiling(x_25, x_11, x_12, x_13, x_14, x_52);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; uint8_t x_81; lean_object* x_82; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_5);
x_80 = lean_unbox(x_53);
x_81 = lean_unbox(x_53);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_82 = l_Lean_Meta_mkAuxTheorem(x_20, x_77, x_80, x_79, x_81, x_11, x_12, x_13, x_14, x_78);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_31 = x_83;
x_32 = x_7;
x_33 = x_8;
x_34 = x_9;
x_35 = x_10;
x_36 = x_11;
x_37 = x_12;
x_38 = x_13;
x_39 = x_14;
x_40 = x_84;
goto block_48;
}
else
{
uint8_t x_85; 
lean_dec(x_29);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_4);
x_85 = !lean_is_exclusive(x_82);
if (x_85 == 0)
{
return x_82;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_82, 0);
x_87 = lean_ctor_get(x_82, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_82);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
else
{
uint8_t x_89; 
lean_dec(x_29);
lean_dec(x_20);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
x_89 = !lean_is_exclusive(x_76);
if (x_89 == 0)
{
return x_76;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_76, 0);
x_91 = lean_ctor_get(x_76, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_76);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
}
else
{
uint8_t x_93; 
lean_dec(x_29);
lean_dec(x_25);
lean_dec(x_20);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
x_93 = !lean_is_exclusive(x_50);
if (x_93 == 0)
{
return x_50;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_50, 0);
x_95 = lean_ctor_get(x_50, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_50);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
}
else
{
lean_object* x_97; 
lean_dec(x_25);
lean_dec(x_20);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_97 = l_Lean_Meta_Grind_Result_toMessageData(x_29, x_11, x_12, x_13, x_14, x_30);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec(x_97);
x_100 = lean_mk_string_unchecked("`grind` failed\n", 15, 15);
x_101 = l_Lean_stringToMessageData(x_100);
lean_dec(x_100);
lean_ctor_set_tag(x_23, 7);
lean_ctor_set(x_23, 1, x_98);
lean_ctor_set(x_23, 0, x_101);
x_102 = lean_mk_string_unchecked("", 0, 0);
x_103 = l_Lean_stringToMessageData(x_102);
lean_dec(x_102);
x_104 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_104, 0, x_23);
lean_ctor_set(x_104, 1, x_103);
x_105 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(x_104, x_11, x_12, x_13, x_14, x_99);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_106 = !lean_is_exclusive(x_105);
if (x_106 == 0)
{
return x_105;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_105, 0);
x_108 = lean_ctor_get(x_105, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_105);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
}
else
{
uint8_t x_110; 
lean_free_object(x_23);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_110 = !lean_is_exclusive(x_97);
if (x_110 == 0)
{
return x_97;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_97, 0);
x_112 = lean_ctor_get(x_97, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_97);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
}
block_48:
{
lean_object* x_41; uint8_t x_42; 
x_41 = l_Lean_MVarId_assign___at___Lean_Elab_Tactic_refineCore_spec__0(x_4, x_31, x_32, x_33, x_34, x_35, x_36, x_37, x_38, x_39, x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_34);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_41, 0);
lean_dec(x_43);
x_44 = lean_ctor_get(x_29, 4);
lean_inc(x_44);
lean_dec(x_29);
lean_ctor_set(x_41, 0, x_44);
return x_41;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_41, 1);
lean_inc(x_45);
lean_dec(x_41);
x_46 = lean_ctor_get(x_29, 4);
lean_inc(x_46);
lean_dec(x_29);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
}
else
{
uint8_t x_114; 
lean_free_object(x_23);
lean_dec(x_25);
lean_dec(x_20);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
x_114 = !lean_is_exclusive(x_28);
if (x_114 == 0)
{
return x_28;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_28, 0);
x_116 = lean_ctor_get(x_28, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_28);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_118 = lean_ctor_get(x_23, 0);
x_119 = lean_ctor_get(x_23, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_23);
x_120 = l_Lean_Expr_mvarId_x21(x_118);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_5);
x_121 = l_Lean_Meta_Grind_main(x_120, x_17, x_5, x_6, x_11, x_12, x_13, x_14, x_119);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; uint8_t x_140; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
lean_dec(x_121);
x_140 = l_Lean_Meta_Grind_Result_hasFailures(x_122);
if (x_140 == 0)
{
lean_object* x_141; 
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_20);
x_141 = l_Lean_Meta_isProp(x_20, x_11, x_12, x_13, x_14, x_123);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; 
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
lean_dec(x_141);
x_144 = lean_box(1);
x_145 = lean_unbox(x_142);
lean_dec(x_142);
if (x_145 == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
lean_dec(x_5);
x_146 = lean_mk_string_unchecked("grind", 5, 5);
x_147 = l_Lean_Name_mkStr1(x_146);
lean_inc(x_9);
x_148 = l_Lean_Elab_Term_mkAuxName(x_147, x_9, x_10, x_11, x_12, x_13, x_14, x_143);
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_148, 1);
lean_inc(x_150);
lean_dec(x_148);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_151 = l_Lean_Elab_instantiateMVarsProfiling(x_118, x_11, x_12, x_13, x_14, x_150);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; lean_object* x_153; uint8_t x_154; uint8_t x_155; lean_object* x_156; 
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_151, 1);
lean_inc(x_153);
lean_dec(x_151);
x_154 = lean_unbox(x_144);
x_155 = lean_unbox(x_144);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_156 = l_Lean_Meta_mkAuxDefinition(x_149, x_20, x_152, x_154, x_155, x_11, x_12, x_13, x_14, x_153);
if (lean_obj_tag(x_156) == 0)
{
lean_object* x_157; lean_object* x_158; 
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
lean_dec(x_156);
x_124 = x_157;
x_125 = x_7;
x_126 = x_8;
x_127 = x_9;
x_128 = x_10;
x_129 = x_11;
x_130 = x_12;
x_131 = x_13;
x_132 = x_14;
x_133 = x_158;
goto block_139;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
lean_dec(x_122);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_4);
x_159 = lean_ctor_get(x_156, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_156, 1);
lean_inc(x_160);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 lean_ctor_release(x_156, 1);
 x_161 = x_156;
} else {
 lean_dec_ref(x_156);
 x_161 = lean_box(0);
}
if (lean_is_scalar(x_161)) {
 x_162 = lean_alloc_ctor(1, 2, 0);
} else {
 x_162 = x_161;
}
lean_ctor_set(x_162, 0, x_159);
lean_ctor_set(x_162, 1, x_160);
return x_162;
}
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_dec(x_149);
lean_dec(x_122);
lean_dec(x_20);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_4);
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
lean_object* x_167; 
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_167 = l_Lean_Elab_instantiateMVarsProfiling(x_118, x_11, x_12, x_13, x_14, x_143);
if (lean_obj_tag(x_167) == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; uint8_t x_171; uint8_t x_172; lean_object* x_173; 
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_167, 1);
lean_inc(x_169);
lean_dec(x_167);
x_170 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_170, 0, x_5);
x_171 = lean_unbox(x_144);
x_172 = lean_unbox(x_144);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_173 = l_Lean_Meta_mkAuxTheorem(x_20, x_168, x_171, x_170, x_172, x_11, x_12, x_13, x_14, x_169);
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_174; lean_object* x_175; 
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_173, 1);
lean_inc(x_175);
lean_dec(x_173);
x_124 = x_174;
x_125 = x_7;
x_126 = x_8;
x_127 = x_9;
x_128 = x_10;
x_129 = x_11;
x_130 = x_12;
x_131 = x_13;
x_132 = x_14;
x_133 = x_175;
goto block_139;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
lean_dec(x_122);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_4);
x_176 = lean_ctor_get(x_173, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_173, 1);
lean_inc(x_177);
if (lean_is_exclusive(x_173)) {
 lean_ctor_release(x_173, 0);
 lean_ctor_release(x_173, 1);
 x_178 = x_173;
} else {
 lean_dec_ref(x_173);
 x_178 = lean_box(0);
}
if (lean_is_scalar(x_178)) {
 x_179 = lean_alloc_ctor(1, 2, 0);
} else {
 x_179 = x_178;
}
lean_ctor_set(x_179, 0, x_176);
lean_ctor_set(x_179, 1, x_177);
return x_179;
}
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
lean_dec(x_122);
lean_dec(x_20);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
x_180 = lean_ctor_get(x_167, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_167, 1);
lean_inc(x_181);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 lean_ctor_release(x_167, 1);
 x_182 = x_167;
} else {
 lean_dec_ref(x_167);
 x_182 = lean_box(0);
}
if (lean_is_scalar(x_182)) {
 x_183 = lean_alloc_ctor(1, 2, 0);
} else {
 x_183 = x_182;
}
lean_ctor_set(x_183, 0, x_180);
lean_ctor_set(x_183, 1, x_181);
return x_183;
}
}
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
lean_dec(x_122);
lean_dec(x_118);
lean_dec(x_20);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
x_184 = lean_ctor_get(x_141, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_141, 1);
lean_inc(x_185);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_186 = x_141;
} else {
 lean_dec_ref(x_141);
 x_186 = lean_box(0);
}
if (lean_is_scalar(x_186)) {
 x_187 = lean_alloc_ctor(1, 2, 0);
} else {
 x_187 = x_186;
}
lean_ctor_set(x_187, 0, x_184);
lean_ctor_set(x_187, 1, x_185);
return x_187;
}
}
else
{
lean_object* x_188; 
lean_dec(x_118);
lean_dec(x_20);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_188 = l_Lean_Meta_Grind_Result_toMessageData(x_122, x_11, x_12, x_13, x_14, x_123);
if (lean_obj_tag(x_188) == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_188, 1);
lean_inc(x_190);
lean_dec(x_188);
x_191 = lean_mk_string_unchecked("`grind` failed\n", 15, 15);
x_192 = l_Lean_stringToMessageData(x_191);
lean_dec(x_191);
x_193 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_189);
x_194 = lean_mk_string_unchecked("", 0, 0);
x_195 = l_Lean_stringToMessageData(x_194);
lean_dec(x_194);
x_196 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_196, 0, x_193);
lean_ctor_set(x_196, 1, x_195);
x_197 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(x_196, x_11, x_12, x_13, x_14, x_190);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_197, 1);
lean_inc(x_199);
if (lean_is_exclusive(x_197)) {
 lean_ctor_release(x_197, 0);
 lean_ctor_release(x_197, 1);
 x_200 = x_197;
} else {
 lean_dec_ref(x_197);
 x_200 = lean_box(0);
}
if (lean_is_scalar(x_200)) {
 x_201 = lean_alloc_ctor(1, 2, 0);
} else {
 x_201 = x_200;
}
lean_ctor_set(x_201, 0, x_198);
lean_ctor_set(x_201, 1, x_199);
return x_201;
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_202 = lean_ctor_get(x_188, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_188, 1);
lean_inc(x_203);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 x_204 = x_188;
} else {
 lean_dec_ref(x_188);
 x_204 = lean_box(0);
}
if (lean_is_scalar(x_204)) {
 x_205 = lean_alloc_ctor(1, 2, 0);
} else {
 x_205 = x_204;
}
lean_ctor_set(x_205, 0, x_202);
lean_ctor_set(x_205, 1, x_203);
return x_205;
}
}
block_139:
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_134 = l_Lean_MVarId_assign___at___Lean_Elab_Tactic_refineCore_spec__0(x_4, x_124, x_125, x_126, x_127, x_128, x_129, x_130, x_131, x_132, x_133);
lean_dec(x_132);
lean_dec(x_131);
lean_dec(x_130);
lean_dec(x_129);
lean_dec(x_127);
x_135 = lean_ctor_get(x_134, 1);
lean_inc(x_135);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_136 = x_134;
} else {
 lean_dec_ref(x_134);
 x_136 = lean_box(0);
}
x_137 = lean_ctor_get(x_122, 4);
lean_inc(x_137);
lean_dec(x_122);
if (lean_is_scalar(x_136)) {
 x_138 = lean_alloc_ctor(0, 2, 0);
} else {
 x_138 = x_136;
}
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_135);
return x_138;
}
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
lean_dec(x_118);
lean_dec(x_20);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
x_206 = lean_ctor_get(x_121, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_121, 1);
lean_inc(x_207);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 lean_ctor_release(x_121, 1);
 x_208 = x_121;
} else {
 lean_dec_ref(x_121);
 x_208 = lean_box(0);
}
if (lean_is_scalar(x_208)) {
 x_209 = lean_alloc_ctor(1, 2, 0);
} else {
 x_209 = x_208;
}
lean_ctor_set(x_209, 0, x_206);
lean_ctor_set(x_209, 1, x_207);
return x_209;
}
}
}
else
{
uint8_t x_210; 
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_210 = !lean_is_exclusive(x_19);
if (x_210 == 0)
{
return x_19;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_211 = lean_ctor_get(x_19, 0);
x_212 = lean_ctor_get(x_19, 1);
lean_inc(x_212);
lean_inc(x_211);
lean_dec(x_19);
x_213 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_213, 0, x_211);
lean_ctor_set(x_213, 1, x_212);
return x_213;
}
}
}
else
{
uint8_t x_214; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_214 = !lean_is_exclusive(x_16);
if (x_214 == 0)
{
return x_16;
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_215 = lean_ctor_get(x_16, 0);
x_216 = lean_ctor_get(x_16, 1);
lean_inc(x_216);
lean_inc(x_215);
lean_dec(x_16);
x_217 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_217, 0, x_215);
lean_ctor_set(x_217, 1, x_216);
return x_217;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_grind(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_box(x_3);
lean_inc(x_1);
x_17 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_grind___lam__0___boxed), 15, 6);
lean_closure_set(x_17, 0, x_2);
lean_closure_set(x_17, 1, x_16);
lean_closure_set(x_17, 2, x_4);
lean_closure_set(x_17, 3, x_1);
lean_closure_set(x_17, 4, x_5);
lean_closure_set(x_17, 5, x_6);
x_18 = l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_withMainContext_spec__0___redArg(x_1, x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_grind___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_2);
lean_dec(x_2);
x_17 = l_Lean_Elab_Tactic_grind___lam__0(x_1, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_grind___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_3);
lean_dec(x_3);
x_17 = l_Lean_Elab_Tactic_grind(x_1, x_2, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_11);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___Lean_evalConst___at_____private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback_unsafe__1_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = l_Lean_stringToMessageData(x_9);
x_11 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_2);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_8);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___Lean_evalConst___at_____private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback_unsafe__1_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_ofExcept___at___Lean_evalConst___at_____private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback_unsafe__1_spec__0_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at_____private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback_unsafe__1_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_6, 2);
x_14 = lean_eval_const(x_12, x_13, x_1);
lean_dec(x_12);
x_15 = l_Lean_ofExcept___at___Lean_evalConst___at_____private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback_unsafe__1_spec__0_spec__0___redArg(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
lean_dec(x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at_____private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback_unsafe__1_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_evalConst___at_____private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback_unsafe__1_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback_unsafe__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_evalConst___at_____private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback_unsafe__1_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___Lean_evalConst___at_____private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback_unsafe__1_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_ofExcept___at___Lean_evalConst___at_____private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback_unsafe__1_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___Lean_evalConst___at_____private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback_unsafe__1_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_ofExcept___at___Lean_evalConst___at_____private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback_unsafe__1_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at_____private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback_unsafe__1_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_evalConst___at_____private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback_unsafe__1_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at_____private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback_unsafe__1_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_evalConst___at_____private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback_unsafe__1_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback_unsafe__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback_unsafe__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_box(0);
x_10 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___lam__0___boxed), 10, 1);
lean_closure_set(x_10, 0, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_1);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; size_t x_29; lean_object* x_30; lean_object* x_31; size_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_mk_string_unchecked("Lean", 4, 4);
x_15 = lean_mk_string_unchecked("Meta", 4, 4);
x_16 = lean_mk_string_unchecked("Grind", 5, 5);
x_17 = lean_mk_string_unchecked("GoalM", 5, 5);
x_18 = l_Lean_Name_mkStr4(x_14, x_15, x_16, x_17);
x_19 = lean_box(0);
x_20 = l_Lean_Expr_const___override(x_18, x_19);
x_21 = lean_mk_string_unchecked("Unit", 4, 4);
x_22 = l_Lean_Name_mkStr1(x_21);
x_23 = l_Lean_Expr_const___override(x_22, x_19);
x_24 = l_Lean_Expr_app___override(x_20, x_23);
x_25 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
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
x_36 = lean_unsigned_to_nat(0u);
x_37 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_34);
lean_ctor_set(x_37, 2, x_36);
lean_ctor_set(x_37, 3, x_36);
lean_ctor_set_usize(x_37, 4, x_29);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_39, 0, x_26);
lean_ctor_set(x_39, 1, x_37);
lean_ctor_set(x_39, 2, x_38);
x_40 = l_Array_empty(lean_box(0));
lean_inc(x_24);
lean_ctor_set(x_1, 0, x_24);
x_41 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermAndSynthesize___boxed), 9, 2);
lean_closure_set(x_41, 0, x_13);
lean_closure_set(x_41, 1, x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
x_42 = l_Lean_Meta_withLCtx___at___Lean_Elab_Term_MVarErrorInfo_logError_spec__3___redArg(x_39, x_40, x_41, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
if (lean_obj_tag(x_43) == 4)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_24);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_ctor_get(x_43, 0);
lean_inc(x_45);
lean_dec(x_43);
x_46 = l_Lean_evalConst___at_____private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback_unsafe__1_spec__0___redArg(x_45, x_2, x_3, x_4, x_5, x_6, x_7, x_44);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_45);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_47 = lean_ctor_get(x_42, 1);
lean_inc(x_47);
lean_dec(x_42);
x_48 = lean_mk_string_unchecked("_grind_fallback", 15, 15);
x_49 = l_Lean_Name_mkStr1(x_48);
lean_inc(x_2);
x_50 = l_Lean_Elab_Term_mkAuxName(x_49, x_2, x_3, x_4, x_5, x_6, x_7, x_47);
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; 
x_52 = lean_ctor_get(x_50, 0);
x_53 = lean_ctor_get(x_50, 1);
x_54 = lean_box(0);
lean_inc(x_52);
x_55 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_55, 0, x_52);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set(x_55, 2, x_24);
x_56 = lean_box(0);
x_57 = lean_box(1);
lean_inc(x_52);
lean_ctor_set_tag(x_50, 1);
lean_ctor_set(x_50, 1, x_54);
x_58 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_43);
lean_ctor_set(x_58, 2, x_56);
lean_ctor_set(x_58, 3, x_50);
x_59 = lean_unbox(x_57);
lean_ctor_set_uint8(x_58, sizeof(void*)*4, x_59);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_58);
lean_inc(x_7);
lean_inc(x_6);
x_61 = l_Lean_addAndCompile(x_60, x_6, x_7, x_53);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
lean_dec(x_61);
x_63 = l_Lean_evalConst___at_____private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback_unsafe__1_spec__0___redArg(x_52, x_2, x_3, x_4, x_5, x_6, x_7, x_62);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_52);
return x_63;
}
else
{
uint8_t x_64; 
lean_dec(x_52);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_64 = !lean_is_exclusive(x_61);
if (x_64 == 0)
{
return x_61;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_61, 0);
x_66 = lean_ctor_get(x_61, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_61);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; 
x_68 = lean_ctor_get(x_50, 0);
x_69 = lean_ctor_get(x_50, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_50);
x_70 = lean_box(0);
lean_inc(x_68);
x_71 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set(x_71, 1, x_70);
lean_ctor_set(x_71, 2, x_24);
x_72 = lean_box(0);
x_73 = lean_box(1);
lean_inc(x_68);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_68);
lean_ctor_set(x_74, 1, x_70);
x_75 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_75, 0, x_71);
lean_ctor_set(x_75, 1, x_43);
lean_ctor_set(x_75, 2, x_72);
lean_ctor_set(x_75, 3, x_74);
x_76 = lean_unbox(x_73);
lean_ctor_set_uint8(x_75, sizeof(void*)*4, x_76);
x_77 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_77, 0, x_75);
lean_inc(x_7);
lean_inc(x_6);
x_78 = l_Lean_addAndCompile(x_77, x_6, x_7, x_69);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
lean_dec(x_78);
x_80 = l_Lean_evalConst___at_____private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback_unsafe__1_spec__0___redArg(x_68, x_2, x_3, x_4, x_5, x_6, x_7, x_79);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_68);
return x_80;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_68);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_81 = lean_ctor_get(x_78, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_78, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_83 = x_78;
} else {
 lean_dec_ref(x_78);
 x_83 = lean_box(0);
}
if (lean_is_scalar(x_83)) {
 x_84 = lean_alloc_ctor(1, 2, 0);
} else {
 x_84 = x_83;
}
lean_ctor_set(x_84, 0, x_81);
lean_ctor_set(x_84, 1, x_82);
return x_84;
}
}
}
}
else
{
uint8_t x_85; 
lean_dec(x_24);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_85 = !lean_is_exclusive(x_42);
if (x_85 == 0)
{
return x_42;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_42, 0);
x_87 = lean_ctor_get(x_42, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_42);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; size_t x_105; lean_object* x_106; lean_object* x_107; size_t x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_89 = lean_ctor_get(x_1, 0);
lean_inc(x_89);
lean_dec(x_1);
x_90 = lean_mk_string_unchecked("Lean", 4, 4);
x_91 = lean_mk_string_unchecked("Meta", 4, 4);
x_92 = lean_mk_string_unchecked("Grind", 5, 5);
x_93 = lean_mk_string_unchecked("GoalM", 5, 5);
x_94 = l_Lean_Name_mkStr4(x_90, x_91, x_92, x_93);
x_95 = lean_box(0);
x_96 = l_Lean_Expr_const___override(x_94, x_95);
x_97 = lean_mk_string_unchecked("Unit", 4, 4);
x_98 = l_Lean_Name_mkStr1(x_97);
x_99 = l_Lean_Expr_const___override(x_98, x_95);
x_100 = l_Lean_Expr_app___override(x_96, x_99);
x_101 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_102 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_102, 0, x_101);
x_103 = lean_unsigned_to_nat(2u);
x_104 = lean_unsigned_to_nat(5u);
x_105 = lean_usize_of_nat(x_104);
x_106 = lean_usize_to_nat(x_105);
x_107 = lean_nat_pow(x_103, x_106);
lean_dec(x_106);
x_108 = lean_usize_of_nat(x_107);
lean_dec(x_107);
x_109 = lean_usize_to_nat(x_108);
x_110 = lean_mk_empty_array_with_capacity(x_109);
lean_dec(x_109);
lean_inc(x_110);
x_111 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_111, 0, x_110);
x_112 = lean_unsigned_to_nat(0u);
x_113 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_110);
lean_ctor_set(x_113, 2, x_112);
lean_ctor_set(x_113, 3, x_112);
lean_ctor_set_usize(x_113, 4, x_105);
x_114 = lean_box(0);
x_115 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_115, 0, x_102);
lean_ctor_set(x_115, 1, x_113);
lean_ctor_set(x_115, 2, x_114);
x_116 = l_Array_empty(lean_box(0));
lean_inc(x_100);
x_117 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_117, 0, x_100);
x_118 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermAndSynthesize___boxed), 9, 2);
lean_closure_set(x_118, 0, x_89);
lean_closure_set(x_118, 1, x_117);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
x_119 = l_Lean_Meta_withLCtx___at___Lean_Elab_Term_MVarErrorInfo_logError_spec__3___redArg(x_115, x_116, x_118, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
if (lean_obj_tag(x_120) == 4)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_100);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec(x_119);
x_122 = lean_ctor_get(x_120, 0);
lean_inc(x_122);
lean_dec(x_120);
x_123 = l_Lean_evalConst___at_____private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback_unsafe__1_spec__0___redArg(x_122, x_2, x_3, x_4, x_5, x_6, x_7, x_121);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_122);
return x_123;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; lean_object* x_138; lean_object* x_139; 
x_124 = lean_ctor_get(x_119, 1);
lean_inc(x_124);
lean_dec(x_119);
x_125 = lean_mk_string_unchecked("_grind_fallback", 15, 15);
x_126 = l_Lean_Name_mkStr1(x_125);
lean_inc(x_2);
x_127 = l_Lean_Elab_Term_mkAuxName(x_126, x_2, x_3, x_4, x_5, x_6, x_7, x_124);
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_130 = x_127;
} else {
 lean_dec_ref(x_127);
 x_130 = lean_box(0);
}
x_131 = lean_box(0);
lean_inc(x_128);
x_132 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_132, 0, x_128);
lean_ctor_set(x_132, 1, x_131);
lean_ctor_set(x_132, 2, x_100);
x_133 = lean_box(0);
x_134 = lean_box(1);
lean_inc(x_128);
if (lean_is_scalar(x_130)) {
 x_135 = lean_alloc_ctor(1, 2, 0);
} else {
 x_135 = x_130;
 lean_ctor_set_tag(x_135, 1);
}
lean_ctor_set(x_135, 0, x_128);
lean_ctor_set(x_135, 1, x_131);
x_136 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_136, 0, x_132);
lean_ctor_set(x_136, 1, x_120);
lean_ctor_set(x_136, 2, x_133);
lean_ctor_set(x_136, 3, x_135);
x_137 = lean_unbox(x_134);
lean_ctor_set_uint8(x_136, sizeof(void*)*4, x_137);
x_138 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_138, 0, x_136);
lean_inc(x_7);
lean_inc(x_6);
x_139 = l_Lean_addAndCompile(x_138, x_6, x_7, x_129);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; lean_object* x_141; 
x_140 = lean_ctor_get(x_139, 1);
lean_inc(x_140);
lean_dec(x_139);
x_141 = l_Lean_evalConst___at_____private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback_unsafe__1_spec__0___redArg(x_128, x_2, x_3, x_4, x_5, x_6, x_7, x_140);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_128);
return x_141;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec(x_128);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_142 = lean_ctor_get(x_139, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_139, 1);
lean_inc(x_143);
if (lean_is_exclusive(x_139)) {
 lean_ctor_release(x_139, 0);
 lean_ctor_release(x_139, 1);
 x_144 = x_139;
} else {
 lean_dec_ref(x_139);
 x_144 = lean_box(0);
}
if (lean_is_scalar(x_144)) {
 x_145 = lean_alloc_ctor(1, 2, 0);
} else {
 x_145 = x_144;
}
lean_ctor_set(x_145, 0, x_142);
lean_ctor_set(x_145, 1, x_143);
return x_145;
}
}
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
lean_dec(x_100);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_146 = lean_ctor_get(x_119, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_119, 1);
lean_inc(x_147);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_148 = x_119;
} else {
 lean_dec_ref(x_119);
 x_148 = lean_box(0);
}
if (lean_is_scalar(x_148)) {
 x_149 = lean_alloc_ctor(1, 2, 0);
} else {
 x_149 = x_148;
}
lean_ctor_set(x_149, 0, x_146);
lean_ctor_set(x_149, 1, x_147);
return x_149;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGrindCore___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Elab_Tactic_getMainGoal(x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_7);
x_18 = l_Lean_Elab_Tactic_grind(x_16, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_box(0);
x_22 = l_Lean_Elab_Tactic_replaceMainGoal___redArg(x_21, x_7, x_10, x_11, x_12, x_13, x_20);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
lean_ctor_set(x_22, 0, x_19);
return x_22;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_19);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_19);
x_27 = !lean_is_exclusive(x_22);
if (x_27 == 0)
{
return x_22;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_22, 0);
x_29 = lean_ctor_get(x_22, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_22);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
return x_18;
}
}
else
{
uint8_t x_31; 
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
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_15);
if (x_31 == 0)
{
return x_15;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_15, 0);
x_33 = lean_ctor_get(x_15, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_15);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGrindCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_9);
lean_inc(x_8);
x_15 = l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback(x_5, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_53; lean_object* x_54; uint8_t x_64; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_70; uint8_t x_71; 
x_70 = lean_box(0);
x_71 = lean_unbox(x_70);
x_64 = x_71;
goto block_69;
}
else
{
lean_object* x_72; uint8_t x_73; 
x_72 = lean_box(1);
x_73 = lean_unbox(x_72);
x_64 = x_73;
goto block_69;
}
block_33:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_box(x_19);
x_31 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalGrindCore___lam__0___boxed), 14, 5);
lean_closure_set(x_31, 0, x_2);
lean_closure_set(x_31, 1, x_30);
lean_closure_set(x_31, 2, x_18);
lean_closure_set(x_31, 3, x_29);
lean_closure_set(x_31, 4, x_16);
x_32 = l_Lean_Elab_Tactic_withMainContext___redArg(x_31, x_22, x_26, x_27, x_28, x_25, x_21, x_24, x_23, x_20);
return x_32;
}
block_52:
{
lean_object* x_45; lean_object* x_46; 
x_45 = l_Lean_Elab_Term_getDeclName_x3f___redArg(x_38, x_44);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_mk_string_unchecked("_grind", 6, 6);
x_49 = l_Lean_Name_mkStr1(x_48);
x_18 = x_34;
x_19 = x_35;
x_20 = x_47;
x_21 = x_41;
x_22 = x_36;
x_23 = x_43;
x_24 = x_42;
x_25 = x_40;
x_26 = x_37;
x_27 = x_38;
x_28 = x_39;
x_29 = x_49;
goto block_33;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_45, 1);
lean_inc(x_50);
lean_dec(x_45);
x_51 = lean_ctor_get(x_46, 0);
lean_inc(x_51);
lean_dec(x_46);
x_18 = x_34;
x_19 = x_35;
x_20 = x_50;
x_21 = x_41;
x_22 = x_36;
x_23 = x_43;
x_24 = x_42;
x_25 = x_40;
x_26 = x_37;
x_27 = x_38;
x_28 = x_39;
x_29 = x_51;
goto block_33;
}
}
block_63:
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_55 = lean_ctor_get(x_12, 2);
lean_inc(x_55);
x_56 = l_Lean_Meta_Grind_grind_warning;
x_57 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_55, x_56);
lean_dec(x_55);
if (x_57 == 0)
{
x_34 = x_54;
x_35 = x_53;
x_36 = x_6;
x_37 = x_7;
x_38 = x_8;
x_39 = x_9;
x_40 = x_10;
x_41 = x_11;
x_42 = x_12;
x_43 = x_13;
x_44 = x_17;
goto block_52;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_58 = lean_mk_string_unchecked("The `grind` tactic is experimental and still under development. Avoid using it in production projects.", 102, 102);
x_59 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_59, 0, x_58);
x_60 = l_Lean_MessageData_ofFormat(x_59);
lean_inc(x_12);
x_61 = l_Lean_logWarningAt___at___Lean_Linter_logLint___at___Lean_Linter_logLintIf___at___Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0_spec__0___redArg(x_1, x_60, x_10, x_11, x_12, x_13, x_17);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
lean_dec(x_61);
x_34 = x_54;
x_35 = x_53;
x_36 = x_6;
x_37 = x_7;
x_38 = x_8;
x_39 = x_9;
x_40 = x_10;
x_41 = x_11;
x_42 = x_12;
x_43 = x_13;
x_44 = x_62;
goto block_52;
}
}
block_69:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_unsigned_to_nat(0u);
x_66 = lean_mk_empty_array_with_capacity(x_65);
x_53 = x_64;
x_54 = x_66;
goto block_63;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_4, 0);
x_68 = l_Lean_Syntax_TSepArray_getElems___redArg(x_67);
x_53 = x_64;
x_54 = x_68;
goto block_63;
}
}
}
else
{
uint8_t x_74; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGrindCore___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_2);
lean_dec(x_2);
x_16 = l_Lean_Elab_Tactic_evalGrindCore___lam__0(x_1, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_10);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGrindCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Elab_Tactic_evalGrindCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_15;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_grindParamsPos() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(3u);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_grindOnlyPos() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(2u);
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_isGrindOnly(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
lean_inc(x_1);
x_2 = l_Lean_Syntax_getKind(x_1);
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Tactic", 6, 6);
x_6 = lean_mk_string_unchecked("grind", 5, 5);
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
x_9 = lean_unsigned_to_nat(2u);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_isGrindOnly___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Tactic_isGrindOnly(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_setGrindParams(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Array_isEmpty___redArg(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
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
x_16 = lean_mk_string_unchecked("null", 4, 4);
x_17 = l_Lean_Name_mkStr1(x_16);
x_18 = lean_box(2);
x_19 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
lean_ctor_set(x_19, 2, x_15);
x_20 = l_Lean_Syntax_setArg(x_1, x_11, x_19);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_21 = lean_unsigned_to_nat(3u);
x_22 = l_Array_empty(lean_box(0));
x_23 = lean_mk_string_unchecked("null", 4, 4);
x_24 = l_Lean_Name_mkStr1(x_23);
x_25 = lean_box(2);
x_26 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
lean_ctor_set(x_26, 2, x_22);
x_27 = l_Lean_Syntax_setArg(x_1, x_21, x_26);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_setGrindParams___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Tactic_setGrindParams(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getGrindParams(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_unsigned_to_nat(3u);
x_3 = l_Lean_Syntax_getArg(x_1, x_2);
x_4 = lean_unsigned_to_nat(1u);
x_5 = l_Lean_Syntax_getArg(x_3, x_4);
lean_dec(x_3);
x_6 = l_Lean_Syntax_getSepArgs(x_5);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getGrindParams___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Tactic_getGrindParams(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___Lean_PersistentHashSet_toList___at___Lean_Elab_Tactic_mkGrindOnly_spec__0_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___Lean_PersistentHashSet_toList___at___Lean_Elab_Tactic_mkGrindOnly_spec__0_spec__0___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_toList___at___Lean_PersistentHashSet_toList___at___Lean_Elab_Tactic_mkGrindOnly_spec__0_spec__0___redArg___lam__0), 3, 0);
x_3 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_beqEMatchTheoremTrace____x40_Lean_Meta_Tactic_Grind_Types___hyg_329____boxed), 2, 0);
x_4 = l_Lean_Meta_Grind_instHashableEMatchTheoremTrace;
x_5 = lean_box(0);
x_6 = l_Lean_PersistentHashMap_foldlM___at___Lean_PersistentHashMap_foldl_spec__0(lean_box(0), x_3, x_4, lean_box(0), lean_box(0), x_1, x_2, x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___Lean_PersistentHashSet_toList___at___Lean_Elab_Tactic_mkGrindOnly_spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PersistentHashMap_toList___at___Lean_PersistentHashSet_toList___at___Lean_Elab_Tactic_mkGrindOnly_spec__0_spec__0___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_PersistentHashSet_toList___at___Lean_Elab_Tactic_mkGrindOnly_spec__0_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_7);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_2);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_toList___at___Lean_Elab_Tactic_mkGrindOnly_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_PersistentHashMap_toList___at___Lean_PersistentHashSet_toList___at___Lean_Elab_Tactic_mkGrindOnly_spec__0_spec__0___redArg(x_1);
x_3 = lean_box(0);
x_4 = l_List_mapTR_loop___at___Lean_PersistentHashSet_toList___at___Lean_Elab_Tactic_mkGrindOnly_spec__0_spec__1(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Tactic_mkGrindOnly_spec__3_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_11 = x_1;
} else {
 lean_dec_ref(x_1);
 x_11 = lean_box(0);
}
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
x_13 = lean_ctor_get_uint8(x_9, sizeof(void*)*1);
lean_dec(x_9);
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_2, 1);
lean_inc(x_22);
lean_dec(x_2);
x_23 = lean_ctor_get(x_12, 0);
lean_inc(x_23);
lean_dec(x_12);
x_24 = lean_st_ref_get(x_6, x_7);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_ctor_get(x_24, 1);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
lean_dec(x_26);
lean_inc(x_23);
x_29 = l_Lean_Meta_Match_isMatchEqnTheorem(x_28, x_23);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_free_object(x_24);
x_30 = l_Lean_Meta_isEqnThm_x3f(x_23, x_5, x_6, x_27);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_30, 1);
x_34 = lean_ctor_get(x_30, 0);
lean_dec(x_34);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_35 = l_Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0(x_23, x_29, x_3, x_4, x_5, x_6, x_33);
if (lean_obj_tag(x_35) == 0)
{
switch (x_13) {
case 0:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
lean_free_object(x_30);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_st_ref_get(x_6, x_37);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_40 = lean_ctor_get(x_38, 1);
x_41 = lean_ctor_get(x_38, 0);
lean_dec(x_41);
x_42 = lean_ctor_get(x_5, 5);
lean_inc(x_42);
x_43 = l_Lean_SourceInfo_fromRef(x_42, x_29);
lean_dec(x_42);
x_44 = lean_mk_string_unchecked("Lean", 4, 4);
x_45 = lean_mk_string_unchecked("Parser", 6, 6);
x_46 = lean_mk_string_unchecked("Tactic", 6, 6);
x_47 = lean_mk_string_unchecked("grindParam", 10, 10);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
x_48 = l_Lean_Name_mkStr4(x_44, x_45, x_46, x_47);
x_49 = lean_mk_string_unchecked("grindLemma", 10, 10);
lean_inc(x_45);
lean_inc(x_44);
x_50 = l_Lean_Name_mkStr4(x_44, x_45, x_46, x_49);
x_51 = lean_mk_string_unchecked("null", 4, 4);
x_52 = l_Lean_Name_mkStr1(x_51);
x_53 = lean_mk_string_unchecked("Attr", 4, 4);
x_54 = lean_mk_string_unchecked("grindMod", 8, 8);
lean_inc(x_53);
lean_inc(x_45);
lean_inc(x_44);
x_55 = l_Lean_Name_mkStr4(x_44, x_45, x_53, x_54);
x_56 = lean_mk_string_unchecked("grindEq", 7, 7);
x_57 = l_Lean_Name_mkStr4(x_44, x_45, x_53, x_56);
x_58 = lean_mk_string_unchecked("=", 1, 1);
lean_inc(x_43);
lean_ctor_set_tag(x_38, 2);
lean_ctor_set(x_38, 1, x_58);
lean_ctor_set(x_38, 0, x_43);
lean_inc(x_43);
x_59 = l_Lean_Syntax_node1(x_43, x_57, x_38);
lean_inc(x_43);
x_60 = l_Lean_Syntax_node1(x_43, x_55, x_59);
lean_inc(x_43);
x_61 = l_Lean_Syntax_node1(x_43, x_52, x_60);
x_62 = lean_mk_syntax_ident(x_36);
lean_inc(x_43);
x_63 = l_Lean_Syntax_node2(x_43, x_50, x_61, x_62);
x_64 = l_Lean_Syntax_node1(x_43, x_48, x_63);
x_15 = x_22;
x_16 = x_64;
x_17 = x_40;
goto block_21;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_65 = lean_ctor_get(x_38, 1);
lean_inc(x_65);
lean_dec(x_38);
x_66 = lean_ctor_get(x_5, 5);
lean_inc(x_66);
x_67 = l_Lean_SourceInfo_fromRef(x_66, x_29);
lean_dec(x_66);
x_68 = lean_mk_string_unchecked("Lean", 4, 4);
x_69 = lean_mk_string_unchecked("Parser", 6, 6);
x_70 = lean_mk_string_unchecked("Tactic", 6, 6);
x_71 = lean_mk_string_unchecked("grindParam", 10, 10);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
x_72 = l_Lean_Name_mkStr4(x_68, x_69, x_70, x_71);
x_73 = lean_mk_string_unchecked("grindLemma", 10, 10);
lean_inc(x_69);
lean_inc(x_68);
x_74 = l_Lean_Name_mkStr4(x_68, x_69, x_70, x_73);
x_75 = lean_mk_string_unchecked("null", 4, 4);
x_76 = l_Lean_Name_mkStr1(x_75);
x_77 = lean_mk_string_unchecked("Attr", 4, 4);
x_78 = lean_mk_string_unchecked("grindMod", 8, 8);
lean_inc(x_77);
lean_inc(x_69);
lean_inc(x_68);
x_79 = l_Lean_Name_mkStr4(x_68, x_69, x_77, x_78);
x_80 = lean_mk_string_unchecked("grindEq", 7, 7);
x_81 = l_Lean_Name_mkStr4(x_68, x_69, x_77, x_80);
x_82 = lean_mk_string_unchecked("=", 1, 1);
lean_inc(x_67);
x_83 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_83, 0, x_67);
lean_ctor_set(x_83, 1, x_82);
lean_inc(x_67);
x_84 = l_Lean_Syntax_node1(x_67, x_81, x_83);
lean_inc(x_67);
x_85 = l_Lean_Syntax_node1(x_67, x_79, x_84);
lean_inc(x_67);
x_86 = l_Lean_Syntax_node1(x_67, x_76, x_85);
x_87 = lean_mk_syntax_ident(x_36);
lean_inc(x_67);
x_88 = l_Lean_Syntax_node2(x_67, x_74, x_86, x_87);
x_89 = l_Lean_Syntax_node1(x_67, x_72, x_88);
x_15 = x_22;
x_16 = x_89;
x_17 = x_65;
goto block_21;
}
}
case 1:
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_90 = lean_ctor_get(x_35, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_35, 1);
lean_inc(x_91);
lean_dec(x_35);
x_92 = lean_st_ref_get(x_6, x_91);
x_93 = !lean_is_exclusive(x_92);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_94 = lean_ctor_get(x_92, 1);
x_95 = lean_ctor_get(x_92, 0);
lean_dec(x_95);
x_96 = lean_ctor_get(x_5, 5);
lean_inc(x_96);
x_97 = l_Lean_SourceInfo_fromRef(x_96, x_29);
lean_dec(x_96);
x_98 = lean_mk_string_unchecked("Lean", 4, 4);
x_99 = lean_mk_string_unchecked("Parser", 6, 6);
x_100 = lean_mk_string_unchecked("Tactic", 6, 6);
x_101 = lean_mk_string_unchecked("grindParam", 10, 10);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
x_102 = l_Lean_Name_mkStr4(x_98, x_99, x_100, x_101);
x_103 = lean_mk_string_unchecked("grindLemma", 10, 10);
lean_inc(x_99);
lean_inc(x_98);
x_104 = l_Lean_Name_mkStr4(x_98, x_99, x_100, x_103);
x_105 = lean_mk_string_unchecked("null", 4, 4);
x_106 = l_Lean_Name_mkStr1(x_105);
x_107 = lean_mk_string_unchecked("Attr", 4, 4);
x_108 = lean_mk_string_unchecked("grindMod", 8, 8);
lean_inc(x_107);
lean_inc(x_99);
lean_inc(x_98);
x_109 = l_Lean_Name_mkStr4(x_98, x_99, x_107, x_108);
x_110 = lean_mk_string_unchecked("grindEqRhs", 10, 10);
x_111 = l_Lean_Name_mkStr4(x_98, x_99, x_107, x_110);
x_112 = lean_mk_string_unchecked("=", 1, 1);
lean_inc(x_97);
lean_ctor_set_tag(x_92, 2);
lean_ctor_set(x_92, 1, x_112);
lean_ctor_set(x_92, 0, x_97);
x_113 = lean_mk_string_unchecked("_", 1, 1);
lean_inc(x_97);
lean_ctor_set_tag(x_30, 2);
lean_ctor_set(x_30, 1, x_113);
lean_ctor_set(x_30, 0, x_97);
lean_inc(x_97);
x_114 = l_Lean_Syntax_node2(x_97, x_111, x_92, x_30);
lean_inc(x_97);
x_115 = l_Lean_Syntax_node1(x_97, x_109, x_114);
lean_inc(x_97);
x_116 = l_Lean_Syntax_node1(x_97, x_106, x_115);
x_117 = lean_mk_syntax_ident(x_90);
lean_inc(x_97);
x_118 = l_Lean_Syntax_node2(x_97, x_104, x_116, x_117);
x_119 = l_Lean_Syntax_node1(x_97, x_102, x_118);
x_15 = x_22;
x_16 = x_119;
x_17 = x_94;
goto block_21;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_120 = lean_ctor_get(x_92, 1);
lean_inc(x_120);
lean_dec(x_92);
x_121 = lean_ctor_get(x_5, 5);
lean_inc(x_121);
x_122 = l_Lean_SourceInfo_fromRef(x_121, x_29);
lean_dec(x_121);
x_123 = lean_mk_string_unchecked("Lean", 4, 4);
x_124 = lean_mk_string_unchecked("Parser", 6, 6);
x_125 = lean_mk_string_unchecked("Tactic", 6, 6);
x_126 = lean_mk_string_unchecked("grindParam", 10, 10);
lean_inc(x_125);
lean_inc(x_124);
lean_inc(x_123);
x_127 = l_Lean_Name_mkStr4(x_123, x_124, x_125, x_126);
x_128 = lean_mk_string_unchecked("grindLemma", 10, 10);
lean_inc(x_124);
lean_inc(x_123);
x_129 = l_Lean_Name_mkStr4(x_123, x_124, x_125, x_128);
x_130 = lean_mk_string_unchecked("null", 4, 4);
x_131 = l_Lean_Name_mkStr1(x_130);
x_132 = lean_mk_string_unchecked("Attr", 4, 4);
x_133 = lean_mk_string_unchecked("grindMod", 8, 8);
lean_inc(x_132);
lean_inc(x_124);
lean_inc(x_123);
x_134 = l_Lean_Name_mkStr4(x_123, x_124, x_132, x_133);
x_135 = lean_mk_string_unchecked("grindEqRhs", 10, 10);
x_136 = l_Lean_Name_mkStr4(x_123, x_124, x_132, x_135);
x_137 = lean_mk_string_unchecked("=", 1, 1);
lean_inc(x_122);
x_138 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_138, 0, x_122);
lean_ctor_set(x_138, 1, x_137);
x_139 = lean_mk_string_unchecked("_", 1, 1);
lean_inc(x_122);
lean_ctor_set_tag(x_30, 2);
lean_ctor_set(x_30, 1, x_139);
lean_ctor_set(x_30, 0, x_122);
lean_inc(x_122);
x_140 = l_Lean_Syntax_node2(x_122, x_136, x_138, x_30);
lean_inc(x_122);
x_141 = l_Lean_Syntax_node1(x_122, x_134, x_140);
lean_inc(x_122);
x_142 = l_Lean_Syntax_node1(x_122, x_131, x_141);
x_143 = lean_mk_syntax_ident(x_90);
lean_inc(x_122);
x_144 = l_Lean_Syntax_node2(x_122, x_129, x_142, x_143);
x_145 = l_Lean_Syntax_node1(x_122, x_127, x_144);
x_15 = x_22;
x_16 = x_145;
x_17 = x_120;
goto block_21;
}
}
case 2:
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; 
x_146 = lean_ctor_get(x_35, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_35, 1);
lean_inc(x_147);
lean_dec(x_35);
x_148 = lean_st_ref_get(x_6, x_147);
x_149 = !lean_is_exclusive(x_148);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_150 = lean_ctor_get(x_148, 1);
x_151 = lean_ctor_get(x_148, 0);
lean_dec(x_151);
x_152 = lean_ctor_get(x_5, 5);
lean_inc(x_152);
x_153 = l_Lean_SourceInfo_fromRef(x_152, x_29);
lean_dec(x_152);
x_154 = lean_mk_string_unchecked("Lean", 4, 4);
x_155 = lean_mk_string_unchecked("Parser", 6, 6);
x_156 = lean_mk_string_unchecked("Tactic", 6, 6);
x_157 = lean_mk_string_unchecked("grindParam", 10, 10);
lean_inc(x_156);
lean_inc(x_155);
lean_inc(x_154);
x_158 = l_Lean_Name_mkStr4(x_154, x_155, x_156, x_157);
x_159 = lean_mk_string_unchecked("grindLemma", 10, 10);
lean_inc(x_155);
lean_inc(x_154);
x_160 = l_Lean_Name_mkStr4(x_154, x_155, x_156, x_159);
x_161 = lean_mk_string_unchecked("null", 4, 4);
x_162 = l_Lean_Name_mkStr1(x_161);
x_163 = lean_mk_string_unchecked("Attr", 4, 4);
x_164 = lean_mk_string_unchecked("grindMod", 8, 8);
lean_inc(x_163);
lean_inc(x_155);
lean_inc(x_154);
x_165 = l_Lean_Name_mkStr4(x_154, x_155, x_163, x_164);
x_166 = lean_mk_string_unchecked("grindEqBoth", 11, 11);
x_167 = l_Lean_Name_mkStr4(x_154, x_155, x_163, x_166);
x_168 = lean_mk_string_unchecked("_", 1, 1);
lean_inc(x_153);
lean_ctor_set_tag(x_148, 2);
lean_ctor_set(x_148, 1, x_168);
lean_ctor_set(x_148, 0, x_153);
x_169 = lean_mk_string_unchecked("=", 1, 1);
lean_inc(x_153);
lean_ctor_set_tag(x_30, 2);
lean_ctor_set(x_30, 1, x_169);
lean_ctor_set(x_30, 0, x_153);
lean_inc(x_148);
lean_inc(x_153);
x_170 = l_Lean_Syntax_node3(x_153, x_167, x_148, x_30, x_148);
lean_inc(x_153);
x_171 = l_Lean_Syntax_node1(x_153, x_165, x_170);
lean_inc(x_153);
x_172 = l_Lean_Syntax_node1(x_153, x_162, x_171);
x_173 = lean_mk_syntax_ident(x_146);
lean_inc(x_153);
x_174 = l_Lean_Syntax_node2(x_153, x_160, x_172, x_173);
x_175 = l_Lean_Syntax_node1(x_153, x_158, x_174);
x_15 = x_22;
x_16 = x_175;
x_17 = x_150;
goto block_21;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_176 = lean_ctor_get(x_148, 1);
lean_inc(x_176);
lean_dec(x_148);
x_177 = lean_ctor_get(x_5, 5);
lean_inc(x_177);
x_178 = l_Lean_SourceInfo_fromRef(x_177, x_29);
lean_dec(x_177);
x_179 = lean_mk_string_unchecked("Lean", 4, 4);
x_180 = lean_mk_string_unchecked("Parser", 6, 6);
x_181 = lean_mk_string_unchecked("Tactic", 6, 6);
x_182 = lean_mk_string_unchecked("grindParam", 10, 10);
lean_inc(x_181);
lean_inc(x_180);
lean_inc(x_179);
x_183 = l_Lean_Name_mkStr4(x_179, x_180, x_181, x_182);
x_184 = lean_mk_string_unchecked("grindLemma", 10, 10);
lean_inc(x_180);
lean_inc(x_179);
x_185 = l_Lean_Name_mkStr4(x_179, x_180, x_181, x_184);
x_186 = lean_mk_string_unchecked("null", 4, 4);
x_187 = l_Lean_Name_mkStr1(x_186);
x_188 = lean_mk_string_unchecked("Attr", 4, 4);
x_189 = lean_mk_string_unchecked("grindMod", 8, 8);
lean_inc(x_188);
lean_inc(x_180);
lean_inc(x_179);
x_190 = l_Lean_Name_mkStr4(x_179, x_180, x_188, x_189);
x_191 = lean_mk_string_unchecked("grindEqBoth", 11, 11);
x_192 = l_Lean_Name_mkStr4(x_179, x_180, x_188, x_191);
x_193 = lean_mk_string_unchecked("_", 1, 1);
lean_inc(x_178);
x_194 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_194, 0, x_178);
lean_ctor_set(x_194, 1, x_193);
x_195 = lean_mk_string_unchecked("=", 1, 1);
lean_inc(x_178);
lean_ctor_set_tag(x_30, 2);
lean_ctor_set(x_30, 1, x_195);
lean_ctor_set(x_30, 0, x_178);
lean_inc(x_194);
lean_inc(x_178);
x_196 = l_Lean_Syntax_node3(x_178, x_192, x_194, x_30, x_194);
lean_inc(x_178);
x_197 = l_Lean_Syntax_node1(x_178, x_190, x_196);
lean_inc(x_178);
x_198 = l_Lean_Syntax_node1(x_178, x_187, x_197);
x_199 = lean_mk_syntax_ident(x_146);
lean_inc(x_178);
x_200 = l_Lean_Syntax_node2(x_178, x_185, x_198, x_199);
x_201 = l_Lean_Syntax_node1(x_178, x_183, x_200);
x_15 = x_22;
x_16 = x_201;
x_17 = x_176;
goto block_21;
}
}
case 3:
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; uint8_t x_205; 
x_202 = lean_ctor_get(x_35, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_35, 1);
lean_inc(x_203);
lean_dec(x_35);
x_204 = lean_st_ref_get(x_6, x_203);
x_205 = !lean_is_exclusive(x_204);
if (x_205 == 0)
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_206 = lean_ctor_get(x_204, 1);
x_207 = lean_ctor_get(x_204, 0);
lean_dec(x_207);
x_208 = lean_ctor_get(x_5, 5);
lean_inc(x_208);
x_209 = l_Lean_SourceInfo_fromRef(x_208, x_29);
lean_dec(x_208);
x_210 = lean_mk_string_unchecked("Lean", 4, 4);
x_211 = lean_mk_string_unchecked("Parser", 6, 6);
x_212 = lean_mk_string_unchecked("Tactic", 6, 6);
x_213 = lean_mk_string_unchecked("grindParam", 10, 10);
lean_inc(x_212);
lean_inc(x_211);
lean_inc(x_210);
x_214 = l_Lean_Name_mkStr4(x_210, x_211, x_212, x_213);
x_215 = lean_mk_string_unchecked("grindLemma", 10, 10);
lean_inc(x_211);
lean_inc(x_210);
x_216 = l_Lean_Name_mkStr4(x_210, x_211, x_212, x_215);
x_217 = lean_mk_string_unchecked("null", 4, 4);
x_218 = l_Lean_Name_mkStr1(x_217);
x_219 = lean_mk_string_unchecked("Attr", 4, 4);
x_220 = lean_mk_string_unchecked("grindMod", 8, 8);
lean_inc(x_219);
lean_inc(x_211);
lean_inc(x_210);
x_221 = l_Lean_Name_mkStr4(x_210, x_211, x_219, x_220);
x_222 = lean_mk_string_unchecked("grindEqBwd", 10, 10);
x_223 = l_Lean_Name_mkStr4(x_210, x_211, x_219, x_222);
x_224 = lean_mk_string_unchecked("group", 5, 5);
x_225 = l_Lean_Name_mkStr1(x_224);
x_226 = lean_mk_string_unchecked("←", 3, 1);
lean_inc(x_209);
lean_ctor_set_tag(x_204, 2);
lean_ctor_set(x_204, 1, x_226);
lean_ctor_set(x_204, 0, x_209);
x_227 = lean_mk_string_unchecked("=", 1, 1);
lean_inc(x_209);
lean_ctor_set_tag(x_30, 2);
lean_ctor_set(x_30, 1, x_227);
lean_ctor_set(x_30, 0, x_209);
lean_inc(x_209);
x_228 = l_Lean_Syntax_node2(x_209, x_225, x_204, x_30);
lean_inc(x_209);
x_229 = l_Lean_Syntax_node1(x_209, x_223, x_228);
lean_inc(x_209);
x_230 = l_Lean_Syntax_node1(x_209, x_221, x_229);
lean_inc(x_209);
x_231 = l_Lean_Syntax_node1(x_209, x_218, x_230);
x_232 = lean_mk_syntax_ident(x_202);
lean_inc(x_209);
x_233 = l_Lean_Syntax_node2(x_209, x_216, x_231, x_232);
x_234 = l_Lean_Syntax_node1(x_209, x_214, x_233);
x_15 = x_22;
x_16 = x_234;
x_17 = x_206;
goto block_21;
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
x_235 = lean_ctor_get(x_204, 1);
lean_inc(x_235);
lean_dec(x_204);
x_236 = lean_ctor_get(x_5, 5);
lean_inc(x_236);
x_237 = l_Lean_SourceInfo_fromRef(x_236, x_29);
lean_dec(x_236);
x_238 = lean_mk_string_unchecked("Lean", 4, 4);
x_239 = lean_mk_string_unchecked("Parser", 6, 6);
x_240 = lean_mk_string_unchecked("Tactic", 6, 6);
x_241 = lean_mk_string_unchecked("grindParam", 10, 10);
lean_inc(x_240);
lean_inc(x_239);
lean_inc(x_238);
x_242 = l_Lean_Name_mkStr4(x_238, x_239, x_240, x_241);
x_243 = lean_mk_string_unchecked("grindLemma", 10, 10);
lean_inc(x_239);
lean_inc(x_238);
x_244 = l_Lean_Name_mkStr4(x_238, x_239, x_240, x_243);
x_245 = lean_mk_string_unchecked("null", 4, 4);
x_246 = l_Lean_Name_mkStr1(x_245);
x_247 = lean_mk_string_unchecked("Attr", 4, 4);
x_248 = lean_mk_string_unchecked("grindMod", 8, 8);
lean_inc(x_247);
lean_inc(x_239);
lean_inc(x_238);
x_249 = l_Lean_Name_mkStr4(x_238, x_239, x_247, x_248);
x_250 = lean_mk_string_unchecked("grindEqBwd", 10, 10);
x_251 = l_Lean_Name_mkStr4(x_238, x_239, x_247, x_250);
x_252 = lean_mk_string_unchecked("group", 5, 5);
x_253 = l_Lean_Name_mkStr1(x_252);
x_254 = lean_mk_string_unchecked("←", 3, 1);
lean_inc(x_237);
x_255 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_255, 0, x_237);
lean_ctor_set(x_255, 1, x_254);
x_256 = lean_mk_string_unchecked("=", 1, 1);
lean_inc(x_237);
lean_ctor_set_tag(x_30, 2);
lean_ctor_set(x_30, 1, x_256);
lean_ctor_set(x_30, 0, x_237);
lean_inc(x_237);
x_257 = l_Lean_Syntax_node2(x_237, x_253, x_255, x_30);
lean_inc(x_237);
x_258 = l_Lean_Syntax_node1(x_237, x_251, x_257);
lean_inc(x_237);
x_259 = l_Lean_Syntax_node1(x_237, x_249, x_258);
lean_inc(x_237);
x_260 = l_Lean_Syntax_node1(x_237, x_246, x_259);
x_261 = lean_mk_syntax_ident(x_202);
lean_inc(x_237);
x_262 = l_Lean_Syntax_node2(x_237, x_244, x_260, x_261);
x_263 = l_Lean_Syntax_node1(x_237, x_242, x_262);
x_15 = x_22;
x_16 = x_263;
x_17 = x_235;
goto block_21;
}
}
case 4:
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; uint8_t x_267; 
lean_free_object(x_30);
x_264 = lean_ctor_get(x_35, 0);
lean_inc(x_264);
x_265 = lean_ctor_get(x_35, 1);
lean_inc(x_265);
lean_dec(x_35);
x_266 = lean_st_ref_get(x_6, x_265);
x_267 = !lean_is_exclusive(x_266);
if (x_267 == 0)
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; 
x_268 = lean_ctor_get(x_266, 1);
x_269 = lean_ctor_get(x_266, 0);
lean_dec(x_269);
x_270 = lean_ctor_get(x_5, 5);
lean_inc(x_270);
x_271 = l_Lean_SourceInfo_fromRef(x_270, x_29);
lean_dec(x_270);
x_272 = lean_mk_string_unchecked("Lean", 4, 4);
x_273 = lean_mk_string_unchecked("Parser", 6, 6);
x_274 = lean_mk_string_unchecked("Tactic", 6, 6);
x_275 = lean_mk_string_unchecked("grindParam", 10, 10);
lean_inc(x_274);
lean_inc(x_273);
lean_inc(x_272);
x_276 = l_Lean_Name_mkStr4(x_272, x_273, x_274, x_275);
x_277 = lean_mk_string_unchecked("grindLemma", 10, 10);
lean_inc(x_273);
lean_inc(x_272);
x_278 = l_Lean_Name_mkStr4(x_272, x_273, x_274, x_277);
x_279 = lean_mk_string_unchecked("null", 4, 4);
x_280 = l_Lean_Name_mkStr1(x_279);
x_281 = lean_mk_string_unchecked("Attr", 4, 4);
x_282 = lean_mk_string_unchecked("grindMod", 8, 8);
lean_inc(x_281);
lean_inc(x_273);
lean_inc(x_272);
x_283 = l_Lean_Name_mkStr4(x_272, x_273, x_281, x_282);
x_284 = lean_mk_string_unchecked("grindFwd", 8, 8);
x_285 = l_Lean_Name_mkStr4(x_272, x_273, x_281, x_284);
x_286 = lean_mk_string_unchecked("token", 5, 5);
x_287 = lean_mk_string_unchecked("→ ", 4, 2);
x_288 = l_Lean_Name_mkStr2(x_286, x_287);
x_289 = lean_mk_string_unchecked("→", 3, 1);
lean_inc(x_271);
lean_ctor_set_tag(x_266, 2);
lean_ctor_set(x_266, 1, x_289);
lean_ctor_set(x_266, 0, x_271);
lean_inc(x_271);
x_290 = l_Lean_Syntax_node1(x_271, x_288, x_266);
lean_inc(x_271);
x_291 = l_Lean_Syntax_node1(x_271, x_285, x_290);
lean_inc(x_271);
x_292 = l_Lean_Syntax_node1(x_271, x_283, x_291);
lean_inc(x_271);
x_293 = l_Lean_Syntax_node1(x_271, x_280, x_292);
x_294 = lean_mk_syntax_ident(x_264);
lean_inc(x_271);
x_295 = l_Lean_Syntax_node2(x_271, x_278, x_293, x_294);
x_296 = l_Lean_Syntax_node1(x_271, x_276, x_295);
x_15 = x_22;
x_16 = x_296;
x_17 = x_268;
goto block_21;
}
else
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; 
x_297 = lean_ctor_get(x_266, 1);
lean_inc(x_297);
lean_dec(x_266);
x_298 = lean_ctor_get(x_5, 5);
lean_inc(x_298);
x_299 = l_Lean_SourceInfo_fromRef(x_298, x_29);
lean_dec(x_298);
x_300 = lean_mk_string_unchecked("Lean", 4, 4);
x_301 = lean_mk_string_unchecked("Parser", 6, 6);
x_302 = lean_mk_string_unchecked("Tactic", 6, 6);
x_303 = lean_mk_string_unchecked("grindParam", 10, 10);
lean_inc(x_302);
lean_inc(x_301);
lean_inc(x_300);
x_304 = l_Lean_Name_mkStr4(x_300, x_301, x_302, x_303);
x_305 = lean_mk_string_unchecked("grindLemma", 10, 10);
lean_inc(x_301);
lean_inc(x_300);
x_306 = l_Lean_Name_mkStr4(x_300, x_301, x_302, x_305);
x_307 = lean_mk_string_unchecked("null", 4, 4);
x_308 = l_Lean_Name_mkStr1(x_307);
x_309 = lean_mk_string_unchecked("Attr", 4, 4);
x_310 = lean_mk_string_unchecked("grindMod", 8, 8);
lean_inc(x_309);
lean_inc(x_301);
lean_inc(x_300);
x_311 = l_Lean_Name_mkStr4(x_300, x_301, x_309, x_310);
x_312 = lean_mk_string_unchecked("grindFwd", 8, 8);
x_313 = l_Lean_Name_mkStr4(x_300, x_301, x_309, x_312);
x_314 = lean_mk_string_unchecked("token", 5, 5);
x_315 = lean_mk_string_unchecked("→ ", 4, 2);
x_316 = l_Lean_Name_mkStr2(x_314, x_315);
x_317 = lean_mk_string_unchecked("→", 3, 1);
lean_inc(x_299);
x_318 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_318, 0, x_299);
lean_ctor_set(x_318, 1, x_317);
lean_inc(x_299);
x_319 = l_Lean_Syntax_node1(x_299, x_316, x_318);
lean_inc(x_299);
x_320 = l_Lean_Syntax_node1(x_299, x_313, x_319);
lean_inc(x_299);
x_321 = l_Lean_Syntax_node1(x_299, x_311, x_320);
lean_inc(x_299);
x_322 = l_Lean_Syntax_node1(x_299, x_308, x_321);
x_323 = lean_mk_syntax_ident(x_264);
lean_inc(x_299);
x_324 = l_Lean_Syntax_node2(x_299, x_306, x_322, x_323);
x_325 = l_Lean_Syntax_node1(x_299, x_304, x_324);
x_15 = x_22;
x_16 = x_325;
x_17 = x_297;
goto block_21;
}
}
case 5:
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; uint8_t x_329; 
lean_free_object(x_30);
x_326 = lean_ctor_get(x_35, 0);
lean_inc(x_326);
x_327 = lean_ctor_get(x_35, 1);
lean_inc(x_327);
lean_dec(x_35);
x_328 = lean_st_ref_get(x_6, x_327);
x_329 = !lean_is_exclusive(x_328);
if (x_329 == 0)
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; 
x_330 = lean_ctor_get(x_328, 1);
x_331 = lean_ctor_get(x_328, 0);
lean_dec(x_331);
x_332 = lean_ctor_get(x_5, 5);
lean_inc(x_332);
x_333 = l_Lean_SourceInfo_fromRef(x_332, x_29);
lean_dec(x_332);
x_334 = lean_mk_string_unchecked("Lean", 4, 4);
x_335 = lean_mk_string_unchecked("Parser", 6, 6);
x_336 = lean_mk_string_unchecked("Tactic", 6, 6);
x_337 = lean_mk_string_unchecked("grindParam", 10, 10);
lean_inc(x_336);
lean_inc(x_335);
lean_inc(x_334);
x_338 = l_Lean_Name_mkStr4(x_334, x_335, x_336, x_337);
x_339 = lean_mk_string_unchecked("grindLemma", 10, 10);
lean_inc(x_335);
lean_inc(x_334);
x_340 = l_Lean_Name_mkStr4(x_334, x_335, x_336, x_339);
x_341 = lean_mk_string_unchecked("null", 4, 4);
x_342 = l_Lean_Name_mkStr1(x_341);
x_343 = lean_mk_string_unchecked("Attr", 4, 4);
x_344 = lean_mk_string_unchecked("grindMod", 8, 8);
lean_inc(x_343);
lean_inc(x_335);
lean_inc(x_334);
x_345 = l_Lean_Name_mkStr4(x_334, x_335, x_343, x_344);
x_346 = lean_mk_string_unchecked("grindBwd", 8, 8);
x_347 = l_Lean_Name_mkStr4(x_334, x_335, x_343, x_346);
x_348 = lean_mk_string_unchecked("token", 5, 5);
x_349 = lean_mk_string_unchecked("← ", 4, 2);
x_350 = l_Lean_Name_mkStr2(x_348, x_349);
x_351 = lean_mk_string_unchecked("←", 3, 1);
lean_inc(x_333);
lean_ctor_set_tag(x_328, 2);
lean_ctor_set(x_328, 1, x_351);
lean_ctor_set(x_328, 0, x_333);
lean_inc(x_333);
x_352 = l_Lean_Syntax_node1(x_333, x_350, x_328);
lean_inc(x_333);
x_353 = l_Lean_Syntax_node1(x_333, x_347, x_352);
lean_inc(x_333);
x_354 = l_Lean_Syntax_node1(x_333, x_345, x_353);
lean_inc(x_333);
x_355 = l_Lean_Syntax_node1(x_333, x_342, x_354);
x_356 = lean_mk_syntax_ident(x_326);
lean_inc(x_333);
x_357 = l_Lean_Syntax_node2(x_333, x_340, x_355, x_356);
x_358 = l_Lean_Syntax_node1(x_333, x_338, x_357);
x_15 = x_22;
x_16 = x_358;
x_17 = x_330;
goto block_21;
}
else
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; 
x_359 = lean_ctor_get(x_328, 1);
lean_inc(x_359);
lean_dec(x_328);
x_360 = lean_ctor_get(x_5, 5);
lean_inc(x_360);
x_361 = l_Lean_SourceInfo_fromRef(x_360, x_29);
lean_dec(x_360);
x_362 = lean_mk_string_unchecked("Lean", 4, 4);
x_363 = lean_mk_string_unchecked("Parser", 6, 6);
x_364 = lean_mk_string_unchecked("Tactic", 6, 6);
x_365 = lean_mk_string_unchecked("grindParam", 10, 10);
lean_inc(x_364);
lean_inc(x_363);
lean_inc(x_362);
x_366 = l_Lean_Name_mkStr4(x_362, x_363, x_364, x_365);
x_367 = lean_mk_string_unchecked("grindLemma", 10, 10);
lean_inc(x_363);
lean_inc(x_362);
x_368 = l_Lean_Name_mkStr4(x_362, x_363, x_364, x_367);
x_369 = lean_mk_string_unchecked("null", 4, 4);
x_370 = l_Lean_Name_mkStr1(x_369);
x_371 = lean_mk_string_unchecked("Attr", 4, 4);
x_372 = lean_mk_string_unchecked("grindMod", 8, 8);
lean_inc(x_371);
lean_inc(x_363);
lean_inc(x_362);
x_373 = l_Lean_Name_mkStr4(x_362, x_363, x_371, x_372);
x_374 = lean_mk_string_unchecked("grindBwd", 8, 8);
x_375 = l_Lean_Name_mkStr4(x_362, x_363, x_371, x_374);
x_376 = lean_mk_string_unchecked("token", 5, 5);
x_377 = lean_mk_string_unchecked("← ", 4, 2);
x_378 = l_Lean_Name_mkStr2(x_376, x_377);
x_379 = lean_mk_string_unchecked("←", 3, 1);
lean_inc(x_361);
x_380 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_380, 0, x_361);
lean_ctor_set(x_380, 1, x_379);
lean_inc(x_361);
x_381 = l_Lean_Syntax_node1(x_361, x_378, x_380);
lean_inc(x_361);
x_382 = l_Lean_Syntax_node1(x_361, x_375, x_381);
lean_inc(x_361);
x_383 = l_Lean_Syntax_node1(x_361, x_373, x_382);
lean_inc(x_361);
x_384 = l_Lean_Syntax_node1(x_361, x_370, x_383);
x_385 = lean_mk_syntax_ident(x_326);
lean_inc(x_361);
x_386 = l_Lean_Syntax_node2(x_361, x_368, x_384, x_385);
x_387 = l_Lean_Syntax_node1(x_361, x_366, x_386);
x_15 = x_22;
x_16 = x_387;
x_17 = x_359;
goto block_21;
}
}
case 6:
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; uint8_t x_391; 
lean_free_object(x_30);
x_388 = lean_ctor_get(x_35, 0);
lean_inc(x_388);
x_389 = lean_ctor_get(x_35, 1);
lean_inc(x_389);
lean_dec(x_35);
x_390 = lean_st_ref_get(x_6, x_389);
x_391 = !lean_is_exclusive(x_390);
if (x_391 == 0)
{
lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; 
x_392 = lean_ctor_get(x_390, 1);
x_393 = lean_ctor_get(x_390, 0);
lean_dec(x_393);
x_394 = lean_ctor_get(x_5, 5);
lean_inc(x_394);
x_395 = l_Lean_SourceInfo_fromRef(x_394, x_29);
lean_dec(x_394);
x_396 = lean_mk_string_unchecked("Lean", 4, 4);
x_397 = lean_mk_string_unchecked("Parser", 6, 6);
x_398 = lean_mk_string_unchecked("Tactic", 6, 6);
x_399 = lean_mk_string_unchecked("grindParam", 10, 10);
lean_inc(x_398);
lean_inc(x_397);
lean_inc(x_396);
x_400 = l_Lean_Name_mkStr4(x_396, x_397, x_398, x_399);
x_401 = lean_mk_string_unchecked("grindLemma", 10, 10);
lean_inc(x_397);
lean_inc(x_396);
x_402 = l_Lean_Name_mkStr4(x_396, x_397, x_398, x_401);
x_403 = lean_mk_string_unchecked("null", 4, 4);
x_404 = l_Lean_Name_mkStr1(x_403);
x_405 = lean_mk_string_unchecked("Attr", 4, 4);
x_406 = lean_mk_string_unchecked("grindMod", 8, 8);
lean_inc(x_405);
lean_inc(x_397);
lean_inc(x_396);
x_407 = l_Lean_Name_mkStr4(x_396, x_397, x_405, x_406);
x_408 = lean_mk_string_unchecked("grindLR", 7, 7);
x_409 = l_Lean_Name_mkStr4(x_396, x_397, x_405, x_408);
x_410 = lean_mk_string_unchecked("token", 5, 5);
x_411 = lean_mk_string_unchecked("=> ", 3, 3);
x_412 = l_Lean_Name_mkStr2(x_410, x_411);
x_413 = lean_mk_string_unchecked("=>", 2, 2);
lean_inc(x_395);
lean_ctor_set_tag(x_390, 2);
lean_ctor_set(x_390, 1, x_413);
lean_ctor_set(x_390, 0, x_395);
lean_inc(x_395);
x_414 = l_Lean_Syntax_node1(x_395, x_412, x_390);
lean_inc(x_395);
x_415 = l_Lean_Syntax_node1(x_395, x_409, x_414);
lean_inc(x_395);
x_416 = l_Lean_Syntax_node1(x_395, x_407, x_415);
lean_inc(x_395);
x_417 = l_Lean_Syntax_node1(x_395, x_404, x_416);
x_418 = lean_mk_syntax_ident(x_388);
lean_inc(x_395);
x_419 = l_Lean_Syntax_node2(x_395, x_402, x_417, x_418);
x_420 = l_Lean_Syntax_node1(x_395, x_400, x_419);
x_15 = x_22;
x_16 = x_420;
x_17 = x_392;
goto block_21;
}
else
{
lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; 
x_421 = lean_ctor_get(x_390, 1);
lean_inc(x_421);
lean_dec(x_390);
x_422 = lean_ctor_get(x_5, 5);
lean_inc(x_422);
x_423 = l_Lean_SourceInfo_fromRef(x_422, x_29);
lean_dec(x_422);
x_424 = lean_mk_string_unchecked("Lean", 4, 4);
x_425 = lean_mk_string_unchecked("Parser", 6, 6);
x_426 = lean_mk_string_unchecked("Tactic", 6, 6);
x_427 = lean_mk_string_unchecked("grindParam", 10, 10);
lean_inc(x_426);
lean_inc(x_425);
lean_inc(x_424);
x_428 = l_Lean_Name_mkStr4(x_424, x_425, x_426, x_427);
x_429 = lean_mk_string_unchecked("grindLemma", 10, 10);
lean_inc(x_425);
lean_inc(x_424);
x_430 = l_Lean_Name_mkStr4(x_424, x_425, x_426, x_429);
x_431 = lean_mk_string_unchecked("null", 4, 4);
x_432 = l_Lean_Name_mkStr1(x_431);
x_433 = lean_mk_string_unchecked("Attr", 4, 4);
x_434 = lean_mk_string_unchecked("grindMod", 8, 8);
lean_inc(x_433);
lean_inc(x_425);
lean_inc(x_424);
x_435 = l_Lean_Name_mkStr4(x_424, x_425, x_433, x_434);
x_436 = lean_mk_string_unchecked("grindLR", 7, 7);
x_437 = l_Lean_Name_mkStr4(x_424, x_425, x_433, x_436);
x_438 = lean_mk_string_unchecked("token", 5, 5);
x_439 = lean_mk_string_unchecked("=> ", 3, 3);
x_440 = l_Lean_Name_mkStr2(x_438, x_439);
x_441 = lean_mk_string_unchecked("=>", 2, 2);
lean_inc(x_423);
x_442 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_442, 0, x_423);
lean_ctor_set(x_442, 1, x_441);
lean_inc(x_423);
x_443 = l_Lean_Syntax_node1(x_423, x_440, x_442);
lean_inc(x_423);
x_444 = l_Lean_Syntax_node1(x_423, x_437, x_443);
lean_inc(x_423);
x_445 = l_Lean_Syntax_node1(x_423, x_435, x_444);
lean_inc(x_423);
x_446 = l_Lean_Syntax_node1(x_423, x_432, x_445);
x_447 = lean_mk_syntax_ident(x_388);
lean_inc(x_423);
x_448 = l_Lean_Syntax_node2(x_423, x_430, x_446, x_447);
x_449 = l_Lean_Syntax_node1(x_423, x_428, x_448);
x_15 = x_22;
x_16 = x_449;
x_17 = x_421;
goto block_21;
}
}
case 7:
{
lean_object* x_450; lean_object* x_451; lean_object* x_452; uint8_t x_453; 
lean_free_object(x_30);
x_450 = lean_ctor_get(x_35, 0);
lean_inc(x_450);
x_451 = lean_ctor_get(x_35, 1);
lean_inc(x_451);
lean_dec(x_35);
x_452 = lean_st_ref_get(x_6, x_451);
x_453 = !lean_is_exclusive(x_452);
if (x_453 == 0)
{
lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; 
x_454 = lean_ctor_get(x_452, 1);
x_455 = lean_ctor_get(x_452, 0);
lean_dec(x_455);
x_456 = lean_ctor_get(x_5, 5);
lean_inc(x_456);
x_457 = l_Lean_SourceInfo_fromRef(x_456, x_29);
lean_dec(x_456);
x_458 = lean_mk_string_unchecked("Lean", 4, 4);
x_459 = lean_mk_string_unchecked("Parser", 6, 6);
x_460 = lean_mk_string_unchecked("Tactic", 6, 6);
x_461 = lean_mk_string_unchecked("grindParam", 10, 10);
lean_inc(x_460);
lean_inc(x_459);
lean_inc(x_458);
x_462 = l_Lean_Name_mkStr4(x_458, x_459, x_460, x_461);
x_463 = lean_mk_string_unchecked("grindLemma", 10, 10);
lean_inc(x_459);
lean_inc(x_458);
x_464 = l_Lean_Name_mkStr4(x_458, x_459, x_460, x_463);
x_465 = lean_mk_string_unchecked("null", 4, 4);
x_466 = l_Lean_Name_mkStr1(x_465);
x_467 = lean_mk_string_unchecked("Attr", 4, 4);
x_468 = lean_mk_string_unchecked("grindMod", 8, 8);
lean_inc(x_467);
lean_inc(x_459);
lean_inc(x_458);
x_469 = l_Lean_Name_mkStr4(x_458, x_459, x_467, x_468);
x_470 = lean_mk_string_unchecked("grindRL", 7, 7);
x_471 = l_Lean_Name_mkStr4(x_458, x_459, x_467, x_470);
x_472 = lean_mk_string_unchecked("token", 5, 5);
x_473 = lean_mk_string_unchecked("<= ", 3, 3);
x_474 = l_Lean_Name_mkStr2(x_472, x_473);
x_475 = lean_mk_string_unchecked("<=", 2, 2);
lean_inc(x_457);
lean_ctor_set_tag(x_452, 2);
lean_ctor_set(x_452, 1, x_475);
lean_ctor_set(x_452, 0, x_457);
lean_inc(x_457);
x_476 = l_Lean_Syntax_node1(x_457, x_474, x_452);
lean_inc(x_457);
x_477 = l_Lean_Syntax_node1(x_457, x_471, x_476);
lean_inc(x_457);
x_478 = l_Lean_Syntax_node1(x_457, x_469, x_477);
lean_inc(x_457);
x_479 = l_Lean_Syntax_node1(x_457, x_466, x_478);
x_480 = lean_mk_syntax_ident(x_450);
lean_inc(x_457);
x_481 = l_Lean_Syntax_node2(x_457, x_464, x_479, x_480);
x_482 = l_Lean_Syntax_node1(x_457, x_462, x_481);
x_15 = x_22;
x_16 = x_482;
x_17 = x_454;
goto block_21;
}
else
{
lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; 
x_483 = lean_ctor_get(x_452, 1);
lean_inc(x_483);
lean_dec(x_452);
x_484 = lean_ctor_get(x_5, 5);
lean_inc(x_484);
x_485 = l_Lean_SourceInfo_fromRef(x_484, x_29);
lean_dec(x_484);
x_486 = lean_mk_string_unchecked("Lean", 4, 4);
x_487 = lean_mk_string_unchecked("Parser", 6, 6);
x_488 = lean_mk_string_unchecked("Tactic", 6, 6);
x_489 = lean_mk_string_unchecked("grindParam", 10, 10);
lean_inc(x_488);
lean_inc(x_487);
lean_inc(x_486);
x_490 = l_Lean_Name_mkStr4(x_486, x_487, x_488, x_489);
x_491 = lean_mk_string_unchecked("grindLemma", 10, 10);
lean_inc(x_487);
lean_inc(x_486);
x_492 = l_Lean_Name_mkStr4(x_486, x_487, x_488, x_491);
x_493 = lean_mk_string_unchecked("null", 4, 4);
x_494 = l_Lean_Name_mkStr1(x_493);
x_495 = lean_mk_string_unchecked("Attr", 4, 4);
x_496 = lean_mk_string_unchecked("grindMod", 8, 8);
lean_inc(x_495);
lean_inc(x_487);
lean_inc(x_486);
x_497 = l_Lean_Name_mkStr4(x_486, x_487, x_495, x_496);
x_498 = lean_mk_string_unchecked("grindRL", 7, 7);
x_499 = l_Lean_Name_mkStr4(x_486, x_487, x_495, x_498);
x_500 = lean_mk_string_unchecked("token", 5, 5);
x_501 = lean_mk_string_unchecked("<= ", 3, 3);
x_502 = l_Lean_Name_mkStr2(x_500, x_501);
x_503 = lean_mk_string_unchecked("<=", 2, 2);
lean_inc(x_485);
x_504 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_504, 0, x_485);
lean_ctor_set(x_504, 1, x_503);
lean_inc(x_485);
x_505 = l_Lean_Syntax_node1(x_485, x_502, x_504);
lean_inc(x_485);
x_506 = l_Lean_Syntax_node1(x_485, x_499, x_505);
lean_inc(x_485);
x_507 = l_Lean_Syntax_node1(x_485, x_497, x_506);
lean_inc(x_485);
x_508 = l_Lean_Syntax_node1(x_485, x_494, x_507);
x_509 = lean_mk_syntax_ident(x_450);
lean_inc(x_485);
x_510 = l_Lean_Syntax_node2(x_485, x_492, x_508, x_509);
x_511 = l_Lean_Syntax_node1(x_485, x_490, x_510);
x_15 = x_22;
x_16 = x_511;
x_17 = x_483;
goto block_21;
}
}
case 8:
{
lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; 
lean_free_object(x_30);
x_512 = lean_ctor_get(x_35, 0);
lean_inc(x_512);
x_513 = lean_ctor_get(x_35, 1);
lean_inc(x_513);
lean_dec(x_35);
x_514 = lean_st_ref_get(x_6, x_513);
x_515 = lean_ctor_get(x_514, 1);
lean_inc(x_515);
lean_dec(x_514);
x_516 = lean_ctor_get(x_5, 5);
lean_inc(x_516);
x_517 = l_Lean_SourceInfo_fromRef(x_516, x_29);
lean_dec(x_516);
x_518 = lean_mk_string_unchecked("Lean", 4, 4);
x_519 = lean_mk_string_unchecked("Parser", 6, 6);
x_520 = lean_mk_string_unchecked("Tactic", 6, 6);
x_521 = lean_mk_string_unchecked("grindParam", 10, 10);
lean_inc(x_520);
lean_inc(x_519);
lean_inc(x_518);
x_522 = l_Lean_Name_mkStr4(x_518, x_519, x_520, x_521);
x_523 = lean_mk_string_unchecked("grindLemma", 10, 10);
x_524 = l_Lean_Name_mkStr4(x_518, x_519, x_520, x_523);
x_525 = lean_mk_string_unchecked("null", 4, 4);
x_526 = l_Lean_Name_mkStr1(x_525);
x_527 = l_Array_mkArray0(lean_box(0));
lean_inc(x_517);
x_528 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_528, 0, x_517);
lean_ctor_set(x_528, 1, x_526);
lean_ctor_set(x_528, 2, x_527);
x_529 = lean_mk_syntax_ident(x_512);
lean_inc(x_517);
x_530 = l_Lean_Syntax_node2(x_517, x_524, x_528, x_529);
x_531 = l_Lean_Syntax_node1(x_517, x_522, x_530);
x_15 = x_22;
x_16 = x_531;
x_17 = x_515;
goto block_21;
}
default: 
{
lean_object* x_532; lean_object* x_533; lean_object* x_534; uint8_t x_535; 
lean_free_object(x_30);
x_532 = lean_ctor_get(x_35, 0);
lean_inc(x_532);
x_533 = lean_ctor_get(x_35, 1);
lean_inc(x_533);
lean_dec(x_35);
x_534 = lean_st_ref_get(x_6, x_533);
x_535 = !lean_is_exclusive(x_534);
if (x_535 == 0)
{
lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; 
x_536 = lean_ctor_get(x_534, 1);
x_537 = lean_ctor_get(x_534, 0);
lean_dec(x_537);
x_538 = lean_ctor_get(x_5, 5);
lean_inc(x_538);
x_539 = l_Lean_SourceInfo_fromRef(x_538, x_29);
lean_dec(x_538);
x_540 = lean_mk_string_unchecked("Lean", 4, 4);
x_541 = lean_mk_string_unchecked("Parser", 6, 6);
x_542 = lean_mk_string_unchecked("Tactic", 6, 6);
x_543 = lean_mk_string_unchecked("grindParam", 10, 10);
lean_inc(x_542);
lean_inc(x_541);
lean_inc(x_540);
x_544 = l_Lean_Name_mkStr4(x_540, x_541, x_542, x_543);
x_545 = lean_mk_string_unchecked("grindLemma", 10, 10);
lean_inc(x_541);
lean_inc(x_540);
x_546 = l_Lean_Name_mkStr4(x_540, x_541, x_542, x_545);
x_547 = lean_mk_string_unchecked("null", 4, 4);
x_548 = l_Lean_Name_mkStr1(x_547);
x_549 = lean_mk_string_unchecked("Attr", 4, 4);
x_550 = lean_mk_string_unchecked("grindMod", 8, 8);
lean_inc(x_549);
lean_inc(x_541);
lean_inc(x_540);
x_551 = l_Lean_Name_mkStr4(x_540, x_541, x_549, x_550);
x_552 = lean_mk_string_unchecked("grindUsr", 8, 8);
x_553 = l_Lean_Name_mkStr4(x_540, x_541, x_549, x_552);
x_554 = lean_mk_string_unchecked("usr", 3, 3);
lean_inc(x_539);
lean_ctor_set_tag(x_534, 2);
lean_ctor_set(x_534, 1, x_554);
lean_ctor_set(x_534, 0, x_539);
lean_inc(x_539);
x_555 = l_Lean_Syntax_node1(x_539, x_553, x_534);
lean_inc(x_539);
x_556 = l_Lean_Syntax_node1(x_539, x_551, x_555);
lean_inc(x_539);
x_557 = l_Lean_Syntax_node1(x_539, x_548, x_556);
x_558 = lean_mk_syntax_ident(x_532);
lean_inc(x_539);
x_559 = l_Lean_Syntax_node2(x_539, x_546, x_557, x_558);
x_560 = l_Lean_Syntax_node1(x_539, x_544, x_559);
x_15 = x_22;
x_16 = x_560;
x_17 = x_536;
goto block_21;
}
else
{
lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; 
x_561 = lean_ctor_get(x_534, 1);
lean_inc(x_561);
lean_dec(x_534);
x_562 = lean_ctor_get(x_5, 5);
lean_inc(x_562);
x_563 = l_Lean_SourceInfo_fromRef(x_562, x_29);
lean_dec(x_562);
x_564 = lean_mk_string_unchecked("Lean", 4, 4);
x_565 = lean_mk_string_unchecked("Parser", 6, 6);
x_566 = lean_mk_string_unchecked("Tactic", 6, 6);
x_567 = lean_mk_string_unchecked("grindParam", 10, 10);
lean_inc(x_566);
lean_inc(x_565);
lean_inc(x_564);
x_568 = l_Lean_Name_mkStr4(x_564, x_565, x_566, x_567);
x_569 = lean_mk_string_unchecked("grindLemma", 10, 10);
lean_inc(x_565);
lean_inc(x_564);
x_570 = l_Lean_Name_mkStr4(x_564, x_565, x_566, x_569);
x_571 = lean_mk_string_unchecked("null", 4, 4);
x_572 = l_Lean_Name_mkStr1(x_571);
x_573 = lean_mk_string_unchecked("Attr", 4, 4);
x_574 = lean_mk_string_unchecked("grindMod", 8, 8);
lean_inc(x_573);
lean_inc(x_565);
lean_inc(x_564);
x_575 = l_Lean_Name_mkStr4(x_564, x_565, x_573, x_574);
x_576 = lean_mk_string_unchecked("grindUsr", 8, 8);
x_577 = l_Lean_Name_mkStr4(x_564, x_565, x_573, x_576);
x_578 = lean_mk_string_unchecked("usr", 3, 3);
lean_inc(x_563);
x_579 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_579, 0, x_563);
lean_ctor_set(x_579, 1, x_578);
lean_inc(x_563);
x_580 = l_Lean_Syntax_node1(x_563, x_577, x_579);
lean_inc(x_563);
x_581 = l_Lean_Syntax_node1(x_563, x_575, x_580);
lean_inc(x_563);
x_582 = l_Lean_Syntax_node1(x_563, x_572, x_581);
x_583 = lean_mk_syntax_ident(x_532);
lean_inc(x_563);
x_584 = l_Lean_Syntax_node2(x_563, x_570, x_582, x_583);
x_585 = l_Lean_Syntax_node1(x_563, x_568, x_584);
x_15 = x_22;
x_16 = x_585;
x_17 = x_561;
goto block_21;
}
}
}
}
else
{
uint8_t x_586; 
lean_free_object(x_30);
lean_dec(x_22);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_586 = !lean_is_exclusive(x_35);
if (x_586 == 0)
{
return x_35;
}
else
{
lean_object* x_587; lean_object* x_588; lean_object* x_589; 
x_587 = lean_ctor_get(x_35, 0);
x_588 = lean_ctor_get(x_35, 1);
lean_inc(x_588);
lean_inc(x_587);
lean_dec(x_35);
x_589 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_589, 0, x_587);
lean_ctor_set(x_589, 1, x_588);
return x_589;
}
}
}
else
{
lean_object* x_590; lean_object* x_591; 
x_590 = lean_ctor_get(x_30, 1);
lean_inc(x_590);
lean_dec(x_30);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_591 = l_Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0(x_23, x_29, x_3, x_4, x_5, x_6, x_590);
if (lean_obj_tag(x_591) == 0)
{
switch (x_13) {
case 0:
{
lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; 
x_592 = lean_ctor_get(x_591, 0);
lean_inc(x_592);
x_593 = lean_ctor_get(x_591, 1);
lean_inc(x_593);
lean_dec(x_591);
x_594 = lean_st_ref_get(x_6, x_593);
x_595 = lean_ctor_get(x_594, 1);
lean_inc(x_595);
if (lean_is_exclusive(x_594)) {
 lean_ctor_release(x_594, 0);
 lean_ctor_release(x_594, 1);
 x_596 = x_594;
} else {
 lean_dec_ref(x_594);
 x_596 = lean_box(0);
}
x_597 = lean_ctor_get(x_5, 5);
lean_inc(x_597);
x_598 = l_Lean_SourceInfo_fromRef(x_597, x_29);
lean_dec(x_597);
x_599 = lean_mk_string_unchecked("Lean", 4, 4);
x_600 = lean_mk_string_unchecked("Parser", 6, 6);
x_601 = lean_mk_string_unchecked("Tactic", 6, 6);
x_602 = lean_mk_string_unchecked("grindParam", 10, 10);
lean_inc(x_601);
lean_inc(x_600);
lean_inc(x_599);
x_603 = l_Lean_Name_mkStr4(x_599, x_600, x_601, x_602);
x_604 = lean_mk_string_unchecked("grindLemma", 10, 10);
lean_inc(x_600);
lean_inc(x_599);
x_605 = l_Lean_Name_mkStr4(x_599, x_600, x_601, x_604);
x_606 = lean_mk_string_unchecked("null", 4, 4);
x_607 = l_Lean_Name_mkStr1(x_606);
x_608 = lean_mk_string_unchecked("Attr", 4, 4);
x_609 = lean_mk_string_unchecked("grindMod", 8, 8);
lean_inc(x_608);
lean_inc(x_600);
lean_inc(x_599);
x_610 = l_Lean_Name_mkStr4(x_599, x_600, x_608, x_609);
x_611 = lean_mk_string_unchecked("grindEq", 7, 7);
x_612 = l_Lean_Name_mkStr4(x_599, x_600, x_608, x_611);
x_613 = lean_mk_string_unchecked("=", 1, 1);
lean_inc(x_598);
if (lean_is_scalar(x_596)) {
 x_614 = lean_alloc_ctor(2, 2, 0);
} else {
 x_614 = x_596;
 lean_ctor_set_tag(x_614, 2);
}
lean_ctor_set(x_614, 0, x_598);
lean_ctor_set(x_614, 1, x_613);
lean_inc(x_598);
x_615 = l_Lean_Syntax_node1(x_598, x_612, x_614);
lean_inc(x_598);
x_616 = l_Lean_Syntax_node1(x_598, x_610, x_615);
lean_inc(x_598);
x_617 = l_Lean_Syntax_node1(x_598, x_607, x_616);
x_618 = lean_mk_syntax_ident(x_592);
lean_inc(x_598);
x_619 = l_Lean_Syntax_node2(x_598, x_605, x_617, x_618);
x_620 = l_Lean_Syntax_node1(x_598, x_603, x_619);
x_15 = x_22;
x_16 = x_620;
x_17 = x_595;
goto block_21;
}
case 1:
{
lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; 
x_621 = lean_ctor_get(x_591, 0);
lean_inc(x_621);
x_622 = lean_ctor_get(x_591, 1);
lean_inc(x_622);
lean_dec(x_591);
x_623 = lean_st_ref_get(x_6, x_622);
x_624 = lean_ctor_get(x_623, 1);
lean_inc(x_624);
if (lean_is_exclusive(x_623)) {
 lean_ctor_release(x_623, 0);
 lean_ctor_release(x_623, 1);
 x_625 = x_623;
} else {
 lean_dec_ref(x_623);
 x_625 = lean_box(0);
}
x_626 = lean_ctor_get(x_5, 5);
lean_inc(x_626);
x_627 = l_Lean_SourceInfo_fromRef(x_626, x_29);
lean_dec(x_626);
x_628 = lean_mk_string_unchecked("Lean", 4, 4);
x_629 = lean_mk_string_unchecked("Parser", 6, 6);
x_630 = lean_mk_string_unchecked("Tactic", 6, 6);
x_631 = lean_mk_string_unchecked("grindParam", 10, 10);
lean_inc(x_630);
lean_inc(x_629);
lean_inc(x_628);
x_632 = l_Lean_Name_mkStr4(x_628, x_629, x_630, x_631);
x_633 = lean_mk_string_unchecked("grindLemma", 10, 10);
lean_inc(x_629);
lean_inc(x_628);
x_634 = l_Lean_Name_mkStr4(x_628, x_629, x_630, x_633);
x_635 = lean_mk_string_unchecked("null", 4, 4);
x_636 = l_Lean_Name_mkStr1(x_635);
x_637 = lean_mk_string_unchecked("Attr", 4, 4);
x_638 = lean_mk_string_unchecked("grindMod", 8, 8);
lean_inc(x_637);
lean_inc(x_629);
lean_inc(x_628);
x_639 = l_Lean_Name_mkStr4(x_628, x_629, x_637, x_638);
x_640 = lean_mk_string_unchecked("grindEqRhs", 10, 10);
x_641 = l_Lean_Name_mkStr4(x_628, x_629, x_637, x_640);
x_642 = lean_mk_string_unchecked("=", 1, 1);
lean_inc(x_627);
if (lean_is_scalar(x_625)) {
 x_643 = lean_alloc_ctor(2, 2, 0);
} else {
 x_643 = x_625;
 lean_ctor_set_tag(x_643, 2);
}
lean_ctor_set(x_643, 0, x_627);
lean_ctor_set(x_643, 1, x_642);
x_644 = lean_mk_string_unchecked("_", 1, 1);
lean_inc(x_627);
x_645 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_645, 0, x_627);
lean_ctor_set(x_645, 1, x_644);
lean_inc(x_627);
x_646 = l_Lean_Syntax_node2(x_627, x_641, x_643, x_645);
lean_inc(x_627);
x_647 = l_Lean_Syntax_node1(x_627, x_639, x_646);
lean_inc(x_627);
x_648 = l_Lean_Syntax_node1(x_627, x_636, x_647);
x_649 = lean_mk_syntax_ident(x_621);
lean_inc(x_627);
x_650 = l_Lean_Syntax_node2(x_627, x_634, x_648, x_649);
x_651 = l_Lean_Syntax_node1(x_627, x_632, x_650);
x_15 = x_22;
x_16 = x_651;
x_17 = x_624;
goto block_21;
}
case 2:
{
lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; 
x_652 = lean_ctor_get(x_591, 0);
lean_inc(x_652);
x_653 = lean_ctor_get(x_591, 1);
lean_inc(x_653);
lean_dec(x_591);
x_654 = lean_st_ref_get(x_6, x_653);
x_655 = lean_ctor_get(x_654, 1);
lean_inc(x_655);
if (lean_is_exclusive(x_654)) {
 lean_ctor_release(x_654, 0);
 lean_ctor_release(x_654, 1);
 x_656 = x_654;
} else {
 lean_dec_ref(x_654);
 x_656 = lean_box(0);
}
x_657 = lean_ctor_get(x_5, 5);
lean_inc(x_657);
x_658 = l_Lean_SourceInfo_fromRef(x_657, x_29);
lean_dec(x_657);
x_659 = lean_mk_string_unchecked("Lean", 4, 4);
x_660 = lean_mk_string_unchecked("Parser", 6, 6);
x_661 = lean_mk_string_unchecked("Tactic", 6, 6);
x_662 = lean_mk_string_unchecked("grindParam", 10, 10);
lean_inc(x_661);
lean_inc(x_660);
lean_inc(x_659);
x_663 = l_Lean_Name_mkStr4(x_659, x_660, x_661, x_662);
x_664 = lean_mk_string_unchecked("grindLemma", 10, 10);
lean_inc(x_660);
lean_inc(x_659);
x_665 = l_Lean_Name_mkStr4(x_659, x_660, x_661, x_664);
x_666 = lean_mk_string_unchecked("null", 4, 4);
x_667 = l_Lean_Name_mkStr1(x_666);
x_668 = lean_mk_string_unchecked("Attr", 4, 4);
x_669 = lean_mk_string_unchecked("grindMod", 8, 8);
lean_inc(x_668);
lean_inc(x_660);
lean_inc(x_659);
x_670 = l_Lean_Name_mkStr4(x_659, x_660, x_668, x_669);
x_671 = lean_mk_string_unchecked("grindEqBoth", 11, 11);
x_672 = l_Lean_Name_mkStr4(x_659, x_660, x_668, x_671);
x_673 = lean_mk_string_unchecked("_", 1, 1);
lean_inc(x_658);
if (lean_is_scalar(x_656)) {
 x_674 = lean_alloc_ctor(2, 2, 0);
} else {
 x_674 = x_656;
 lean_ctor_set_tag(x_674, 2);
}
lean_ctor_set(x_674, 0, x_658);
lean_ctor_set(x_674, 1, x_673);
x_675 = lean_mk_string_unchecked("=", 1, 1);
lean_inc(x_658);
x_676 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_676, 0, x_658);
lean_ctor_set(x_676, 1, x_675);
lean_inc(x_674);
lean_inc(x_658);
x_677 = l_Lean_Syntax_node3(x_658, x_672, x_674, x_676, x_674);
lean_inc(x_658);
x_678 = l_Lean_Syntax_node1(x_658, x_670, x_677);
lean_inc(x_658);
x_679 = l_Lean_Syntax_node1(x_658, x_667, x_678);
x_680 = lean_mk_syntax_ident(x_652);
lean_inc(x_658);
x_681 = l_Lean_Syntax_node2(x_658, x_665, x_679, x_680);
x_682 = l_Lean_Syntax_node1(x_658, x_663, x_681);
x_15 = x_22;
x_16 = x_682;
x_17 = x_655;
goto block_21;
}
case 3:
{
lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; 
x_683 = lean_ctor_get(x_591, 0);
lean_inc(x_683);
x_684 = lean_ctor_get(x_591, 1);
lean_inc(x_684);
lean_dec(x_591);
x_685 = lean_st_ref_get(x_6, x_684);
x_686 = lean_ctor_get(x_685, 1);
lean_inc(x_686);
if (lean_is_exclusive(x_685)) {
 lean_ctor_release(x_685, 0);
 lean_ctor_release(x_685, 1);
 x_687 = x_685;
} else {
 lean_dec_ref(x_685);
 x_687 = lean_box(0);
}
x_688 = lean_ctor_get(x_5, 5);
lean_inc(x_688);
x_689 = l_Lean_SourceInfo_fromRef(x_688, x_29);
lean_dec(x_688);
x_690 = lean_mk_string_unchecked("Lean", 4, 4);
x_691 = lean_mk_string_unchecked("Parser", 6, 6);
x_692 = lean_mk_string_unchecked("Tactic", 6, 6);
x_693 = lean_mk_string_unchecked("grindParam", 10, 10);
lean_inc(x_692);
lean_inc(x_691);
lean_inc(x_690);
x_694 = l_Lean_Name_mkStr4(x_690, x_691, x_692, x_693);
x_695 = lean_mk_string_unchecked("grindLemma", 10, 10);
lean_inc(x_691);
lean_inc(x_690);
x_696 = l_Lean_Name_mkStr4(x_690, x_691, x_692, x_695);
x_697 = lean_mk_string_unchecked("null", 4, 4);
x_698 = l_Lean_Name_mkStr1(x_697);
x_699 = lean_mk_string_unchecked("Attr", 4, 4);
x_700 = lean_mk_string_unchecked("grindMod", 8, 8);
lean_inc(x_699);
lean_inc(x_691);
lean_inc(x_690);
x_701 = l_Lean_Name_mkStr4(x_690, x_691, x_699, x_700);
x_702 = lean_mk_string_unchecked("grindEqBwd", 10, 10);
x_703 = l_Lean_Name_mkStr4(x_690, x_691, x_699, x_702);
x_704 = lean_mk_string_unchecked("group", 5, 5);
x_705 = l_Lean_Name_mkStr1(x_704);
x_706 = lean_mk_string_unchecked("←", 3, 1);
lean_inc(x_689);
if (lean_is_scalar(x_687)) {
 x_707 = lean_alloc_ctor(2, 2, 0);
} else {
 x_707 = x_687;
 lean_ctor_set_tag(x_707, 2);
}
lean_ctor_set(x_707, 0, x_689);
lean_ctor_set(x_707, 1, x_706);
x_708 = lean_mk_string_unchecked("=", 1, 1);
lean_inc(x_689);
x_709 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_709, 0, x_689);
lean_ctor_set(x_709, 1, x_708);
lean_inc(x_689);
x_710 = l_Lean_Syntax_node2(x_689, x_705, x_707, x_709);
lean_inc(x_689);
x_711 = l_Lean_Syntax_node1(x_689, x_703, x_710);
lean_inc(x_689);
x_712 = l_Lean_Syntax_node1(x_689, x_701, x_711);
lean_inc(x_689);
x_713 = l_Lean_Syntax_node1(x_689, x_698, x_712);
x_714 = lean_mk_syntax_ident(x_683);
lean_inc(x_689);
x_715 = l_Lean_Syntax_node2(x_689, x_696, x_713, x_714);
x_716 = l_Lean_Syntax_node1(x_689, x_694, x_715);
x_15 = x_22;
x_16 = x_716;
x_17 = x_686;
goto block_21;
}
case 4:
{
lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; 
x_717 = lean_ctor_get(x_591, 0);
lean_inc(x_717);
x_718 = lean_ctor_get(x_591, 1);
lean_inc(x_718);
lean_dec(x_591);
x_719 = lean_st_ref_get(x_6, x_718);
x_720 = lean_ctor_get(x_719, 1);
lean_inc(x_720);
if (lean_is_exclusive(x_719)) {
 lean_ctor_release(x_719, 0);
 lean_ctor_release(x_719, 1);
 x_721 = x_719;
} else {
 lean_dec_ref(x_719);
 x_721 = lean_box(0);
}
x_722 = lean_ctor_get(x_5, 5);
lean_inc(x_722);
x_723 = l_Lean_SourceInfo_fromRef(x_722, x_29);
lean_dec(x_722);
x_724 = lean_mk_string_unchecked("Lean", 4, 4);
x_725 = lean_mk_string_unchecked("Parser", 6, 6);
x_726 = lean_mk_string_unchecked("Tactic", 6, 6);
x_727 = lean_mk_string_unchecked("grindParam", 10, 10);
lean_inc(x_726);
lean_inc(x_725);
lean_inc(x_724);
x_728 = l_Lean_Name_mkStr4(x_724, x_725, x_726, x_727);
x_729 = lean_mk_string_unchecked("grindLemma", 10, 10);
lean_inc(x_725);
lean_inc(x_724);
x_730 = l_Lean_Name_mkStr4(x_724, x_725, x_726, x_729);
x_731 = lean_mk_string_unchecked("null", 4, 4);
x_732 = l_Lean_Name_mkStr1(x_731);
x_733 = lean_mk_string_unchecked("Attr", 4, 4);
x_734 = lean_mk_string_unchecked("grindMod", 8, 8);
lean_inc(x_733);
lean_inc(x_725);
lean_inc(x_724);
x_735 = l_Lean_Name_mkStr4(x_724, x_725, x_733, x_734);
x_736 = lean_mk_string_unchecked("grindFwd", 8, 8);
x_737 = l_Lean_Name_mkStr4(x_724, x_725, x_733, x_736);
x_738 = lean_mk_string_unchecked("token", 5, 5);
x_739 = lean_mk_string_unchecked("→ ", 4, 2);
x_740 = l_Lean_Name_mkStr2(x_738, x_739);
x_741 = lean_mk_string_unchecked("→", 3, 1);
lean_inc(x_723);
if (lean_is_scalar(x_721)) {
 x_742 = lean_alloc_ctor(2, 2, 0);
} else {
 x_742 = x_721;
 lean_ctor_set_tag(x_742, 2);
}
lean_ctor_set(x_742, 0, x_723);
lean_ctor_set(x_742, 1, x_741);
lean_inc(x_723);
x_743 = l_Lean_Syntax_node1(x_723, x_740, x_742);
lean_inc(x_723);
x_744 = l_Lean_Syntax_node1(x_723, x_737, x_743);
lean_inc(x_723);
x_745 = l_Lean_Syntax_node1(x_723, x_735, x_744);
lean_inc(x_723);
x_746 = l_Lean_Syntax_node1(x_723, x_732, x_745);
x_747 = lean_mk_syntax_ident(x_717);
lean_inc(x_723);
x_748 = l_Lean_Syntax_node2(x_723, x_730, x_746, x_747);
x_749 = l_Lean_Syntax_node1(x_723, x_728, x_748);
x_15 = x_22;
x_16 = x_749;
x_17 = x_720;
goto block_21;
}
case 5:
{
lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; 
x_750 = lean_ctor_get(x_591, 0);
lean_inc(x_750);
x_751 = lean_ctor_get(x_591, 1);
lean_inc(x_751);
lean_dec(x_591);
x_752 = lean_st_ref_get(x_6, x_751);
x_753 = lean_ctor_get(x_752, 1);
lean_inc(x_753);
if (lean_is_exclusive(x_752)) {
 lean_ctor_release(x_752, 0);
 lean_ctor_release(x_752, 1);
 x_754 = x_752;
} else {
 lean_dec_ref(x_752);
 x_754 = lean_box(0);
}
x_755 = lean_ctor_get(x_5, 5);
lean_inc(x_755);
x_756 = l_Lean_SourceInfo_fromRef(x_755, x_29);
lean_dec(x_755);
x_757 = lean_mk_string_unchecked("Lean", 4, 4);
x_758 = lean_mk_string_unchecked("Parser", 6, 6);
x_759 = lean_mk_string_unchecked("Tactic", 6, 6);
x_760 = lean_mk_string_unchecked("grindParam", 10, 10);
lean_inc(x_759);
lean_inc(x_758);
lean_inc(x_757);
x_761 = l_Lean_Name_mkStr4(x_757, x_758, x_759, x_760);
x_762 = lean_mk_string_unchecked("grindLemma", 10, 10);
lean_inc(x_758);
lean_inc(x_757);
x_763 = l_Lean_Name_mkStr4(x_757, x_758, x_759, x_762);
x_764 = lean_mk_string_unchecked("null", 4, 4);
x_765 = l_Lean_Name_mkStr1(x_764);
x_766 = lean_mk_string_unchecked("Attr", 4, 4);
x_767 = lean_mk_string_unchecked("grindMod", 8, 8);
lean_inc(x_766);
lean_inc(x_758);
lean_inc(x_757);
x_768 = l_Lean_Name_mkStr4(x_757, x_758, x_766, x_767);
x_769 = lean_mk_string_unchecked("grindBwd", 8, 8);
x_770 = l_Lean_Name_mkStr4(x_757, x_758, x_766, x_769);
x_771 = lean_mk_string_unchecked("token", 5, 5);
x_772 = lean_mk_string_unchecked("← ", 4, 2);
x_773 = l_Lean_Name_mkStr2(x_771, x_772);
x_774 = lean_mk_string_unchecked("←", 3, 1);
lean_inc(x_756);
if (lean_is_scalar(x_754)) {
 x_775 = lean_alloc_ctor(2, 2, 0);
} else {
 x_775 = x_754;
 lean_ctor_set_tag(x_775, 2);
}
lean_ctor_set(x_775, 0, x_756);
lean_ctor_set(x_775, 1, x_774);
lean_inc(x_756);
x_776 = l_Lean_Syntax_node1(x_756, x_773, x_775);
lean_inc(x_756);
x_777 = l_Lean_Syntax_node1(x_756, x_770, x_776);
lean_inc(x_756);
x_778 = l_Lean_Syntax_node1(x_756, x_768, x_777);
lean_inc(x_756);
x_779 = l_Lean_Syntax_node1(x_756, x_765, x_778);
x_780 = lean_mk_syntax_ident(x_750);
lean_inc(x_756);
x_781 = l_Lean_Syntax_node2(x_756, x_763, x_779, x_780);
x_782 = l_Lean_Syntax_node1(x_756, x_761, x_781);
x_15 = x_22;
x_16 = x_782;
x_17 = x_753;
goto block_21;
}
case 6:
{
lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; lean_object* x_815; 
x_783 = lean_ctor_get(x_591, 0);
lean_inc(x_783);
x_784 = lean_ctor_get(x_591, 1);
lean_inc(x_784);
lean_dec(x_591);
x_785 = lean_st_ref_get(x_6, x_784);
x_786 = lean_ctor_get(x_785, 1);
lean_inc(x_786);
if (lean_is_exclusive(x_785)) {
 lean_ctor_release(x_785, 0);
 lean_ctor_release(x_785, 1);
 x_787 = x_785;
} else {
 lean_dec_ref(x_785);
 x_787 = lean_box(0);
}
x_788 = lean_ctor_get(x_5, 5);
lean_inc(x_788);
x_789 = l_Lean_SourceInfo_fromRef(x_788, x_29);
lean_dec(x_788);
x_790 = lean_mk_string_unchecked("Lean", 4, 4);
x_791 = lean_mk_string_unchecked("Parser", 6, 6);
x_792 = lean_mk_string_unchecked("Tactic", 6, 6);
x_793 = lean_mk_string_unchecked("grindParam", 10, 10);
lean_inc(x_792);
lean_inc(x_791);
lean_inc(x_790);
x_794 = l_Lean_Name_mkStr4(x_790, x_791, x_792, x_793);
x_795 = lean_mk_string_unchecked("grindLemma", 10, 10);
lean_inc(x_791);
lean_inc(x_790);
x_796 = l_Lean_Name_mkStr4(x_790, x_791, x_792, x_795);
x_797 = lean_mk_string_unchecked("null", 4, 4);
x_798 = l_Lean_Name_mkStr1(x_797);
x_799 = lean_mk_string_unchecked("Attr", 4, 4);
x_800 = lean_mk_string_unchecked("grindMod", 8, 8);
lean_inc(x_799);
lean_inc(x_791);
lean_inc(x_790);
x_801 = l_Lean_Name_mkStr4(x_790, x_791, x_799, x_800);
x_802 = lean_mk_string_unchecked("grindLR", 7, 7);
x_803 = l_Lean_Name_mkStr4(x_790, x_791, x_799, x_802);
x_804 = lean_mk_string_unchecked("token", 5, 5);
x_805 = lean_mk_string_unchecked("=> ", 3, 3);
x_806 = l_Lean_Name_mkStr2(x_804, x_805);
x_807 = lean_mk_string_unchecked("=>", 2, 2);
lean_inc(x_789);
if (lean_is_scalar(x_787)) {
 x_808 = lean_alloc_ctor(2, 2, 0);
} else {
 x_808 = x_787;
 lean_ctor_set_tag(x_808, 2);
}
lean_ctor_set(x_808, 0, x_789);
lean_ctor_set(x_808, 1, x_807);
lean_inc(x_789);
x_809 = l_Lean_Syntax_node1(x_789, x_806, x_808);
lean_inc(x_789);
x_810 = l_Lean_Syntax_node1(x_789, x_803, x_809);
lean_inc(x_789);
x_811 = l_Lean_Syntax_node1(x_789, x_801, x_810);
lean_inc(x_789);
x_812 = l_Lean_Syntax_node1(x_789, x_798, x_811);
x_813 = lean_mk_syntax_ident(x_783);
lean_inc(x_789);
x_814 = l_Lean_Syntax_node2(x_789, x_796, x_812, x_813);
x_815 = l_Lean_Syntax_node1(x_789, x_794, x_814);
x_15 = x_22;
x_16 = x_815;
x_17 = x_786;
goto block_21;
}
case 7:
{
lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; lean_object* x_822; lean_object* x_823; lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; lean_object* x_834; lean_object* x_835; lean_object* x_836; lean_object* x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; lean_object* x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; 
x_816 = lean_ctor_get(x_591, 0);
lean_inc(x_816);
x_817 = lean_ctor_get(x_591, 1);
lean_inc(x_817);
lean_dec(x_591);
x_818 = lean_st_ref_get(x_6, x_817);
x_819 = lean_ctor_get(x_818, 1);
lean_inc(x_819);
if (lean_is_exclusive(x_818)) {
 lean_ctor_release(x_818, 0);
 lean_ctor_release(x_818, 1);
 x_820 = x_818;
} else {
 lean_dec_ref(x_818);
 x_820 = lean_box(0);
}
x_821 = lean_ctor_get(x_5, 5);
lean_inc(x_821);
x_822 = l_Lean_SourceInfo_fromRef(x_821, x_29);
lean_dec(x_821);
x_823 = lean_mk_string_unchecked("Lean", 4, 4);
x_824 = lean_mk_string_unchecked("Parser", 6, 6);
x_825 = lean_mk_string_unchecked("Tactic", 6, 6);
x_826 = lean_mk_string_unchecked("grindParam", 10, 10);
lean_inc(x_825);
lean_inc(x_824);
lean_inc(x_823);
x_827 = l_Lean_Name_mkStr4(x_823, x_824, x_825, x_826);
x_828 = lean_mk_string_unchecked("grindLemma", 10, 10);
lean_inc(x_824);
lean_inc(x_823);
x_829 = l_Lean_Name_mkStr4(x_823, x_824, x_825, x_828);
x_830 = lean_mk_string_unchecked("null", 4, 4);
x_831 = l_Lean_Name_mkStr1(x_830);
x_832 = lean_mk_string_unchecked("Attr", 4, 4);
x_833 = lean_mk_string_unchecked("grindMod", 8, 8);
lean_inc(x_832);
lean_inc(x_824);
lean_inc(x_823);
x_834 = l_Lean_Name_mkStr4(x_823, x_824, x_832, x_833);
x_835 = lean_mk_string_unchecked("grindRL", 7, 7);
x_836 = l_Lean_Name_mkStr4(x_823, x_824, x_832, x_835);
x_837 = lean_mk_string_unchecked("token", 5, 5);
x_838 = lean_mk_string_unchecked("<= ", 3, 3);
x_839 = l_Lean_Name_mkStr2(x_837, x_838);
x_840 = lean_mk_string_unchecked("<=", 2, 2);
lean_inc(x_822);
if (lean_is_scalar(x_820)) {
 x_841 = lean_alloc_ctor(2, 2, 0);
} else {
 x_841 = x_820;
 lean_ctor_set_tag(x_841, 2);
}
lean_ctor_set(x_841, 0, x_822);
lean_ctor_set(x_841, 1, x_840);
lean_inc(x_822);
x_842 = l_Lean_Syntax_node1(x_822, x_839, x_841);
lean_inc(x_822);
x_843 = l_Lean_Syntax_node1(x_822, x_836, x_842);
lean_inc(x_822);
x_844 = l_Lean_Syntax_node1(x_822, x_834, x_843);
lean_inc(x_822);
x_845 = l_Lean_Syntax_node1(x_822, x_831, x_844);
x_846 = lean_mk_syntax_ident(x_816);
lean_inc(x_822);
x_847 = l_Lean_Syntax_node2(x_822, x_829, x_845, x_846);
x_848 = l_Lean_Syntax_node1(x_822, x_827, x_847);
x_15 = x_22;
x_16 = x_848;
x_17 = x_819;
goto block_21;
}
case 8:
{
lean_object* x_849; lean_object* x_850; lean_object* x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; lean_object* x_864; lean_object* x_865; lean_object* x_866; lean_object* x_867; lean_object* x_868; 
x_849 = lean_ctor_get(x_591, 0);
lean_inc(x_849);
x_850 = lean_ctor_get(x_591, 1);
lean_inc(x_850);
lean_dec(x_591);
x_851 = lean_st_ref_get(x_6, x_850);
x_852 = lean_ctor_get(x_851, 1);
lean_inc(x_852);
lean_dec(x_851);
x_853 = lean_ctor_get(x_5, 5);
lean_inc(x_853);
x_854 = l_Lean_SourceInfo_fromRef(x_853, x_29);
lean_dec(x_853);
x_855 = lean_mk_string_unchecked("Lean", 4, 4);
x_856 = lean_mk_string_unchecked("Parser", 6, 6);
x_857 = lean_mk_string_unchecked("Tactic", 6, 6);
x_858 = lean_mk_string_unchecked("grindParam", 10, 10);
lean_inc(x_857);
lean_inc(x_856);
lean_inc(x_855);
x_859 = l_Lean_Name_mkStr4(x_855, x_856, x_857, x_858);
x_860 = lean_mk_string_unchecked("grindLemma", 10, 10);
x_861 = l_Lean_Name_mkStr4(x_855, x_856, x_857, x_860);
x_862 = lean_mk_string_unchecked("null", 4, 4);
x_863 = l_Lean_Name_mkStr1(x_862);
x_864 = l_Array_mkArray0(lean_box(0));
lean_inc(x_854);
x_865 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_865, 0, x_854);
lean_ctor_set(x_865, 1, x_863);
lean_ctor_set(x_865, 2, x_864);
x_866 = lean_mk_syntax_ident(x_849);
lean_inc(x_854);
x_867 = l_Lean_Syntax_node2(x_854, x_861, x_865, x_866);
x_868 = l_Lean_Syntax_node1(x_854, x_859, x_867);
x_15 = x_22;
x_16 = x_868;
x_17 = x_852;
goto block_21;
}
default: 
{
lean_object* x_869; lean_object* x_870; lean_object* x_871; lean_object* x_872; lean_object* x_873; lean_object* x_874; lean_object* x_875; lean_object* x_876; lean_object* x_877; lean_object* x_878; lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; lean_object* x_884; lean_object* x_885; lean_object* x_886; lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; lean_object* x_891; lean_object* x_892; lean_object* x_893; lean_object* x_894; lean_object* x_895; lean_object* x_896; lean_object* x_897; 
x_869 = lean_ctor_get(x_591, 0);
lean_inc(x_869);
x_870 = lean_ctor_get(x_591, 1);
lean_inc(x_870);
lean_dec(x_591);
x_871 = lean_st_ref_get(x_6, x_870);
x_872 = lean_ctor_get(x_871, 1);
lean_inc(x_872);
if (lean_is_exclusive(x_871)) {
 lean_ctor_release(x_871, 0);
 lean_ctor_release(x_871, 1);
 x_873 = x_871;
} else {
 lean_dec_ref(x_871);
 x_873 = lean_box(0);
}
x_874 = lean_ctor_get(x_5, 5);
lean_inc(x_874);
x_875 = l_Lean_SourceInfo_fromRef(x_874, x_29);
lean_dec(x_874);
x_876 = lean_mk_string_unchecked("Lean", 4, 4);
x_877 = lean_mk_string_unchecked("Parser", 6, 6);
x_878 = lean_mk_string_unchecked("Tactic", 6, 6);
x_879 = lean_mk_string_unchecked("grindParam", 10, 10);
lean_inc(x_878);
lean_inc(x_877);
lean_inc(x_876);
x_880 = l_Lean_Name_mkStr4(x_876, x_877, x_878, x_879);
x_881 = lean_mk_string_unchecked("grindLemma", 10, 10);
lean_inc(x_877);
lean_inc(x_876);
x_882 = l_Lean_Name_mkStr4(x_876, x_877, x_878, x_881);
x_883 = lean_mk_string_unchecked("null", 4, 4);
x_884 = l_Lean_Name_mkStr1(x_883);
x_885 = lean_mk_string_unchecked("Attr", 4, 4);
x_886 = lean_mk_string_unchecked("grindMod", 8, 8);
lean_inc(x_885);
lean_inc(x_877);
lean_inc(x_876);
x_887 = l_Lean_Name_mkStr4(x_876, x_877, x_885, x_886);
x_888 = lean_mk_string_unchecked("grindUsr", 8, 8);
x_889 = l_Lean_Name_mkStr4(x_876, x_877, x_885, x_888);
x_890 = lean_mk_string_unchecked("usr", 3, 3);
lean_inc(x_875);
if (lean_is_scalar(x_873)) {
 x_891 = lean_alloc_ctor(2, 2, 0);
} else {
 x_891 = x_873;
 lean_ctor_set_tag(x_891, 2);
}
lean_ctor_set(x_891, 0, x_875);
lean_ctor_set(x_891, 1, x_890);
lean_inc(x_875);
x_892 = l_Lean_Syntax_node1(x_875, x_889, x_891);
lean_inc(x_875);
x_893 = l_Lean_Syntax_node1(x_875, x_887, x_892);
lean_inc(x_875);
x_894 = l_Lean_Syntax_node1(x_875, x_884, x_893);
x_895 = lean_mk_syntax_ident(x_869);
lean_inc(x_875);
x_896 = l_Lean_Syntax_node2(x_875, x_882, x_894, x_895);
x_897 = l_Lean_Syntax_node1(x_875, x_880, x_896);
x_15 = x_22;
x_16 = x_897;
x_17 = x_872;
goto block_21;
}
}
}
else
{
lean_object* x_898; lean_object* x_899; lean_object* x_900; lean_object* x_901; 
lean_dec(x_22);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_898 = lean_ctor_get(x_591, 0);
lean_inc(x_898);
x_899 = lean_ctor_get(x_591, 1);
lean_inc(x_899);
if (lean_is_exclusive(x_591)) {
 lean_ctor_release(x_591, 0);
 lean_ctor_release(x_591, 1);
 x_900 = x_591;
} else {
 lean_dec_ref(x_591);
 x_900 = lean_box(0);
}
if (lean_is_scalar(x_900)) {
 x_901 = lean_alloc_ctor(1, 2, 0);
} else {
 x_901 = x_900;
}
lean_ctor_set(x_901, 0, x_898);
lean_ctor_set(x_901, 1, x_899);
return x_901;
}
}
}
else
{
uint8_t x_902; 
lean_dec(x_23);
lean_dec(x_11);
x_902 = !lean_is_exclusive(x_30);
if (x_902 == 0)
{
lean_object* x_903; lean_object* x_904; lean_object* x_905; uint8_t x_906; 
x_903 = lean_ctor_get(x_30, 1);
x_904 = lean_ctor_get(x_30, 0);
lean_dec(x_904);
x_905 = lean_ctor_get(x_31, 0);
lean_inc(x_905);
lean_dec(x_31);
x_906 = l_Lean_NameSet_contains(x_14, x_905);
if (x_906 == 0)
{
lean_object* x_907; 
lean_free_object(x_30);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_905);
x_907 = l_Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0(x_905, x_906, x_3, x_4, x_5, x_6, x_903);
if (lean_obj_tag(x_907) == 0)
{
lean_object* x_908; lean_object* x_909; lean_object* x_910; uint8_t x_911; 
x_908 = lean_ctor_get(x_907, 0);
lean_inc(x_908);
x_909 = lean_ctor_get(x_907, 1);
lean_inc(x_909);
lean_dec(x_907);
x_910 = lean_st_ref_get(x_6, x_909);
x_911 = !lean_is_exclusive(x_910);
if (x_911 == 0)
{
lean_object* x_912; lean_object* x_913; lean_object* x_914; lean_object* x_915; lean_object* x_916; lean_object* x_917; lean_object* x_918; lean_object* x_919; lean_object* x_920; lean_object* x_921; lean_object* x_922; lean_object* x_923; lean_object* x_924; lean_object* x_925; lean_object* x_926; lean_object* x_927; lean_object* x_928; lean_object* x_929; lean_object* x_930; lean_object* x_931; 
x_912 = lean_ctor_get(x_910, 1);
x_913 = lean_ctor_get(x_910, 0);
lean_dec(x_913);
x_914 = lean_ctor_get(x_5, 5);
lean_inc(x_914);
x_915 = l_Lean_NameSet_insert(x_14, x_905);
x_916 = l_Lean_SourceInfo_fromRef(x_914, x_906);
lean_dec(x_914);
x_917 = lean_mk_string_unchecked("Lean", 4, 4);
x_918 = lean_mk_string_unchecked("Parser", 6, 6);
x_919 = lean_mk_string_unchecked("Tactic", 6, 6);
x_920 = lean_mk_string_unchecked("grindParam", 10, 10);
lean_inc(x_919);
lean_inc(x_918);
lean_inc(x_917);
x_921 = l_Lean_Name_mkStr4(x_917, x_918, x_919, x_920);
x_922 = lean_mk_string_unchecked("grindLemma", 10, 10);
x_923 = l_Lean_Name_mkStr4(x_917, x_918, x_919, x_922);
x_924 = lean_mk_string_unchecked("null", 4, 4);
x_925 = l_Lean_Name_mkStr1(x_924);
x_926 = l_Array_mkArray0(lean_box(0));
lean_inc(x_916);
x_927 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_927, 0, x_916);
lean_ctor_set(x_927, 1, x_925);
lean_ctor_set(x_927, 2, x_926);
x_928 = lean_mk_syntax_ident(x_908);
lean_inc(x_916);
x_929 = l_Lean_Syntax_node2(x_916, x_923, x_927, x_928);
x_930 = l_Lean_Syntax_node1(x_916, x_921, x_929);
x_931 = lean_array_push(x_22, x_930);
lean_ctor_set(x_910, 1, x_931);
lean_ctor_set(x_910, 0, x_915);
x_1 = x_10;
x_2 = x_910;
x_7 = x_912;
goto _start;
}
else
{
lean_object* x_933; lean_object* x_934; lean_object* x_935; lean_object* x_936; lean_object* x_937; lean_object* x_938; lean_object* x_939; lean_object* x_940; lean_object* x_941; lean_object* x_942; lean_object* x_943; lean_object* x_944; lean_object* x_945; lean_object* x_946; lean_object* x_947; lean_object* x_948; lean_object* x_949; lean_object* x_950; lean_object* x_951; lean_object* x_952; 
x_933 = lean_ctor_get(x_910, 1);
lean_inc(x_933);
lean_dec(x_910);
x_934 = lean_ctor_get(x_5, 5);
lean_inc(x_934);
x_935 = l_Lean_NameSet_insert(x_14, x_905);
x_936 = l_Lean_SourceInfo_fromRef(x_934, x_906);
lean_dec(x_934);
x_937 = lean_mk_string_unchecked("Lean", 4, 4);
x_938 = lean_mk_string_unchecked("Parser", 6, 6);
x_939 = lean_mk_string_unchecked("Tactic", 6, 6);
x_940 = lean_mk_string_unchecked("grindParam", 10, 10);
lean_inc(x_939);
lean_inc(x_938);
lean_inc(x_937);
x_941 = l_Lean_Name_mkStr4(x_937, x_938, x_939, x_940);
x_942 = lean_mk_string_unchecked("grindLemma", 10, 10);
x_943 = l_Lean_Name_mkStr4(x_937, x_938, x_939, x_942);
x_944 = lean_mk_string_unchecked("null", 4, 4);
x_945 = l_Lean_Name_mkStr1(x_944);
x_946 = l_Array_mkArray0(lean_box(0));
lean_inc(x_936);
x_947 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_947, 0, x_936);
lean_ctor_set(x_947, 1, x_945);
lean_ctor_set(x_947, 2, x_946);
x_948 = lean_mk_syntax_ident(x_908);
lean_inc(x_936);
x_949 = l_Lean_Syntax_node2(x_936, x_943, x_947, x_948);
x_950 = l_Lean_Syntax_node1(x_936, x_941, x_949);
x_951 = lean_array_push(x_22, x_950);
x_952 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_952, 0, x_935);
lean_ctor_set(x_952, 1, x_951);
x_1 = x_10;
x_2 = x_952;
x_7 = x_933;
goto _start;
}
}
else
{
uint8_t x_954; 
lean_dec(x_905);
lean_dec(x_22);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_954 = !lean_is_exclusive(x_907);
if (x_954 == 0)
{
return x_907;
}
else
{
lean_object* x_955; lean_object* x_956; lean_object* x_957; 
x_955 = lean_ctor_get(x_907, 0);
x_956 = lean_ctor_get(x_907, 1);
lean_inc(x_956);
lean_inc(x_955);
lean_dec(x_907);
x_957 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_957, 0, x_955);
lean_ctor_set(x_957, 1, x_956);
return x_957;
}
}
}
else
{
lean_dec(x_905);
lean_ctor_set(x_30, 1, x_22);
lean_ctor_set(x_30, 0, x_14);
x_1 = x_10;
x_2 = x_30;
x_7 = x_903;
goto _start;
}
}
else
{
lean_object* x_959; lean_object* x_960; uint8_t x_961; 
x_959 = lean_ctor_get(x_30, 1);
lean_inc(x_959);
lean_dec(x_30);
x_960 = lean_ctor_get(x_31, 0);
lean_inc(x_960);
lean_dec(x_31);
x_961 = l_Lean_NameSet_contains(x_14, x_960);
if (x_961 == 0)
{
lean_object* x_962; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_960);
x_962 = l_Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0(x_960, x_961, x_3, x_4, x_5, x_6, x_959);
if (lean_obj_tag(x_962) == 0)
{
lean_object* x_963; lean_object* x_964; lean_object* x_965; lean_object* x_966; lean_object* x_967; lean_object* x_968; lean_object* x_969; lean_object* x_970; lean_object* x_971; lean_object* x_972; lean_object* x_973; lean_object* x_974; lean_object* x_975; lean_object* x_976; lean_object* x_977; lean_object* x_978; lean_object* x_979; lean_object* x_980; lean_object* x_981; lean_object* x_982; lean_object* x_983; lean_object* x_984; lean_object* x_985; lean_object* x_986; 
x_963 = lean_ctor_get(x_962, 0);
lean_inc(x_963);
x_964 = lean_ctor_get(x_962, 1);
lean_inc(x_964);
lean_dec(x_962);
x_965 = lean_st_ref_get(x_6, x_964);
x_966 = lean_ctor_get(x_965, 1);
lean_inc(x_966);
if (lean_is_exclusive(x_965)) {
 lean_ctor_release(x_965, 0);
 lean_ctor_release(x_965, 1);
 x_967 = x_965;
} else {
 lean_dec_ref(x_965);
 x_967 = lean_box(0);
}
x_968 = lean_ctor_get(x_5, 5);
lean_inc(x_968);
x_969 = l_Lean_NameSet_insert(x_14, x_960);
x_970 = l_Lean_SourceInfo_fromRef(x_968, x_961);
lean_dec(x_968);
x_971 = lean_mk_string_unchecked("Lean", 4, 4);
x_972 = lean_mk_string_unchecked("Parser", 6, 6);
x_973 = lean_mk_string_unchecked("Tactic", 6, 6);
x_974 = lean_mk_string_unchecked("grindParam", 10, 10);
lean_inc(x_973);
lean_inc(x_972);
lean_inc(x_971);
x_975 = l_Lean_Name_mkStr4(x_971, x_972, x_973, x_974);
x_976 = lean_mk_string_unchecked("grindLemma", 10, 10);
x_977 = l_Lean_Name_mkStr4(x_971, x_972, x_973, x_976);
x_978 = lean_mk_string_unchecked("null", 4, 4);
x_979 = l_Lean_Name_mkStr1(x_978);
x_980 = l_Array_mkArray0(lean_box(0));
lean_inc(x_970);
x_981 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_981, 0, x_970);
lean_ctor_set(x_981, 1, x_979);
lean_ctor_set(x_981, 2, x_980);
x_982 = lean_mk_syntax_ident(x_963);
lean_inc(x_970);
x_983 = l_Lean_Syntax_node2(x_970, x_977, x_981, x_982);
x_984 = l_Lean_Syntax_node1(x_970, x_975, x_983);
x_985 = lean_array_push(x_22, x_984);
if (lean_is_scalar(x_967)) {
 x_986 = lean_alloc_ctor(0, 2, 0);
} else {
 x_986 = x_967;
}
lean_ctor_set(x_986, 0, x_969);
lean_ctor_set(x_986, 1, x_985);
x_1 = x_10;
x_2 = x_986;
x_7 = x_966;
goto _start;
}
else
{
lean_object* x_988; lean_object* x_989; lean_object* x_990; lean_object* x_991; 
lean_dec(x_960);
lean_dec(x_22);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_988 = lean_ctor_get(x_962, 0);
lean_inc(x_988);
x_989 = lean_ctor_get(x_962, 1);
lean_inc(x_989);
if (lean_is_exclusive(x_962)) {
 lean_ctor_release(x_962, 0);
 lean_ctor_release(x_962, 1);
 x_990 = x_962;
} else {
 lean_dec_ref(x_962);
 x_990 = lean_box(0);
}
if (lean_is_scalar(x_990)) {
 x_991 = lean_alloc_ctor(1, 2, 0);
} else {
 x_991 = x_990;
}
lean_ctor_set(x_991, 0, x_988);
lean_ctor_set(x_991, 1, x_989);
return x_991;
}
}
else
{
lean_object* x_992; 
lean_dec(x_960);
x_992 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_992, 0, x_14);
lean_ctor_set(x_992, 1, x_22);
x_1 = x_10;
x_2 = x_992;
x_7 = x_959;
goto _start;
}
}
}
}
else
{
lean_dec(x_23);
lean_dec(x_11);
lean_ctor_set(x_24, 1, x_22);
lean_ctor_set(x_24, 0, x_14);
x_1 = x_10;
x_2 = x_24;
x_7 = x_27;
goto _start;
}
}
else
{
lean_object* x_995; lean_object* x_996; lean_object* x_997; uint8_t x_998; 
x_995 = lean_ctor_get(x_24, 0);
x_996 = lean_ctor_get(x_24, 1);
lean_inc(x_996);
lean_inc(x_995);
lean_dec(x_24);
x_997 = lean_ctor_get(x_995, 0);
lean_inc(x_997);
lean_dec(x_995);
lean_inc(x_23);
x_998 = l_Lean_Meta_Match_isMatchEqnTheorem(x_997, x_23);
if (x_998 == 0)
{
lean_object* x_999; lean_object* x_1000; 
x_999 = l_Lean_Meta_isEqnThm_x3f(x_23, x_5, x_6, x_996);
x_1000 = lean_ctor_get(x_999, 0);
lean_inc(x_1000);
if (lean_obj_tag(x_1000) == 0)
{
lean_object* x_1001; lean_object* x_1002; lean_object* x_1003; 
x_1001 = lean_ctor_get(x_999, 1);
lean_inc(x_1001);
if (lean_is_exclusive(x_999)) {
 lean_ctor_release(x_999, 0);
 lean_ctor_release(x_999, 1);
 x_1002 = x_999;
} else {
 lean_dec_ref(x_999);
 x_1002 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1003 = l_Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0(x_23, x_998, x_3, x_4, x_5, x_6, x_1001);
if (lean_obj_tag(x_1003) == 0)
{
switch (x_13) {
case 0:
{
lean_object* x_1004; lean_object* x_1005; lean_object* x_1006; lean_object* x_1007; lean_object* x_1008; lean_object* x_1009; lean_object* x_1010; lean_object* x_1011; lean_object* x_1012; lean_object* x_1013; lean_object* x_1014; lean_object* x_1015; lean_object* x_1016; lean_object* x_1017; lean_object* x_1018; lean_object* x_1019; lean_object* x_1020; lean_object* x_1021; lean_object* x_1022; lean_object* x_1023; lean_object* x_1024; lean_object* x_1025; lean_object* x_1026; lean_object* x_1027; lean_object* x_1028; lean_object* x_1029; lean_object* x_1030; lean_object* x_1031; lean_object* x_1032; 
lean_dec(x_1002);
x_1004 = lean_ctor_get(x_1003, 0);
lean_inc(x_1004);
x_1005 = lean_ctor_get(x_1003, 1);
lean_inc(x_1005);
lean_dec(x_1003);
x_1006 = lean_st_ref_get(x_6, x_1005);
x_1007 = lean_ctor_get(x_1006, 1);
lean_inc(x_1007);
if (lean_is_exclusive(x_1006)) {
 lean_ctor_release(x_1006, 0);
 lean_ctor_release(x_1006, 1);
 x_1008 = x_1006;
} else {
 lean_dec_ref(x_1006);
 x_1008 = lean_box(0);
}
x_1009 = lean_ctor_get(x_5, 5);
lean_inc(x_1009);
x_1010 = l_Lean_SourceInfo_fromRef(x_1009, x_998);
lean_dec(x_1009);
x_1011 = lean_mk_string_unchecked("Lean", 4, 4);
x_1012 = lean_mk_string_unchecked("Parser", 6, 6);
x_1013 = lean_mk_string_unchecked("Tactic", 6, 6);
x_1014 = lean_mk_string_unchecked("grindParam", 10, 10);
lean_inc(x_1013);
lean_inc(x_1012);
lean_inc(x_1011);
x_1015 = l_Lean_Name_mkStr4(x_1011, x_1012, x_1013, x_1014);
x_1016 = lean_mk_string_unchecked("grindLemma", 10, 10);
lean_inc(x_1012);
lean_inc(x_1011);
x_1017 = l_Lean_Name_mkStr4(x_1011, x_1012, x_1013, x_1016);
x_1018 = lean_mk_string_unchecked("null", 4, 4);
x_1019 = l_Lean_Name_mkStr1(x_1018);
x_1020 = lean_mk_string_unchecked("Attr", 4, 4);
x_1021 = lean_mk_string_unchecked("grindMod", 8, 8);
lean_inc(x_1020);
lean_inc(x_1012);
lean_inc(x_1011);
x_1022 = l_Lean_Name_mkStr4(x_1011, x_1012, x_1020, x_1021);
x_1023 = lean_mk_string_unchecked("grindEq", 7, 7);
x_1024 = l_Lean_Name_mkStr4(x_1011, x_1012, x_1020, x_1023);
x_1025 = lean_mk_string_unchecked("=", 1, 1);
lean_inc(x_1010);
if (lean_is_scalar(x_1008)) {
 x_1026 = lean_alloc_ctor(2, 2, 0);
} else {
 x_1026 = x_1008;
 lean_ctor_set_tag(x_1026, 2);
}
lean_ctor_set(x_1026, 0, x_1010);
lean_ctor_set(x_1026, 1, x_1025);
lean_inc(x_1010);
x_1027 = l_Lean_Syntax_node1(x_1010, x_1024, x_1026);
lean_inc(x_1010);
x_1028 = l_Lean_Syntax_node1(x_1010, x_1022, x_1027);
lean_inc(x_1010);
x_1029 = l_Lean_Syntax_node1(x_1010, x_1019, x_1028);
x_1030 = lean_mk_syntax_ident(x_1004);
lean_inc(x_1010);
x_1031 = l_Lean_Syntax_node2(x_1010, x_1017, x_1029, x_1030);
x_1032 = l_Lean_Syntax_node1(x_1010, x_1015, x_1031);
x_15 = x_22;
x_16 = x_1032;
x_17 = x_1007;
goto block_21;
}
case 1:
{
lean_object* x_1033; lean_object* x_1034; lean_object* x_1035; lean_object* x_1036; lean_object* x_1037; lean_object* x_1038; lean_object* x_1039; lean_object* x_1040; lean_object* x_1041; lean_object* x_1042; lean_object* x_1043; lean_object* x_1044; lean_object* x_1045; lean_object* x_1046; lean_object* x_1047; lean_object* x_1048; lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; lean_object* x_1052; lean_object* x_1053; lean_object* x_1054; lean_object* x_1055; lean_object* x_1056; lean_object* x_1057; lean_object* x_1058; lean_object* x_1059; lean_object* x_1060; lean_object* x_1061; lean_object* x_1062; lean_object* x_1063; 
x_1033 = lean_ctor_get(x_1003, 0);
lean_inc(x_1033);
x_1034 = lean_ctor_get(x_1003, 1);
lean_inc(x_1034);
lean_dec(x_1003);
x_1035 = lean_st_ref_get(x_6, x_1034);
x_1036 = lean_ctor_get(x_1035, 1);
lean_inc(x_1036);
if (lean_is_exclusive(x_1035)) {
 lean_ctor_release(x_1035, 0);
 lean_ctor_release(x_1035, 1);
 x_1037 = x_1035;
} else {
 lean_dec_ref(x_1035);
 x_1037 = lean_box(0);
}
x_1038 = lean_ctor_get(x_5, 5);
lean_inc(x_1038);
x_1039 = l_Lean_SourceInfo_fromRef(x_1038, x_998);
lean_dec(x_1038);
x_1040 = lean_mk_string_unchecked("Lean", 4, 4);
x_1041 = lean_mk_string_unchecked("Parser", 6, 6);
x_1042 = lean_mk_string_unchecked("Tactic", 6, 6);
x_1043 = lean_mk_string_unchecked("grindParam", 10, 10);
lean_inc(x_1042);
lean_inc(x_1041);
lean_inc(x_1040);
x_1044 = l_Lean_Name_mkStr4(x_1040, x_1041, x_1042, x_1043);
x_1045 = lean_mk_string_unchecked("grindLemma", 10, 10);
lean_inc(x_1041);
lean_inc(x_1040);
x_1046 = l_Lean_Name_mkStr4(x_1040, x_1041, x_1042, x_1045);
x_1047 = lean_mk_string_unchecked("null", 4, 4);
x_1048 = l_Lean_Name_mkStr1(x_1047);
x_1049 = lean_mk_string_unchecked("Attr", 4, 4);
x_1050 = lean_mk_string_unchecked("grindMod", 8, 8);
lean_inc(x_1049);
lean_inc(x_1041);
lean_inc(x_1040);
x_1051 = l_Lean_Name_mkStr4(x_1040, x_1041, x_1049, x_1050);
x_1052 = lean_mk_string_unchecked("grindEqRhs", 10, 10);
x_1053 = l_Lean_Name_mkStr4(x_1040, x_1041, x_1049, x_1052);
x_1054 = lean_mk_string_unchecked("=", 1, 1);
lean_inc(x_1039);
if (lean_is_scalar(x_1037)) {
 x_1055 = lean_alloc_ctor(2, 2, 0);
} else {
 x_1055 = x_1037;
 lean_ctor_set_tag(x_1055, 2);
}
lean_ctor_set(x_1055, 0, x_1039);
lean_ctor_set(x_1055, 1, x_1054);
x_1056 = lean_mk_string_unchecked("_", 1, 1);
lean_inc(x_1039);
if (lean_is_scalar(x_1002)) {
 x_1057 = lean_alloc_ctor(2, 2, 0);
} else {
 x_1057 = x_1002;
 lean_ctor_set_tag(x_1057, 2);
}
lean_ctor_set(x_1057, 0, x_1039);
lean_ctor_set(x_1057, 1, x_1056);
lean_inc(x_1039);
x_1058 = l_Lean_Syntax_node2(x_1039, x_1053, x_1055, x_1057);
lean_inc(x_1039);
x_1059 = l_Lean_Syntax_node1(x_1039, x_1051, x_1058);
lean_inc(x_1039);
x_1060 = l_Lean_Syntax_node1(x_1039, x_1048, x_1059);
x_1061 = lean_mk_syntax_ident(x_1033);
lean_inc(x_1039);
x_1062 = l_Lean_Syntax_node2(x_1039, x_1046, x_1060, x_1061);
x_1063 = l_Lean_Syntax_node1(x_1039, x_1044, x_1062);
x_15 = x_22;
x_16 = x_1063;
x_17 = x_1036;
goto block_21;
}
case 2:
{
lean_object* x_1064; lean_object* x_1065; lean_object* x_1066; lean_object* x_1067; lean_object* x_1068; lean_object* x_1069; lean_object* x_1070; lean_object* x_1071; lean_object* x_1072; lean_object* x_1073; lean_object* x_1074; lean_object* x_1075; lean_object* x_1076; lean_object* x_1077; lean_object* x_1078; lean_object* x_1079; lean_object* x_1080; lean_object* x_1081; lean_object* x_1082; lean_object* x_1083; lean_object* x_1084; lean_object* x_1085; lean_object* x_1086; lean_object* x_1087; lean_object* x_1088; lean_object* x_1089; lean_object* x_1090; lean_object* x_1091; lean_object* x_1092; lean_object* x_1093; lean_object* x_1094; 
x_1064 = lean_ctor_get(x_1003, 0);
lean_inc(x_1064);
x_1065 = lean_ctor_get(x_1003, 1);
lean_inc(x_1065);
lean_dec(x_1003);
x_1066 = lean_st_ref_get(x_6, x_1065);
x_1067 = lean_ctor_get(x_1066, 1);
lean_inc(x_1067);
if (lean_is_exclusive(x_1066)) {
 lean_ctor_release(x_1066, 0);
 lean_ctor_release(x_1066, 1);
 x_1068 = x_1066;
} else {
 lean_dec_ref(x_1066);
 x_1068 = lean_box(0);
}
x_1069 = lean_ctor_get(x_5, 5);
lean_inc(x_1069);
x_1070 = l_Lean_SourceInfo_fromRef(x_1069, x_998);
lean_dec(x_1069);
x_1071 = lean_mk_string_unchecked("Lean", 4, 4);
x_1072 = lean_mk_string_unchecked("Parser", 6, 6);
x_1073 = lean_mk_string_unchecked("Tactic", 6, 6);
x_1074 = lean_mk_string_unchecked("grindParam", 10, 10);
lean_inc(x_1073);
lean_inc(x_1072);
lean_inc(x_1071);
x_1075 = l_Lean_Name_mkStr4(x_1071, x_1072, x_1073, x_1074);
x_1076 = lean_mk_string_unchecked("grindLemma", 10, 10);
lean_inc(x_1072);
lean_inc(x_1071);
x_1077 = l_Lean_Name_mkStr4(x_1071, x_1072, x_1073, x_1076);
x_1078 = lean_mk_string_unchecked("null", 4, 4);
x_1079 = l_Lean_Name_mkStr1(x_1078);
x_1080 = lean_mk_string_unchecked("Attr", 4, 4);
x_1081 = lean_mk_string_unchecked("grindMod", 8, 8);
lean_inc(x_1080);
lean_inc(x_1072);
lean_inc(x_1071);
x_1082 = l_Lean_Name_mkStr4(x_1071, x_1072, x_1080, x_1081);
x_1083 = lean_mk_string_unchecked("grindEqBoth", 11, 11);
x_1084 = l_Lean_Name_mkStr4(x_1071, x_1072, x_1080, x_1083);
x_1085 = lean_mk_string_unchecked("_", 1, 1);
lean_inc(x_1070);
if (lean_is_scalar(x_1068)) {
 x_1086 = lean_alloc_ctor(2, 2, 0);
} else {
 x_1086 = x_1068;
 lean_ctor_set_tag(x_1086, 2);
}
lean_ctor_set(x_1086, 0, x_1070);
lean_ctor_set(x_1086, 1, x_1085);
x_1087 = lean_mk_string_unchecked("=", 1, 1);
lean_inc(x_1070);
if (lean_is_scalar(x_1002)) {
 x_1088 = lean_alloc_ctor(2, 2, 0);
} else {
 x_1088 = x_1002;
 lean_ctor_set_tag(x_1088, 2);
}
lean_ctor_set(x_1088, 0, x_1070);
lean_ctor_set(x_1088, 1, x_1087);
lean_inc(x_1086);
lean_inc(x_1070);
x_1089 = l_Lean_Syntax_node3(x_1070, x_1084, x_1086, x_1088, x_1086);
lean_inc(x_1070);
x_1090 = l_Lean_Syntax_node1(x_1070, x_1082, x_1089);
lean_inc(x_1070);
x_1091 = l_Lean_Syntax_node1(x_1070, x_1079, x_1090);
x_1092 = lean_mk_syntax_ident(x_1064);
lean_inc(x_1070);
x_1093 = l_Lean_Syntax_node2(x_1070, x_1077, x_1091, x_1092);
x_1094 = l_Lean_Syntax_node1(x_1070, x_1075, x_1093);
x_15 = x_22;
x_16 = x_1094;
x_17 = x_1067;
goto block_21;
}
case 3:
{
lean_object* x_1095; lean_object* x_1096; lean_object* x_1097; lean_object* x_1098; lean_object* x_1099; lean_object* x_1100; lean_object* x_1101; lean_object* x_1102; lean_object* x_1103; lean_object* x_1104; lean_object* x_1105; lean_object* x_1106; lean_object* x_1107; lean_object* x_1108; lean_object* x_1109; lean_object* x_1110; lean_object* x_1111; lean_object* x_1112; lean_object* x_1113; lean_object* x_1114; lean_object* x_1115; lean_object* x_1116; lean_object* x_1117; lean_object* x_1118; lean_object* x_1119; lean_object* x_1120; lean_object* x_1121; lean_object* x_1122; lean_object* x_1123; lean_object* x_1124; lean_object* x_1125; lean_object* x_1126; lean_object* x_1127; lean_object* x_1128; 
x_1095 = lean_ctor_get(x_1003, 0);
lean_inc(x_1095);
x_1096 = lean_ctor_get(x_1003, 1);
lean_inc(x_1096);
lean_dec(x_1003);
x_1097 = lean_st_ref_get(x_6, x_1096);
x_1098 = lean_ctor_get(x_1097, 1);
lean_inc(x_1098);
if (lean_is_exclusive(x_1097)) {
 lean_ctor_release(x_1097, 0);
 lean_ctor_release(x_1097, 1);
 x_1099 = x_1097;
} else {
 lean_dec_ref(x_1097);
 x_1099 = lean_box(0);
}
x_1100 = lean_ctor_get(x_5, 5);
lean_inc(x_1100);
x_1101 = l_Lean_SourceInfo_fromRef(x_1100, x_998);
lean_dec(x_1100);
x_1102 = lean_mk_string_unchecked("Lean", 4, 4);
x_1103 = lean_mk_string_unchecked("Parser", 6, 6);
x_1104 = lean_mk_string_unchecked("Tactic", 6, 6);
x_1105 = lean_mk_string_unchecked("grindParam", 10, 10);
lean_inc(x_1104);
lean_inc(x_1103);
lean_inc(x_1102);
x_1106 = l_Lean_Name_mkStr4(x_1102, x_1103, x_1104, x_1105);
x_1107 = lean_mk_string_unchecked("grindLemma", 10, 10);
lean_inc(x_1103);
lean_inc(x_1102);
x_1108 = l_Lean_Name_mkStr4(x_1102, x_1103, x_1104, x_1107);
x_1109 = lean_mk_string_unchecked("null", 4, 4);
x_1110 = l_Lean_Name_mkStr1(x_1109);
x_1111 = lean_mk_string_unchecked("Attr", 4, 4);
x_1112 = lean_mk_string_unchecked("grindMod", 8, 8);
lean_inc(x_1111);
lean_inc(x_1103);
lean_inc(x_1102);
x_1113 = l_Lean_Name_mkStr4(x_1102, x_1103, x_1111, x_1112);
x_1114 = lean_mk_string_unchecked("grindEqBwd", 10, 10);
x_1115 = l_Lean_Name_mkStr4(x_1102, x_1103, x_1111, x_1114);
x_1116 = lean_mk_string_unchecked("group", 5, 5);
x_1117 = l_Lean_Name_mkStr1(x_1116);
x_1118 = lean_mk_string_unchecked("←", 3, 1);
lean_inc(x_1101);
if (lean_is_scalar(x_1099)) {
 x_1119 = lean_alloc_ctor(2, 2, 0);
} else {
 x_1119 = x_1099;
 lean_ctor_set_tag(x_1119, 2);
}
lean_ctor_set(x_1119, 0, x_1101);
lean_ctor_set(x_1119, 1, x_1118);
x_1120 = lean_mk_string_unchecked("=", 1, 1);
lean_inc(x_1101);
if (lean_is_scalar(x_1002)) {
 x_1121 = lean_alloc_ctor(2, 2, 0);
} else {
 x_1121 = x_1002;
 lean_ctor_set_tag(x_1121, 2);
}
lean_ctor_set(x_1121, 0, x_1101);
lean_ctor_set(x_1121, 1, x_1120);
lean_inc(x_1101);
x_1122 = l_Lean_Syntax_node2(x_1101, x_1117, x_1119, x_1121);
lean_inc(x_1101);
x_1123 = l_Lean_Syntax_node1(x_1101, x_1115, x_1122);
lean_inc(x_1101);
x_1124 = l_Lean_Syntax_node1(x_1101, x_1113, x_1123);
lean_inc(x_1101);
x_1125 = l_Lean_Syntax_node1(x_1101, x_1110, x_1124);
x_1126 = lean_mk_syntax_ident(x_1095);
lean_inc(x_1101);
x_1127 = l_Lean_Syntax_node2(x_1101, x_1108, x_1125, x_1126);
x_1128 = l_Lean_Syntax_node1(x_1101, x_1106, x_1127);
x_15 = x_22;
x_16 = x_1128;
x_17 = x_1098;
goto block_21;
}
case 4:
{
lean_object* x_1129; lean_object* x_1130; lean_object* x_1131; lean_object* x_1132; lean_object* x_1133; lean_object* x_1134; lean_object* x_1135; lean_object* x_1136; lean_object* x_1137; lean_object* x_1138; lean_object* x_1139; lean_object* x_1140; lean_object* x_1141; lean_object* x_1142; lean_object* x_1143; lean_object* x_1144; lean_object* x_1145; lean_object* x_1146; lean_object* x_1147; lean_object* x_1148; lean_object* x_1149; lean_object* x_1150; lean_object* x_1151; lean_object* x_1152; lean_object* x_1153; lean_object* x_1154; lean_object* x_1155; lean_object* x_1156; lean_object* x_1157; lean_object* x_1158; lean_object* x_1159; lean_object* x_1160; lean_object* x_1161; 
lean_dec(x_1002);
x_1129 = lean_ctor_get(x_1003, 0);
lean_inc(x_1129);
x_1130 = lean_ctor_get(x_1003, 1);
lean_inc(x_1130);
lean_dec(x_1003);
x_1131 = lean_st_ref_get(x_6, x_1130);
x_1132 = lean_ctor_get(x_1131, 1);
lean_inc(x_1132);
if (lean_is_exclusive(x_1131)) {
 lean_ctor_release(x_1131, 0);
 lean_ctor_release(x_1131, 1);
 x_1133 = x_1131;
} else {
 lean_dec_ref(x_1131);
 x_1133 = lean_box(0);
}
x_1134 = lean_ctor_get(x_5, 5);
lean_inc(x_1134);
x_1135 = l_Lean_SourceInfo_fromRef(x_1134, x_998);
lean_dec(x_1134);
x_1136 = lean_mk_string_unchecked("Lean", 4, 4);
x_1137 = lean_mk_string_unchecked("Parser", 6, 6);
x_1138 = lean_mk_string_unchecked("Tactic", 6, 6);
x_1139 = lean_mk_string_unchecked("grindParam", 10, 10);
lean_inc(x_1138);
lean_inc(x_1137);
lean_inc(x_1136);
x_1140 = l_Lean_Name_mkStr4(x_1136, x_1137, x_1138, x_1139);
x_1141 = lean_mk_string_unchecked("grindLemma", 10, 10);
lean_inc(x_1137);
lean_inc(x_1136);
x_1142 = l_Lean_Name_mkStr4(x_1136, x_1137, x_1138, x_1141);
x_1143 = lean_mk_string_unchecked("null", 4, 4);
x_1144 = l_Lean_Name_mkStr1(x_1143);
x_1145 = lean_mk_string_unchecked("Attr", 4, 4);
x_1146 = lean_mk_string_unchecked("grindMod", 8, 8);
lean_inc(x_1145);
lean_inc(x_1137);
lean_inc(x_1136);
x_1147 = l_Lean_Name_mkStr4(x_1136, x_1137, x_1145, x_1146);
x_1148 = lean_mk_string_unchecked("grindFwd", 8, 8);
x_1149 = l_Lean_Name_mkStr4(x_1136, x_1137, x_1145, x_1148);
x_1150 = lean_mk_string_unchecked("token", 5, 5);
x_1151 = lean_mk_string_unchecked("→ ", 4, 2);
x_1152 = l_Lean_Name_mkStr2(x_1150, x_1151);
x_1153 = lean_mk_string_unchecked("→", 3, 1);
lean_inc(x_1135);
if (lean_is_scalar(x_1133)) {
 x_1154 = lean_alloc_ctor(2, 2, 0);
} else {
 x_1154 = x_1133;
 lean_ctor_set_tag(x_1154, 2);
}
lean_ctor_set(x_1154, 0, x_1135);
lean_ctor_set(x_1154, 1, x_1153);
lean_inc(x_1135);
x_1155 = l_Lean_Syntax_node1(x_1135, x_1152, x_1154);
lean_inc(x_1135);
x_1156 = l_Lean_Syntax_node1(x_1135, x_1149, x_1155);
lean_inc(x_1135);
x_1157 = l_Lean_Syntax_node1(x_1135, x_1147, x_1156);
lean_inc(x_1135);
x_1158 = l_Lean_Syntax_node1(x_1135, x_1144, x_1157);
x_1159 = lean_mk_syntax_ident(x_1129);
lean_inc(x_1135);
x_1160 = l_Lean_Syntax_node2(x_1135, x_1142, x_1158, x_1159);
x_1161 = l_Lean_Syntax_node1(x_1135, x_1140, x_1160);
x_15 = x_22;
x_16 = x_1161;
x_17 = x_1132;
goto block_21;
}
case 5:
{
lean_object* x_1162; lean_object* x_1163; lean_object* x_1164; lean_object* x_1165; lean_object* x_1166; lean_object* x_1167; lean_object* x_1168; lean_object* x_1169; lean_object* x_1170; lean_object* x_1171; lean_object* x_1172; lean_object* x_1173; lean_object* x_1174; lean_object* x_1175; lean_object* x_1176; lean_object* x_1177; lean_object* x_1178; lean_object* x_1179; lean_object* x_1180; lean_object* x_1181; lean_object* x_1182; lean_object* x_1183; lean_object* x_1184; lean_object* x_1185; lean_object* x_1186; lean_object* x_1187; lean_object* x_1188; lean_object* x_1189; lean_object* x_1190; lean_object* x_1191; lean_object* x_1192; lean_object* x_1193; lean_object* x_1194; 
lean_dec(x_1002);
x_1162 = lean_ctor_get(x_1003, 0);
lean_inc(x_1162);
x_1163 = lean_ctor_get(x_1003, 1);
lean_inc(x_1163);
lean_dec(x_1003);
x_1164 = lean_st_ref_get(x_6, x_1163);
x_1165 = lean_ctor_get(x_1164, 1);
lean_inc(x_1165);
if (lean_is_exclusive(x_1164)) {
 lean_ctor_release(x_1164, 0);
 lean_ctor_release(x_1164, 1);
 x_1166 = x_1164;
} else {
 lean_dec_ref(x_1164);
 x_1166 = lean_box(0);
}
x_1167 = lean_ctor_get(x_5, 5);
lean_inc(x_1167);
x_1168 = l_Lean_SourceInfo_fromRef(x_1167, x_998);
lean_dec(x_1167);
x_1169 = lean_mk_string_unchecked("Lean", 4, 4);
x_1170 = lean_mk_string_unchecked("Parser", 6, 6);
x_1171 = lean_mk_string_unchecked("Tactic", 6, 6);
x_1172 = lean_mk_string_unchecked("grindParam", 10, 10);
lean_inc(x_1171);
lean_inc(x_1170);
lean_inc(x_1169);
x_1173 = l_Lean_Name_mkStr4(x_1169, x_1170, x_1171, x_1172);
x_1174 = lean_mk_string_unchecked("grindLemma", 10, 10);
lean_inc(x_1170);
lean_inc(x_1169);
x_1175 = l_Lean_Name_mkStr4(x_1169, x_1170, x_1171, x_1174);
x_1176 = lean_mk_string_unchecked("null", 4, 4);
x_1177 = l_Lean_Name_mkStr1(x_1176);
x_1178 = lean_mk_string_unchecked("Attr", 4, 4);
x_1179 = lean_mk_string_unchecked("grindMod", 8, 8);
lean_inc(x_1178);
lean_inc(x_1170);
lean_inc(x_1169);
x_1180 = l_Lean_Name_mkStr4(x_1169, x_1170, x_1178, x_1179);
x_1181 = lean_mk_string_unchecked("grindBwd", 8, 8);
x_1182 = l_Lean_Name_mkStr4(x_1169, x_1170, x_1178, x_1181);
x_1183 = lean_mk_string_unchecked("token", 5, 5);
x_1184 = lean_mk_string_unchecked("← ", 4, 2);
x_1185 = l_Lean_Name_mkStr2(x_1183, x_1184);
x_1186 = lean_mk_string_unchecked("←", 3, 1);
lean_inc(x_1168);
if (lean_is_scalar(x_1166)) {
 x_1187 = lean_alloc_ctor(2, 2, 0);
} else {
 x_1187 = x_1166;
 lean_ctor_set_tag(x_1187, 2);
}
lean_ctor_set(x_1187, 0, x_1168);
lean_ctor_set(x_1187, 1, x_1186);
lean_inc(x_1168);
x_1188 = l_Lean_Syntax_node1(x_1168, x_1185, x_1187);
lean_inc(x_1168);
x_1189 = l_Lean_Syntax_node1(x_1168, x_1182, x_1188);
lean_inc(x_1168);
x_1190 = l_Lean_Syntax_node1(x_1168, x_1180, x_1189);
lean_inc(x_1168);
x_1191 = l_Lean_Syntax_node1(x_1168, x_1177, x_1190);
x_1192 = lean_mk_syntax_ident(x_1162);
lean_inc(x_1168);
x_1193 = l_Lean_Syntax_node2(x_1168, x_1175, x_1191, x_1192);
x_1194 = l_Lean_Syntax_node1(x_1168, x_1173, x_1193);
x_15 = x_22;
x_16 = x_1194;
x_17 = x_1165;
goto block_21;
}
case 6:
{
lean_object* x_1195; lean_object* x_1196; lean_object* x_1197; lean_object* x_1198; lean_object* x_1199; lean_object* x_1200; lean_object* x_1201; lean_object* x_1202; lean_object* x_1203; lean_object* x_1204; lean_object* x_1205; lean_object* x_1206; lean_object* x_1207; lean_object* x_1208; lean_object* x_1209; lean_object* x_1210; lean_object* x_1211; lean_object* x_1212; lean_object* x_1213; lean_object* x_1214; lean_object* x_1215; lean_object* x_1216; lean_object* x_1217; lean_object* x_1218; lean_object* x_1219; lean_object* x_1220; lean_object* x_1221; lean_object* x_1222; lean_object* x_1223; lean_object* x_1224; lean_object* x_1225; lean_object* x_1226; lean_object* x_1227; 
lean_dec(x_1002);
x_1195 = lean_ctor_get(x_1003, 0);
lean_inc(x_1195);
x_1196 = lean_ctor_get(x_1003, 1);
lean_inc(x_1196);
lean_dec(x_1003);
x_1197 = lean_st_ref_get(x_6, x_1196);
x_1198 = lean_ctor_get(x_1197, 1);
lean_inc(x_1198);
if (lean_is_exclusive(x_1197)) {
 lean_ctor_release(x_1197, 0);
 lean_ctor_release(x_1197, 1);
 x_1199 = x_1197;
} else {
 lean_dec_ref(x_1197);
 x_1199 = lean_box(0);
}
x_1200 = lean_ctor_get(x_5, 5);
lean_inc(x_1200);
x_1201 = l_Lean_SourceInfo_fromRef(x_1200, x_998);
lean_dec(x_1200);
x_1202 = lean_mk_string_unchecked("Lean", 4, 4);
x_1203 = lean_mk_string_unchecked("Parser", 6, 6);
x_1204 = lean_mk_string_unchecked("Tactic", 6, 6);
x_1205 = lean_mk_string_unchecked("grindParam", 10, 10);
lean_inc(x_1204);
lean_inc(x_1203);
lean_inc(x_1202);
x_1206 = l_Lean_Name_mkStr4(x_1202, x_1203, x_1204, x_1205);
x_1207 = lean_mk_string_unchecked("grindLemma", 10, 10);
lean_inc(x_1203);
lean_inc(x_1202);
x_1208 = l_Lean_Name_mkStr4(x_1202, x_1203, x_1204, x_1207);
x_1209 = lean_mk_string_unchecked("null", 4, 4);
x_1210 = l_Lean_Name_mkStr1(x_1209);
x_1211 = lean_mk_string_unchecked("Attr", 4, 4);
x_1212 = lean_mk_string_unchecked("grindMod", 8, 8);
lean_inc(x_1211);
lean_inc(x_1203);
lean_inc(x_1202);
x_1213 = l_Lean_Name_mkStr4(x_1202, x_1203, x_1211, x_1212);
x_1214 = lean_mk_string_unchecked("grindLR", 7, 7);
x_1215 = l_Lean_Name_mkStr4(x_1202, x_1203, x_1211, x_1214);
x_1216 = lean_mk_string_unchecked("token", 5, 5);
x_1217 = lean_mk_string_unchecked("=> ", 3, 3);
x_1218 = l_Lean_Name_mkStr2(x_1216, x_1217);
x_1219 = lean_mk_string_unchecked("=>", 2, 2);
lean_inc(x_1201);
if (lean_is_scalar(x_1199)) {
 x_1220 = lean_alloc_ctor(2, 2, 0);
} else {
 x_1220 = x_1199;
 lean_ctor_set_tag(x_1220, 2);
}
lean_ctor_set(x_1220, 0, x_1201);
lean_ctor_set(x_1220, 1, x_1219);
lean_inc(x_1201);
x_1221 = l_Lean_Syntax_node1(x_1201, x_1218, x_1220);
lean_inc(x_1201);
x_1222 = l_Lean_Syntax_node1(x_1201, x_1215, x_1221);
lean_inc(x_1201);
x_1223 = l_Lean_Syntax_node1(x_1201, x_1213, x_1222);
lean_inc(x_1201);
x_1224 = l_Lean_Syntax_node1(x_1201, x_1210, x_1223);
x_1225 = lean_mk_syntax_ident(x_1195);
lean_inc(x_1201);
x_1226 = l_Lean_Syntax_node2(x_1201, x_1208, x_1224, x_1225);
x_1227 = l_Lean_Syntax_node1(x_1201, x_1206, x_1226);
x_15 = x_22;
x_16 = x_1227;
x_17 = x_1198;
goto block_21;
}
case 7:
{
lean_object* x_1228; lean_object* x_1229; lean_object* x_1230; lean_object* x_1231; lean_object* x_1232; lean_object* x_1233; lean_object* x_1234; lean_object* x_1235; lean_object* x_1236; lean_object* x_1237; lean_object* x_1238; lean_object* x_1239; lean_object* x_1240; lean_object* x_1241; lean_object* x_1242; lean_object* x_1243; lean_object* x_1244; lean_object* x_1245; lean_object* x_1246; lean_object* x_1247; lean_object* x_1248; lean_object* x_1249; lean_object* x_1250; lean_object* x_1251; lean_object* x_1252; lean_object* x_1253; lean_object* x_1254; lean_object* x_1255; lean_object* x_1256; lean_object* x_1257; lean_object* x_1258; lean_object* x_1259; lean_object* x_1260; 
lean_dec(x_1002);
x_1228 = lean_ctor_get(x_1003, 0);
lean_inc(x_1228);
x_1229 = lean_ctor_get(x_1003, 1);
lean_inc(x_1229);
lean_dec(x_1003);
x_1230 = lean_st_ref_get(x_6, x_1229);
x_1231 = lean_ctor_get(x_1230, 1);
lean_inc(x_1231);
if (lean_is_exclusive(x_1230)) {
 lean_ctor_release(x_1230, 0);
 lean_ctor_release(x_1230, 1);
 x_1232 = x_1230;
} else {
 lean_dec_ref(x_1230);
 x_1232 = lean_box(0);
}
x_1233 = lean_ctor_get(x_5, 5);
lean_inc(x_1233);
x_1234 = l_Lean_SourceInfo_fromRef(x_1233, x_998);
lean_dec(x_1233);
x_1235 = lean_mk_string_unchecked("Lean", 4, 4);
x_1236 = lean_mk_string_unchecked("Parser", 6, 6);
x_1237 = lean_mk_string_unchecked("Tactic", 6, 6);
x_1238 = lean_mk_string_unchecked("grindParam", 10, 10);
lean_inc(x_1237);
lean_inc(x_1236);
lean_inc(x_1235);
x_1239 = l_Lean_Name_mkStr4(x_1235, x_1236, x_1237, x_1238);
x_1240 = lean_mk_string_unchecked("grindLemma", 10, 10);
lean_inc(x_1236);
lean_inc(x_1235);
x_1241 = l_Lean_Name_mkStr4(x_1235, x_1236, x_1237, x_1240);
x_1242 = lean_mk_string_unchecked("null", 4, 4);
x_1243 = l_Lean_Name_mkStr1(x_1242);
x_1244 = lean_mk_string_unchecked("Attr", 4, 4);
x_1245 = lean_mk_string_unchecked("grindMod", 8, 8);
lean_inc(x_1244);
lean_inc(x_1236);
lean_inc(x_1235);
x_1246 = l_Lean_Name_mkStr4(x_1235, x_1236, x_1244, x_1245);
x_1247 = lean_mk_string_unchecked("grindRL", 7, 7);
x_1248 = l_Lean_Name_mkStr4(x_1235, x_1236, x_1244, x_1247);
x_1249 = lean_mk_string_unchecked("token", 5, 5);
x_1250 = lean_mk_string_unchecked("<= ", 3, 3);
x_1251 = l_Lean_Name_mkStr2(x_1249, x_1250);
x_1252 = lean_mk_string_unchecked("<=", 2, 2);
lean_inc(x_1234);
if (lean_is_scalar(x_1232)) {
 x_1253 = lean_alloc_ctor(2, 2, 0);
} else {
 x_1253 = x_1232;
 lean_ctor_set_tag(x_1253, 2);
}
lean_ctor_set(x_1253, 0, x_1234);
lean_ctor_set(x_1253, 1, x_1252);
lean_inc(x_1234);
x_1254 = l_Lean_Syntax_node1(x_1234, x_1251, x_1253);
lean_inc(x_1234);
x_1255 = l_Lean_Syntax_node1(x_1234, x_1248, x_1254);
lean_inc(x_1234);
x_1256 = l_Lean_Syntax_node1(x_1234, x_1246, x_1255);
lean_inc(x_1234);
x_1257 = l_Lean_Syntax_node1(x_1234, x_1243, x_1256);
x_1258 = lean_mk_syntax_ident(x_1228);
lean_inc(x_1234);
x_1259 = l_Lean_Syntax_node2(x_1234, x_1241, x_1257, x_1258);
x_1260 = l_Lean_Syntax_node1(x_1234, x_1239, x_1259);
x_15 = x_22;
x_16 = x_1260;
x_17 = x_1231;
goto block_21;
}
case 8:
{
lean_object* x_1261; lean_object* x_1262; lean_object* x_1263; lean_object* x_1264; lean_object* x_1265; lean_object* x_1266; lean_object* x_1267; lean_object* x_1268; lean_object* x_1269; lean_object* x_1270; lean_object* x_1271; lean_object* x_1272; lean_object* x_1273; lean_object* x_1274; lean_object* x_1275; lean_object* x_1276; lean_object* x_1277; lean_object* x_1278; lean_object* x_1279; lean_object* x_1280; 
lean_dec(x_1002);
x_1261 = lean_ctor_get(x_1003, 0);
lean_inc(x_1261);
x_1262 = lean_ctor_get(x_1003, 1);
lean_inc(x_1262);
lean_dec(x_1003);
x_1263 = lean_st_ref_get(x_6, x_1262);
x_1264 = lean_ctor_get(x_1263, 1);
lean_inc(x_1264);
lean_dec(x_1263);
x_1265 = lean_ctor_get(x_5, 5);
lean_inc(x_1265);
x_1266 = l_Lean_SourceInfo_fromRef(x_1265, x_998);
lean_dec(x_1265);
x_1267 = lean_mk_string_unchecked("Lean", 4, 4);
x_1268 = lean_mk_string_unchecked("Parser", 6, 6);
x_1269 = lean_mk_string_unchecked("Tactic", 6, 6);
x_1270 = lean_mk_string_unchecked("grindParam", 10, 10);
lean_inc(x_1269);
lean_inc(x_1268);
lean_inc(x_1267);
x_1271 = l_Lean_Name_mkStr4(x_1267, x_1268, x_1269, x_1270);
x_1272 = lean_mk_string_unchecked("grindLemma", 10, 10);
x_1273 = l_Lean_Name_mkStr4(x_1267, x_1268, x_1269, x_1272);
x_1274 = lean_mk_string_unchecked("null", 4, 4);
x_1275 = l_Lean_Name_mkStr1(x_1274);
x_1276 = l_Array_mkArray0(lean_box(0));
lean_inc(x_1266);
x_1277 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1277, 0, x_1266);
lean_ctor_set(x_1277, 1, x_1275);
lean_ctor_set(x_1277, 2, x_1276);
x_1278 = lean_mk_syntax_ident(x_1261);
lean_inc(x_1266);
x_1279 = l_Lean_Syntax_node2(x_1266, x_1273, x_1277, x_1278);
x_1280 = l_Lean_Syntax_node1(x_1266, x_1271, x_1279);
x_15 = x_22;
x_16 = x_1280;
x_17 = x_1264;
goto block_21;
}
default: 
{
lean_object* x_1281; lean_object* x_1282; lean_object* x_1283; lean_object* x_1284; lean_object* x_1285; lean_object* x_1286; lean_object* x_1287; lean_object* x_1288; lean_object* x_1289; lean_object* x_1290; lean_object* x_1291; lean_object* x_1292; lean_object* x_1293; lean_object* x_1294; lean_object* x_1295; lean_object* x_1296; lean_object* x_1297; lean_object* x_1298; lean_object* x_1299; lean_object* x_1300; lean_object* x_1301; lean_object* x_1302; lean_object* x_1303; lean_object* x_1304; lean_object* x_1305; lean_object* x_1306; lean_object* x_1307; lean_object* x_1308; lean_object* x_1309; 
lean_dec(x_1002);
x_1281 = lean_ctor_get(x_1003, 0);
lean_inc(x_1281);
x_1282 = lean_ctor_get(x_1003, 1);
lean_inc(x_1282);
lean_dec(x_1003);
x_1283 = lean_st_ref_get(x_6, x_1282);
x_1284 = lean_ctor_get(x_1283, 1);
lean_inc(x_1284);
if (lean_is_exclusive(x_1283)) {
 lean_ctor_release(x_1283, 0);
 lean_ctor_release(x_1283, 1);
 x_1285 = x_1283;
} else {
 lean_dec_ref(x_1283);
 x_1285 = lean_box(0);
}
x_1286 = lean_ctor_get(x_5, 5);
lean_inc(x_1286);
x_1287 = l_Lean_SourceInfo_fromRef(x_1286, x_998);
lean_dec(x_1286);
x_1288 = lean_mk_string_unchecked("Lean", 4, 4);
x_1289 = lean_mk_string_unchecked("Parser", 6, 6);
x_1290 = lean_mk_string_unchecked("Tactic", 6, 6);
x_1291 = lean_mk_string_unchecked("grindParam", 10, 10);
lean_inc(x_1290);
lean_inc(x_1289);
lean_inc(x_1288);
x_1292 = l_Lean_Name_mkStr4(x_1288, x_1289, x_1290, x_1291);
x_1293 = lean_mk_string_unchecked("grindLemma", 10, 10);
lean_inc(x_1289);
lean_inc(x_1288);
x_1294 = l_Lean_Name_mkStr4(x_1288, x_1289, x_1290, x_1293);
x_1295 = lean_mk_string_unchecked("null", 4, 4);
x_1296 = l_Lean_Name_mkStr1(x_1295);
x_1297 = lean_mk_string_unchecked("Attr", 4, 4);
x_1298 = lean_mk_string_unchecked("grindMod", 8, 8);
lean_inc(x_1297);
lean_inc(x_1289);
lean_inc(x_1288);
x_1299 = l_Lean_Name_mkStr4(x_1288, x_1289, x_1297, x_1298);
x_1300 = lean_mk_string_unchecked("grindUsr", 8, 8);
x_1301 = l_Lean_Name_mkStr4(x_1288, x_1289, x_1297, x_1300);
x_1302 = lean_mk_string_unchecked("usr", 3, 3);
lean_inc(x_1287);
if (lean_is_scalar(x_1285)) {
 x_1303 = lean_alloc_ctor(2, 2, 0);
} else {
 x_1303 = x_1285;
 lean_ctor_set_tag(x_1303, 2);
}
lean_ctor_set(x_1303, 0, x_1287);
lean_ctor_set(x_1303, 1, x_1302);
lean_inc(x_1287);
x_1304 = l_Lean_Syntax_node1(x_1287, x_1301, x_1303);
lean_inc(x_1287);
x_1305 = l_Lean_Syntax_node1(x_1287, x_1299, x_1304);
lean_inc(x_1287);
x_1306 = l_Lean_Syntax_node1(x_1287, x_1296, x_1305);
x_1307 = lean_mk_syntax_ident(x_1281);
lean_inc(x_1287);
x_1308 = l_Lean_Syntax_node2(x_1287, x_1294, x_1306, x_1307);
x_1309 = l_Lean_Syntax_node1(x_1287, x_1292, x_1308);
x_15 = x_22;
x_16 = x_1309;
x_17 = x_1284;
goto block_21;
}
}
}
else
{
lean_object* x_1310; lean_object* x_1311; lean_object* x_1312; lean_object* x_1313; 
lean_dec(x_1002);
lean_dec(x_22);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1310 = lean_ctor_get(x_1003, 0);
lean_inc(x_1310);
x_1311 = lean_ctor_get(x_1003, 1);
lean_inc(x_1311);
if (lean_is_exclusive(x_1003)) {
 lean_ctor_release(x_1003, 0);
 lean_ctor_release(x_1003, 1);
 x_1312 = x_1003;
} else {
 lean_dec_ref(x_1003);
 x_1312 = lean_box(0);
}
if (lean_is_scalar(x_1312)) {
 x_1313 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1313 = x_1312;
}
lean_ctor_set(x_1313, 0, x_1310);
lean_ctor_set(x_1313, 1, x_1311);
return x_1313;
}
}
else
{
lean_object* x_1314; lean_object* x_1315; lean_object* x_1316; uint8_t x_1317; 
lean_dec(x_23);
lean_dec(x_11);
x_1314 = lean_ctor_get(x_999, 1);
lean_inc(x_1314);
if (lean_is_exclusive(x_999)) {
 lean_ctor_release(x_999, 0);
 lean_ctor_release(x_999, 1);
 x_1315 = x_999;
} else {
 lean_dec_ref(x_999);
 x_1315 = lean_box(0);
}
x_1316 = lean_ctor_get(x_1000, 0);
lean_inc(x_1316);
lean_dec(x_1000);
x_1317 = l_Lean_NameSet_contains(x_14, x_1316);
if (x_1317 == 0)
{
lean_object* x_1318; 
lean_dec(x_1315);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1316);
x_1318 = l_Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0(x_1316, x_1317, x_3, x_4, x_5, x_6, x_1314);
if (lean_obj_tag(x_1318) == 0)
{
lean_object* x_1319; lean_object* x_1320; lean_object* x_1321; lean_object* x_1322; lean_object* x_1323; lean_object* x_1324; lean_object* x_1325; lean_object* x_1326; lean_object* x_1327; lean_object* x_1328; lean_object* x_1329; lean_object* x_1330; lean_object* x_1331; lean_object* x_1332; lean_object* x_1333; lean_object* x_1334; lean_object* x_1335; lean_object* x_1336; lean_object* x_1337; lean_object* x_1338; lean_object* x_1339; lean_object* x_1340; lean_object* x_1341; lean_object* x_1342; 
x_1319 = lean_ctor_get(x_1318, 0);
lean_inc(x_1319);
x_1320 = lean_ctor_get(x_1318, 1);
lean_inc(x_1320);
lean_dec(x_1318);
x_1321 = lean_st_ref_get(x_6, x_1320);
x_1322 = lean_ctor_get(x_1321, 1);
lean_inc(x_1322);
if (lean_is_exclusive(x_1321)) {
 lean_ctor_release(x_1321, 0);
 lean_ctor_release(x_1321, 1);
 x_1323 = x_1321;
} else {
 lean_dec_ref(x_1321);
 x_1323 = lean_box(0);
}
x_1324 = lean_ctor_get(x_5, 5);
lean_inc(x_1324);
x_1325 = l_Lean_NameSet_insert(x_14, x_1316);
x_1326 = l_Lean_SourceInfo_fromRef(x_1324, x_1317);
lean_dec(x_1324);
x_1327 = lean_mk_string_unchecked("Lean", 4, 4);
x_1328 = lean_mk_string_unchecked("Parser", 6, 6);
x_1329 = lean_mk_string_unchecked("Tactic", 6, 6);
x_1330 = lean_mk_string_unchecked("grindParam", 10, 10);
lean_inc(x_1329);
lean_inc(x_1328);
lean_inc(x_1327);
x_1331 = l_Lean_Name_mkStr4(x_1327, x_1328, x_1329, x_1330);
x_1332 = lean_mk_string_unchecked("grindLemma", 10, 10);
x_1333 = l_Lean_Name_mkStr4(x_1327, x_1328, x_1329, x_1332);
x_1334 = lean_mk_string_unchecked("null", 4, 4);
x_1335 = l_Lean_Name_mkStr1(x_1334);
x_1336 = l_Array_mkArray0(lean_box(0));
lean_inc(x_1326);
x_1337 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1337, 0, x_1326);
lean_ctor_set(x_1337, 1, x_1335);
lean_ctor_set(x_1337, 2, x_1336);
x_1338 = lean_mk_syntax_ident(x_1319);
lean_inc(x_1326);
x_1339 = l_Lean_Syntax_node2(x_1326, x_1333, x_1337, x_1338);
x_1340 = l_Lean_Syntax_node1(x_1326, x_1331, x_1339);
x_1341 = lean_array_push(x_22, x_1340);
if (lean_is_scalar(x_1323)) {
 x_1342 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1342 = x_1323;
}
lean_ctor_set(x_1342, 0, x_1325);
lean_ctor_set(x_1342, 1, x_1341);
x_1 = x_10;
x_2 = x_1342;
x_7 = x_1322;
goto _start;
}
else
{
lean_object* x_1344; lean_object* x_1345; lean_object* x_1346; lean_object* x_1347; 
lean_dec(x_1316);
lean_dec(x_22);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1344 = lean_ctor_get(x_1318, 0);
lean_inc(x_1344);
x_1345 = lean_ctor_get(x_1318, 1);
lean_inc(x_1345);
if (lean_is_exclusive(x_1318)) {
 lean_ctor_release(x_1318, 0);
 lean_ctor_release(x_1318, 1);
 x_1346 = x_1318;
} else {
 lean_dec_ref(x_1318);
 x_1346 = lean_box(0);
}
if (lean_is_scalar(x_1346)) {
 x_1347 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1347 = x_1346;
}
lean_ctor_set(x_1347, 0, x_1344);
lean_ctor_set(x_1347, 1, x_1345);
return x_1347;
}
}
else
{
lean_object* x_1348; 
lean_dec(x_1316);
if (lean_is_scalar(x_1315)) {
 x_1348 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1348 = x_1315;
}
lean_ctor_set(x_1348, 0, x_14);
lean_ctor_set(x_1348, 1, x_22);
x_1 = x_10;
x_2 = x_1348;
x_7 = x_1314;
goto _start;
}
}
}
else
{
lean_object* x_1350; 
lean_dec(x_23);
lean_dec(x_11);
x_1350 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1350, 0, x_14);
lean_ctor_set(x_1350, 1, x_22);
x_1 = x_10;
x_2 = x_1350;
x_7 = x_996;
goto _start;
}
}
}
else
{
lean_object* x_1352; lean_object* x_1353; 
lean_dec(x_12);
lean_dec(x_11);
x_1352 = lean_ctor_get(x_2, 1);
lean_inc(x_1352);
lean_dec(x_2);
x_1353 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1353, 0, x_14);
lean_ctor_set(x_1353, 1, x_1352);
x_1 = x_10;
x_2 = x_1353;
goto _start;
}
block_21:
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_array_push(x_15, x_16);
if (lean_is_scalar(x_11)) {
 x_19 = lean_alloc_ctor(0, 2, 0);
} else {
 x_19 = x_11;
 lean_ctor_set_tag(x_19, 0);
}
lean_ctor_set(x_19, 0, x_14);
lean_ctor_set(x_19, 1, x_18);
x_1 = x_10;
x_2 = x_19;
x_7 = x_17;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Tactic_mkGrindOnly_spec__3_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Tactic_mkGrindOnly_spec__3_spec__3___redArg(x_2, x_3, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Elab_Tactic_mkGrindOnly_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_12 = x_2;
} else {
 lean_dec_ref(x_2);
 x_12 = lean_box(0);
}
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
x_14 = lean_ctor_get_uint8(x_10, sizeof(void*)*1);
lean_dec(x_10);
x_15 = lean_ctor_get(x_3, 0);
lean_inc(x_15);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_3, 1);
lean_inc(x_23);
lean_dec(x_3);
x_24 = lean_ctor_get(x_13, 0);
lean_inc(x_24);
lean_dec(x_13);
x_25 = lean_st_ref_get(x_7, x_8);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_ctor_get(x_25, 1);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
lean_dec(x_27);
lean_inc(x_24);
x_30 = l_Lean_Meta_Match_isMatchEqnTheorem(x_29, x_24);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_free_object(x_25);
x_31 = l_Lean_Meta_isEqnThm_x3f(x_24, x_6, x_7, x_28);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_31);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_31, 1);
x_35 = lean_ctor_get(x_31, 0);
lean_dec(x_35);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_36 = l_Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0(x_24, x_30, x_4, x_5, x_6, x_7, x_34);
if (lean_obj_tag(x_36) == 0)
{
switch (x_14) {
case 0:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
lean_free_object(x_31);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_st_ref_get(x_7, x_38);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_41 = lean_ctor_get(x_39, 1);
x_42 = lean_ctor_get(x_39, 0);
lean_dec(x_42);
x_43 = lean_ctor_get(x_6, 5);
lean_inc(x_43);
x_44 = l_Lean_SourceInfo_fromRef(x_43, x_30);
lean_dec(x_43);
x_45 = lean_mk_string_unchecked("Lean", 4, 4);
x_46 = lean_mk_string_unchecked("Parser", 6, 6);
x_47 = lean_mk_string_unchecked("Tactic", 6, 6);
x_48 = lean_mk_string_unchecked("grindParam", 10, 10);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
x_49 = l_Lean_Name_mkStr4(x_45, x_46, x_47, x_48);
x_50 = lean_mk_string_unchecked("grindLemma", 10, 10);
lean_inc(x_46);
lean_inc(x_45);
x_51 = l_Lean_Name_mkStr4(x_45, x_46, x_47, x_50);
x_52 = lean_mk_string_unchecked("null", 4, 4);
x_53 = l_Lean_Name_mkStr1(x_52);
x_54 = lean_mk_string_unchecked("Attr", 4, 4);
x_55 = lean_mk_string_unchecked("grindMod", 8, 8);
lean_inc(x_54);
lean_inc(x_46);
lean_inc(x_45);
x_56 = l_Lean_Name_mkStr4(x_45, x_46, x_54, x_55);
x_57 = lean_mk_string_unchecked("grindEq", 7, 7);
x_58 = l_Lean_Name_mkStr4(x_45, x_46, x_54, x_57);
x_59 = lean_mk_string_unchecked("=", 1, 1);
lean_inc(x_44);
lean_ctor_set_tag(x_39, 2);
lean_ctor_set(x_39, 1, x_59);
lean_ctor_set(x_39, 0, x_44);
lean_inc(x_44);
x_60 = l_Lean_Syntax_node1(x_44, x_58, x_39);
lean_inc(x_44);
x_61 = l_Lean_Syntax_node1(x_44, x_56, x_60);
lean_inc(x_44);
x_62 = l_Lean_Syntax_node1(x_44, x_53, x_61);
x_63 = lean_mk_syntax_ident(x_37);
lean_inc(x_44);
x_64 = l_Lean_Syntax_node2(x_44, x_51, x_62, x_63);
x_65 = l_Lean_Syntax_node1(x_44, x_49, x_64);
x_16 = x_23;
x_17 = x_65;
x_18 = x_41;
goto block_22;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_66 = lean_ctor_get(x_39, 1);
lean_inc(x_66);
lean_dec(x_39);
x_67 = lean_ctor_get(x_6, 5);
lean_inc(x_67);
x_68 = l_Lean_SourceInfo_fromRef(x_67, x_30);
lean_dec(x_67);
x_69 = lean_mk_string_unchecked("Lean", 4, 4);
x_70 = lean_mk_string_unchecked("Parser", 6, 6);
x_71 = lean_mk_string_unchecked("Tactic", 6, 6);
x_72 = lean_mk_string_unchecked("grindParam", 10, 10);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
x_73 = l_Lean_Name_mkStr4(x_69, x_70, x_71, x_72);
x_74 = lean_mk_string_unchecked("grindLemma", 10, 10);
lean_inc(x_70);
lean_inc(x_69);
x_75 = l_Lean_Name_mkStr4(x_69, x_70, x_71, x_74);
x_76 = lean_mk_string_unchecked("null", 4, 4);
x_77 = l_Lean_Name_mkStr1(x_76);
x_78 = lean_mk_string_unchecked("Attr", 4, 4);
x_79 = lean_mk_string_unchecked("grindMod", 8, 8);
lean_inc(x_78);
lean_inc(x_70);
lean_inc(x_69);
x_80 = l_Lean_Name_mkStr4(x_69, x_70, x_78, x_79);
x_81 = lean_mk_string_unchecked("grindEq", 7, 7);
x_82 = l_Lean_Name_mkStr4(x_69, x_70, x_78, x_81);
x_83 = lean_mk_string_unchecked("=", 1, 1);
lean_inc(x_68);
x_84 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_84, 0, x_68);
lean_ctor_set(x_84, 1, x_83);
lean_inc(x_68);
x_85 = l_Lean_Syntax_node1(x_68, x_82, x_84);
lean_inc(x_68);
x_86 = l_Lean_Syntax_node1(x_68, x_80, x_85);
lean_inc(x_68);
x_87 = l_Lean_Syntax_node1(x_68, x_77, x_86);
x_88 = lean_mk_syntax_ident(x_37);
lean_inc(x_68);
x_89 = l_Lean_Syntax_node2(x_68, x_75, x_87, x_88);
x_90 = l_Lean_Syntax_node1(x_68, x_73, x_89);
x_16 = x_23;
x_17 = x_90;
x_18 = x_66;
goto block_22;
}
}
case 1:
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_91 = lean_ctor_get(x_36, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_36, 1);
lean_inc(x_92);
lean_dec(x_36);
x_93 = lean_st_ref_get(x_7, x_92);
x_94 = !lean_is_exclusive(x_93);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_95 = lean_ctor_get(x_93, 1);
x_96 = lean_ctor_get(x_93, 0);
lean_dec(x_96);
x_97 = lean_ctor_get(x_6, 5);
lean_inc(x_97);
x_98 = l_Lean_SourceInfo_fromRef(x_97, x_30);
lean_dec(x_97);
x_99 = lean_mk_string_unchecked("Lean", 4, 4);
x_100 = lean_mk_string_unchecked("Parser", 6, 6);
x_101 = lean_mk_string_unchecked("Tactic", 6, 6);
x_102 = lean_mk_string_unchecked("grindParam", 10, 10);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
x_103 = l_Lean_Name_mkStr4(x_99, x_100, x_101, x_102);
x_104 = lean_mk_string_unchecked("grindLemma", 10, 10);
lean_inc(x_100);
lean_inc(x_99);
x_105 = l_Lean_Name_mkStr4(x_99, x_100, x_101, x_104);
x_106 = lean_mk_string_unchecked("null", 4, 4);
x_107 = l_Lean_Name_mkStr1(x_106);
x_108 = lean_mk_string_unchecked("Attr", 4, 4);
x_109 = lean_mk_string_unchecked("grindMod", 8, 8);
lean_inc(x_108);
lean_inc(x_100);
lean_inc(x_99);
x_110 = l_Lean_Name_mkStr4(x_99, x_100, x_108, x_109);
x_111 = lean_mk_string_unchecked("grindEqRhs", 10, 10);
x_112 = l_Lean_Name_mkStr4(x_99, x_100, x_108, x_111);
x_113 = lean_mk_string_unchecked("=", 1, 1);
lean_inc(x_98);
lean_ctor_set_tag(x_93, 2);
lean_ctor_set(x_93, 1, x_113);
lean_ctor_set(x_93, 0, x_98);
x_114 = lean_mk_string_unchecked("_", 1, 1);
lean_inc(x_98);
lean_ctor_set_tag(x_31, 2);
lean_ctor_set(x_31, 1, x_114);
lean_ctor_set(x_31, 0, x_98);
lean_inc(x_98);
x_115 = l_Lean_Syntax_node2(x_98, x_112, x_93, x_31);
lean_inc(x_98);
x_116 = l_Lean_Syntax_node1(x_98, x_110, x_115);
lean_inc(x_98);
x_117 = l_Lean_Syntax_node1(x_98, x_107, x_116);
x_118 = lean_mk_syntax_ident(x_91);
lean_inc(x_98);
x_119 = l_Lean_Syntax_node2(x_98, x_105, x_117, x_118);
x_120 = l_Lean_Syntax_node1(x_98, x_103, x_119);
x_16 = x_23;
x_17 = x_120;
x_18 = x_95;
goto block_22;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_121 = lean_ctor_get(x_93, 1);
lean_inc(x_121);
lean_dec(x_93);
x_122 = lean_ctor_get(x_6, 5);
lean_inc(x_122);
x_123 = l_Lean_SourceInfo_fromRef(x_122, x_30);
lean_dec(x_122);
x_124 = lean_mk_string_unchecked("Lean", 4, 4);
x_125 = lean_mk_string_unchecked("Parser", 6, 6);
x_126 = lean_mk_string_unchecked("Tactic", 6, 6);
x_127 = lean_mk_string_unchecked("grindParam", 10, 10);
lean_inc(x_126);
lean_inc(x_125);
lean_inc(x_124);
x_128 = l_Lean_Name_mkStr4(x_124, x_125, x_126, x_127);
x_129 = lean_mk_string_unchecked("grindLemma", 10, 10);
lean_inc(x_125);
lean_inc(x_124);
x_130 = l_Lean_Name_mkStr4(x_124, x_125, x_126, x_129);
x_131 = lean_mk_string_unchecked("null", 4, 4);
x_132 = l_Lean_Name_mkStr1(x_131);
x_133 = lean_mk_string_unchecked("Attr", 4, 4);
x_134 = lean_mk_string_unchecked("grindMod", 8, 8);
lean_inc(x_133);
lean_inc(x_125);
lean_inc(x_124);
x_135 = l_Lean_Name_mkStr4(x_124, x_125, x_133, x_134);
x_136 = lean_mk_string_unchecked("grindEqRhs", 10, 10);
x_137 = l_Lean_Name_mkStr4(x_124, x_125, x_133, x_136);
x_138 = lean_mk_string_unchecked("=", 1, 1);
lean_inc(x_123);
x_139 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_139, 0, x_123);
lean_ctor_set(x_139, 1, x_138);
x_140 = lean_mk_string_unchecked("_", 1, 1);
lean_inc(x_123);
lean_ctor_set_tag(x_31, 2);
lean_ctor_set(x_31, 1, x_140);
lean_ctor_set(x_31, 0, x_123);
lean_inc(x_123);
x_141 = l_Lean_Syntax_node2(x_123, x_137, x_139, x_31);
lean_inc(x_123);
x_142 = l_Lean_Syntax_node1(x_123, x_135, x_141);
lean_inc(x_123);
x_143 = l_Lean_Syntax_node1(x_123, x_132, x_142);
x_144 = lean_mk_syntax_ident(x_91);
lean_inc(x_123);
x_145 = l_Lean_Syntax_node2(x_123, x_130, x_143, x_144);
x_146 = l_Lean_Syntax_node1(x_123, x_128, x_145);
x_16 = x_23;
x_17 = x_146;
x_18 = x_121;
goto block_22;
}
}
case 2:
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; 
x_147 = lean_ctor_get(x_36, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_36, 1);
lean_inc(x_148);
lean_dec(x_36);
x_149 = lean_st_ref_get(x_7, x_148);
x_150 = !lean_is_exclusive(x_149);
if (x_150 == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_151 = lean_ctor_get(x_149, 1);
x_152 = lean_ctor_get(x_149, 0);
lean_dec(x_152);
x_153 = lean_ctor_get(x_6, 5);
lean_inc(x_153);
x_154 = l_Lean_SourceInfo_fromRef(x_153, x_30);
lean_dec(x_153);
x_155 = lean_mk_string_unchecked("Lean", 4, 4);
x_156 = lean_mk_string_unchecked("Parser", 6, 6);
x_157 = lean_mk_string_unchecked("Tactic", 6, 6);
x_158 = lean_mk_string_unchecked("grindParam", 10, 10);
lean_inc(x_157);
lean_inc(x_156);
lean_inc(x_155);
x_159 = l_Lean_Name_mkStr4(x_155, x_156, x_157, x_158);
x_160 = lean_mk_string_unchecked("grindLemma", 10, 10);
lean_inc(x_156);
lean_inc(x_155);
x_161 = l_Lean_Name_mkStr4(x_155, x_156, x_157, x_160);
x_162 = lean_mk_string_unchecked("null", 4, 4);
x_163 = l_Lean_Name_mkStr1(x_162);
x_164 = lean_mk_string_unchecked("Attr", 4, 4);
x_165 = lean_mk_string_unchecked("grindMod", 8, 8);
lean_inc(x_164);
lean_inc(x_156);
lean_inc(x_155);
x_166 = l_Lean_Name_mkStr4(x_155, x_156, x_164, x_165);
x_167 = lean_mk_string_unchecked("grindEqBoth", 11, 11);
x_168 = l_Lean_Name_mkStr4(x_155, x_156, x_164, x_167);
x_169 = lean_mk_string_unchecked("_", 1, 1);
lean_inc(x_154);
lean_ctor_set_tag(x_149, 2);
lean_ctor_set(x_149, 1, x_169);
lean_ctor_set(x_149, 0, x_154);
x_170 = lean_mk_string_unchecked("=", 1, 1);
lean_inc(x_154);
lean_ctor_set_tag(x_31, 2);
lean_ctor_set(x_31, 1, x_170);
lean_ctor_set(x_31, 0, x_154);
lean_inc(x_149);
lean_inc(x_154);
x_171 = l_Lean_Syntax_node3(x_154, x_168, x_149, x_31, x_149);
lean_inc(x_154);
x_172 = l_Lean_Syntax_node1(x_154, x_166, x_171);
lean_inc(x_154);
x_173 = l_Lean_Syntax_node1(x_154, x_163, x_172);
x_174 = lean_mk_syntax_ident(x_147);
lean_inc(x_154);
x_175 = l_Lean_Syntax_node2(x_154, x_161, x_173, x_174);
x_176 = l_Lean_Syntax_node1(x_154, x_159, x_175);
x_16 = x_23;
x_17 = x_176;
x_18 = x_151;
goto block_22;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_177 = lean_ctor_get(x_149, 1);
lean_inc(x_177);
lean_dec(x_149);
x_178 = lean_ctor_get(x_6, 5);
lean_inc(x_178);
x_179 = l_Lean_SourceInfo_fromRef(x_178, x_30);
lean_dec(x_178);
x_180 = lean_mk_string_unchecked("Lean", 4, 4);
x_181 = lean_mk_string_unchecked("Parser", 6, 6);
x_182 = lean_mk_string_unchecked("Tactic", 6, 6);
x_183 = lean_mk_string_unchecked("grindParam", 10, 10);
lean_inc(x_182);
lean_inc(x_181);
lean_inc(x_180);
x_184 = l_Lean_Name_mkStr4(x_180, x_181, x_182, x_183);
x_185 = lean_mk_string_unchecked("grindLemma", 10, 10);
lean_inc(x_181);
lean_inc(x_180);
x_186 = l_Lean_Name_mkStr4(x_180, x_181, x_182, x_185);
x_187 = lean_mk_string_unchecked("null", 4, 4);
x_188 = l_Lean_Name_mkStr1(x_187);
x_189 = lean_mk_string_unchecked("Attr", 4, 4);
x_190 = lean_mk_string_unchecked("grindMod", 8, 8);
lean_inc(x_189);
lean_inc(x_181);
lean_inc(x_180);
x_191 = l_Lean_Name_mkStr4(x_180, x_181, x_189, x_190);
x_192 = lean_mk_string_unchecked("grindEqBoth", 11, 11);
x_193 = l_Lean_Name_mkStr4(x_180, x_181, x_189, x_192);
x_194 = lean_mk_string_unchecked("_", 1, 1);
lean_inc(x_179);
x_195 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_195, 0, x_179);
lean_ctor_set(x_195, 1, x_194);
x_196 = lean_mk_string_unchecked("=", 1, 1);
lean_inc(x_179);
lean_ctor_set_tag(x_31, 2);
lean_ctor_set(x_31, 1, x_196);
lean_ctor_set(x_31, 0, x_179);
lean_inc(x_195);
lean_inc(x_179);
x_197 = l_Lean_Syntax_node3(x_179, x_193, x_195, x_31, x_195);
lean_inc(x_179);
x_198 = l_Lean_Syntax_node1(x_179, x_191, x_197);
lean_inc(x_179);
x_199 = l_Lean_Syntax_node1(x_179, x_188, x_198);
x_200 = lean_mk_syntax_ident(x_147);
lean_inc(x_179);
x_201 = l_Lean_Syntax_node2(x_179, x_186, x_199, x_200);
x_202 = l_Lean_Syntax_node1(x_179, x_184, x_201);
x_16 = x_23;
x_17 = x_202;
x_18 = x_177;
goto block_22;
}
}
case 3:
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; uint8_t x_206; 
x_203 = lean_ctor_get(x_36, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_36, 1);
lean_inc(x_204);
lean_dec(x_36);
x_205 = lean_st_ref_get(x_7, x_204);
x_206 = !lean_is_exclusive(x_205);
if (x_206 == 0)
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_207 = lean_ctor_get(x_205, 1);
x_208 = lean_ctor_get(x_205, 0);
lean_dec(x_208);
x_209 = lean_ctor_get(x_6, 5);
lean_inc(x_209);
x_210 = l_Lean_SourceInfo_fromRef(x_209, x_30);
lean_dec(x_209);
x_211 = lean_mk_string_unchecked("Lean", 4, 4);
x_212 = lean_mk_string_unchecked("Parser", 6, 6);
x_213 = lean_mk_string_unchecked("Tactic", 6, 6);
x_214 = lean_mk_string_unchecked("grindParam", 10, 10);
lean_inc(x_213);
lean_inc(x_212);
lean_inc(x_211);
x_215 = l_Lean_Name_mkStr4(x_211, x_212, x_213, x_214);
x_216 = lean_mk_string_unchecked("grindLemma", 10, 10);
lean_inc(x_212);
lean_inc(x_211);
x_217 = l_Lean_Name_mkStr4(x_211, x_212, x_213, x_216);
x_218 = lean_mk_string_unchecked("null", 4, 4);
x_219 = l_Lean_Name_mkStr1(x_218);
x_220 = lean_mk_string_unchecked("Attr", 4, 4);
x_221 = lean_mk_string_unchecked("grindMod", 8, 8);
lean_inc(x_220);
lean_inc(x_212);
lean_inc(x_211);
x_222 = l_Lean_Name_mkStr4(x_211, x_212, x_220, x_221);
x_223 = lean_mk_string_unchecked("grindEqBwd", 10, 10);
x_224 = l_Lean_Name_mkStr4(x_211, x_212, x_220, x_223);
x_225 = lean_mk_string_unchecked("group", 5, 5);
x_226 = l_Lean_Name_mkStr1(x_225);
x_227 = lean_mk_string_unchecked("←", 3, 1);
lean_inc(x_210);
lean_ctor_set_tag(x_205, 2);
lean_ctor_set(x_205, 1, x_227);
lean_ctor_set(x_205, 0, x_210);
x_228 = lean_mk_string_unchecked("=", 1, 1);
lean_inc(x_210);
lean_ctor_set_tag(x_31, 2);
lean_ctor_set(x_31, 1, x_228);
lean_ctor_set(x_31, 0, x_210);
lean_inc(x_210);
x_229 = l_Lean_Syntax_node2(x_210, x_226, x_205, x_31);
lean_inc(x_210);
x_230 = l_Lean_Syntax_node1(x_210, x_224, x_229);
lean_inc(x_210);
x_231 = l_Lean_Syntax_node1(x_210, x_222, x_230);
lean_inc(x_210);
x_232 = l_Lean_Syntax_node1(x_210, x_219, x_231);
x_233 = lean_mk_syntax_ident(x_203);
lean_inc(x_210);
x_234 = l_Lean_Syntax_node2(x_210, x_217, x_232, x_233);
x_235 = l_Lean_Syntax_node1(x_210, x_215, x_234);
x_16 = x_23;
x_17 = x_235;
x_18 = x_207;
goto block_22;
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_236 = lean_ctor_get(x_205, 1);
lean_inc(x_236);
lean_dec(x_205);
x_237 = lean_ctor_get(x_6, 5);
lean_inc(x_237);
x_238 = l_Lean_SourceInfo_fromRef(x_237, x_30);
lean_dec(x_237);
x_239 = lean_mk_string_unchecked("Lean", 4, 4);
x_240 = lean_mk_string_unchecked("Parser", 6, 6);
x_241 = lean_mk_string_unchecked("Tactic", 6, 6);
x_242 = lean_mk_string_unchecked("grindParam", 10, 10);
lean_inc(x_241);
lean_inc(x_240);
lean_inc(x_239);
x_243 = l_Lean_Name_mkStr4(x_239, x_240, x_241, x_242);
x_244 = lean_mk_string_unchecked("grindLemma", 10, 10);
lean_inc(x_240);
lean_inc(x_239);
x_245 = l_Lean_Name_mkStr4(x_239, x_240, x_241, x_244);
x_246 = lean_mk_string_unchecked("null", 4, 4);
x_247 = l_Lean_Name_mkStr1(x_246);
x_248 = lean_mk_string_unchecked("Attr", 4, 4);
x_249 = lean_mk_string_unchecked("grindMod", 8, 8);
lean_inc(x_248);
lean_inc(x_240);
lean_inc(x_239);
x_250 = l_Lean_Name_mkStr4(x_239, x_240, x_248, x_249);
x_251 = lean_mk_string_unchecked("grindEqBwd", 10, 10);
x_252 = l_Lean_Name_mkStr4(x_239, x_240, x_248, x_251);
x_253 = lean_mk_string_unchecked("group", 5, 5);
x_254 = l_Lean_Name_mkStr1(x_253);
x_255 = lean_mk_string_unchecked("←", 3, 1);
lean_inc(x_238);
x_256 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_256, 0, x_238);
lean_ctor_set(x_256, 1, x_255);
x_257 = lean_mk_string_unchecked("=", 1, 1);
lean_inc(x_238);
lean_ctor_set_tag(x_31, 2);
lean_ctor_set(x_31, 1, x_257);
lean_ctor_set(x_31, 0, x_238);
lean_inc(x_238);
x_258 = l_Lean_Syntax_node2(x_238, x_254, x_256, x_31);
lean_inc(x_238);
x_259 = l_Lean_Syntax_node1(x_238, x_252, x_258);
lean_inc(x_238);
x_260 = l_Lean_Syntax_node1(x_238, x_250, x_259);
lean_inc(x_238);
x_261 = l_Lean_Syntax_node1(x_238, x_247, x_260);
x_262 = lean_mk_syntax_ident(x_203);
lean_inc(x_238);
x_263 = l_Lean_Syntax_node2(x_238, x_245, x_261, x_262);
x_264 = l_Lean_Syntax_node1(x_238, x_243, x_263);
x_16 = x_23;
x_17 = x_264;
x_18 = x_236;
goto block_22;
}
}
case 4:
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; uint8_t x_268; 
lean_free_object(x_31);
x_265 = lean_ctor_get(x_36, 0);
lean_inc(x_265);
x_266 = lean_ctor_get(x_36, 1);
lean_inc(x_266);
lean_dec(x_36);
x_267 = lean_st_ref_get(x_7, x_266);
x_268 = !lean_is_exclusive(x_267);
if (x_268 == 0)
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; 
x_269 = lean_ctor_get(x_267, 1);
x_270 = lean_ctor_get(x_267, 0);
lean_dec(x_270);
x_271 = lean_ctor_get(x_6, 5);
lean_inc(x_271);
x_272 = l_Lean_SourceInfo_fromRef(x_271, x_30);
lean_dec(x_271);
x_273 = lean_mk_string_unchecked("Lean", 4, 4);
x_274 = lean_mk_string_unchecked("Parser", 6, 6);
x_275 = lean_mk_string_unchecked("Tactic", 6, 6);
x_276 = lean_mk_string_unchecked("grindParam", 10, 10);
lean_inc(x_275);
lean_inc(x_274);
lean_inc(x_273);
x_277 = l_Lean_Name_mkStr4(x_273, x_274, x_275, x_276);
x_278 = lean_mk_string_unchecked("grindLemma", 10, 10);
lean_inc(x_274);
lean_inc(x_273);
x_279 = l_Lean_Name_mkStr4(x_273, x_274, x_275, x_278);
x_280 = lean_mk_string_unchecked("null", 4, 4);
x_281 = l_Lean_Name_mkStr1(x_280);
x_282 = lean_mk_string_unchecked("Attr", 4, 4);
x_283 = lean_mk_string_unchecked("grindMod", 8, 8);
lean_inc(x_282);
lean_inc(x_274);
lean_inc(x_273);
x_284 = l_Lean_Name_mkStr4(x_273, x_274, x_282, x_283);
x_285 = lean_mk_string_unchecked("grindFwd", 8, 8);
x_286 = l_Lean_Name_mkStr4(x_273, x_274, x_282, x_285);
x_287 = lean_mk_string_unchecked("token", 5, 5);
x_288 = lean_mk_string_unchecked("→ ", 4, 2);
x_289 = l_Lean_Name_mkStr2(x_287, x_288);
x_290 = lean_mk_string_unchecked("→", 3, 1);
lean_inc(x_272);
lean_ctor_set_tag(x_267, 2);
lean_ctor_set(x_267, 1, x_290);
lean_ctor_set(x_267, 0, x_272);
lean_inc(x_272);
x_291 = l_Lean_Syntax_node1(x_272, x_289, x_267);
lean_inc(x_272);
x_292 = l_Lean_Syntax_node1(x_272, x_286, x_291);
lean_inc(x_272);
x_293 = l_Lean_Syntax_node1(x_272, x_284, x_292);
lean_inc(x_272);
x_294 = l_Lean_Syntax_node1(x_272, x_281, x_293);
x_295 = lean_mk_syntax_ident(x_265);
lean_inc(x_272);
x_296 = l_Lean_Syntax_node2(x_272, x_279, x_294, x_295);
x_297 = l_Lean_Syntax_node1(x_272, x_277, x_296);
x_16 = x_23;
x_17 = x_297;
x_18 = x_269;
goto block_22;
}
else
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; 
x_298 = lean_ctor_get(x_267, 1);
lean_inc(x_298);
lean_dec(x_267);
x_299 = lean_ctor_get(x_6, 5);
lean_inc(x_299);
x_300 = l_Lean_SourceInfo_fromRef(x_299, x_30);
lean_dec(x_299);
x_301 = lean_mk_string_unchecked("Lean", 4, 4);
x_302 = lean_mk_string_unchecked("Parser", 6, 6);
x_303 = lean_mk_string_unchecked("Tactic", 6, 6);
x_304 = lean_mk_string_unchecked("grindParam", 10, 10);
lean_inc(x_303);
lean_inc(x_302);
lean_inc(x_301);
x_305 = l_Lean_Name_mkStr4(x_301, x_302, x_303, x_304);
x_306 = lean_mk_string_unchecked("grindLemma", 10, 10);
lean_inc(x_302);
lean_inc(x_301);
x_307 = l_Lean_Name_mkStr4(x_301, x_302, x_303, x_306);
x_308 = lean_mk_string_unchecked("null", 4, 4);
x_309 = l_Lean_Name_mkStr1(x_308);
x_310 = lean_mk_string_unchecked("Attr", 4, 4);
x_311 = lean_mk_string_unchecked("grindMod", 8, 8);
lean_inc(x_310);
lean_inc(x_302);
lean_inc(x_301);
x_312 = l_Lean_Name_mkStr4(x_301, x_302, x_310, x_311);
x_313 = lean_mk_string_unchecked("grindFwd", 8, 8);
x_314 = l_Lean_Name_mkStr4(x_301, x_302, x_310, x_313);
x_315 = lean_mk_string_unchecked("token", 5, 5);
x_316 = lean_mk_string_unchecked("→ ", 4, 2);
x_317 = l_Lean_Name_mkStr2(x_315, x_316);
x_318 = lean_mk_string_unchecked("→", 3, 1);
lean_inc(x_300);
x_319 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_319, 0, x_300);
lean_ctor_set(x_319, 1, x_318);
lean_inc(x_300);
x_320 = l_Lean_Syntax_node1(x_300, x_317, x_319);
lean_inc(x_300);
x_321 = l_Lean_Syntax_node1(x_300, x_314, x_320);
lean_inc(x_300);
x_322 = l_Lean_Syntax_node1(x_300, x_312, x_321);
lean_inc(x_300);
x_323 = l_Lean_Syntax_node1(x_300, x_309, x_322);
x_324 = lean_mk_syntax_ident(x_265);
lean_inc(x_300);
x_325 = l_Lean_Syntax_node2(x_300, x_307, x_323, x_324);
x_326 = l_Lean_Syntax_node1(x_300, x_305, x_325);
x_16 = x_23;
x_17 = x_326;
x_18 = x_298;
goto block_22;
}
}
case 5:
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; uint8_t x_330; 
lean_free_object(x_31);
x_327 = lean_ctor_get(x_36, 0);
lean_inc(x_327);
x_328 = lean_ctor_get(x_36, 1);
lean_inc(x_328);
lean_dec(x_36);
x_329 = lean_st_ref_get(x_7, x_328);
x_330 = !lean_is_exclusive(x_329);
if (x_330 == 0)
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; 
x_331 = lean_ctor_get(x_329, 1);
x_332 = lean_ctor_get(x_329, 0);
lean_dec(x_332);
x_333 = lean_ctor_get(x_6, 5);
lean_inc(x_333);
x_334 = l_Lean_SourceInfo_fromRef(x_333, x_30);
lean_dec(x_333);
x_335 = lean_mk_string_unchecked("Lean", 4, 4);
x_336 = lean_mk_string_unchecked("Parser", 6, 6);
x_337 = lean_mk_string_unchecked("Tactic", 6, 6);
x_338 = lean_mk_string_unchecked("grindParam", 10, 10);
lean_inc(x_337);
lean_inc(x_336);
lean_inc(x_335);
x_339 = l_Lean_Name_mkStr4(x_335, x_336, x_337, x_338);
x_340 = lean_mk_string_unchecked("grindLemma", 10, 10);
lean_inc(x_336);
lean_inc(x_335);
x_341 = l_Lean_Name_mkStr4(x_335, x_336, x_337, x_340);
x_342 = lean_mk_string_unchecked("null", 4, 4);
x_343 = l_Lean_Name_mkStr1(x_342);
x_344 = lean_mk_string_unchecked("Attr", 4, 4);
x_345 = lean_mk_string_unchecked("grindMod", 8, 8);
lean_inc(x_344);
lean_inc(x_336);
lean_inc(x_335);
x_346 = l_Lean_Name_mkStr4(x_335, x_336, x_344, x_345);
x_347 = lean_mk_string_unchecked("grindBwd", 8, 8);
x_348 = l_Lean_Name_mkStr4(x_335, x_336, x_344, x_347);
x_349 = lean_mk_string_unchecked("token", 5, 5);
x_350 = lean_mk_string_unchecked("← ", 4, 2);
x_351 = l_Lean_Name_mkStr2(x_349, x_350);
x_352 = lean_mk_string_unchecked("←", 3, 1);
lean_inc(x_334);
lean_ctor_set_tag(x_329, 2);
lean_ctor_set(x_329, 1, x_352);
lean_ctor_set(x_329, 0, x_334);
lean_inc(x_334);
x_353 = l_Lean_Syntax_node1(x_334, x_351, x_329);
lean_inc(x_334);
x_354 = l_Lean_Syntax_node1(x_334, x_348, x_353);
lean_inc(x_334);
x_355 = l_Lean_Syntax_node1(x_334, x_346, x_354);
lean_inc(x_334);
x_356 = l_Lean_Syntax_node1(x_334, x_343, x_355);
x_357 = lean_mk_syntax_ident(x_327);
lean_inc(x_334);
x_358 = l_Lean_Syntax_node2(x_334, x_341, x_356, x_357);
x_359 = l_Lean_Syntax_node1(x_334, x_339, x_358);
x_16 = x_23;
x_17 = x_359;
x_18 = x_331;
goto block_22;
}
else
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; 
x_360 = lean_ctor_get(x_329, 1);
lean_inc(x_360);
lean_dec(x_329);
x_361 = lean_ctor_get(x_6, 5);
lean_inc(x_361);
x_362 = l_Lean_SourceInfo_fromRef(x_361, x_30);
lean_dec(x_361);
x_363 = lean_mk_string_unchecked("Lean", 4, 4);
x_364 = lean_mk_string_unchecked("Parser", 6, 6);
x_365 = lean_mk_string_unchecked("Tactic", 6, 6);
x_366 = lean_mk_string_unchecked("grindParam", 10, 10);
lean_inc(x_365);
lean_inc(x_364);
lean_inc(x_363);
x_367 = l_Lean_Name_mkStr4(x_363, x_364, x_365, x_366);
x_368 = lean_mk_string_unchecked("grindLemma", 10, 10);
lean_inc(x_364);
lean_inc(x_363);
x_369 = l_Lean_Name_mkStr4(x_363, x_364, x_365, x_368);
x_370 = lean_mk_string_unchecked("null", 4, 4);
x_371 = l_Lean_Name_mkStr1(x_370);
x_372 = lean_mk_string_unchecked("Attr", 4, 4);
x_373 = lean_mk_string_unchecked("grindMod", 8, 8);
lean_inc(x_372);
lean_inc(x_364);
lean_inc(x_363);
x_374 = l_Lean_Name_mkStr4(x_363, x_364, x_372, x_373);
x_375 = lean_mk_string_unchecked("grindBwd", 8, 8);
x_376 = l_Lean_Name_mkStr4(x_363, x_364, x_372, x_375);
x_377 = lean_mk_string_unchecked("token", 5, 5);
x_378 = lean_mk_string_unchecked("← ", 4, 2);
x_379 = l_Lean_Name_mkStr2(x_377, x_378);
x_380 = lean_mk_string_unchecked("←", 3, 1);
lean_inc(x_362);
x_381 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_381, 0, x_362);
lean_ctor_set(x_381, 1, x_380);
lean_inc(x_362);
x_382 = l_Lean_Syntax_node1(x_362, x_379, x_381);
lean_inc(x_362);
x_383 = l_Lean_Syntax_node1(x_362, x_376, x_382);
lean_inc(x_362);
x_384 = l_Lean_Syntax_node1(x_362, x_374, x_383);
lean_inc(x_362);
x_385 = l_Lean_Syntax_node1(x_362, x_371, x_384);
x_386 = lean_mk_syntax_ident(x_327);
lean_inc(x_362);
x_387 = l_Lean_Syntax_node2(x_362, x_369, x_385, x_386);
x_388 = l_Lean_Syntax_node1(x_362, x_367, x_387);
x_16 = x_23;
x_17 = x_388;
x_18 = x_360;
goto block_22;
}
}
case 6:
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; uint8_t x_392; 
lean_free_object(x_31);
x_389 = lean_ctor_get(x_36, 0);
lean_inc(x_389);
x_390 = lean_ctor_get(x_36, 1);
lean_inc(x_390);
lean_dec(x_36);
x_391 = lean_st_ref_get(x_7, x_390);
x_392 = !lean_is_exclusive(x_391);
if (x_392 == 0)
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; 
x_393 = lean_ctor_get(x_391, 1);
x_394 = lean_ctor_get(x_391, 0);
lean_dec(x_394);
x_395 = lean_ctor_get(x_6, 5);
lean_inc(x_395);
x_396 = l_Lean_SourceInfo_fromRef(x_395, x_30);
lean_dec(x_395);
x_397 = lean_mk_string_unchecked("Lean", 4, 4);
x_398 = lean_mk_string_unchecked("Parser", 6, 6);
x_399 = lean_mk_string_unchecked("Tactic", 6, 6);
x_400 = lean_mk_string_unchecked("grindParam", 10, 10);
lean_inc(x_399);
lean_inc(x_398);
lean_inc(x_397);
x_401 = l_Lean_Name_mkStr4(x_397, x_398, x_399, x_400);
x_402 = lean_mk_string_unchecked("grindLemma", 10, 10);
lean_inc(x_398);
lean_inc(x_397);
x_403 = l_Lean_Name_mkStr4(x_397, x_398, x_399, x_402);
x_404 = lean_mk_string_unchecked("null", 4, 4);
x_405 = l_Lean_Name_mkStr1(x_404);
x_406 = lean_mk_string_unchecked("Attr", 4, 4);
x_407 = lean_mk_string_unchecked("grindMod", 8, 8);
lean_inc(x_406);
lean_inc(x_398);
lean_inc(x_397);
x_408 = l_Lean_Name_mkStr4(x_397, x_398, x_406, x_407);
x_409 = lean_mk_string_unchecked("grindLR", 7, 7);
x_410 = l_Lean_Name_mkStr4(x_397, x_398, x_406, x_409);
x_411 = lean_mk_string_unchecked("token", 5, 5);
x_412 = lean_mk_string_unchecked("=> ", 3, 3);
x_413 = l_Lean_Name_mkStr2(x_411, x_412);
x_414 = lean_mk_string_unchecked("=>", 2, 2);
lean_inc(x_396);
lean_ctor_set_tag(x_391, 2);
lean_ctor_set(x_391, 1, x_414);
lean_ctor_set(x_391, 0, x_396);
lean_inc(x_396);
x_415 = l_Lean_Syntax_node1(x_396, x_413, x_391);
lean_inc(x_396);
x_416 = l_Lean_Syntax_node1(x_396, x_410, x_415);
lean_inc(x_396);
x_417 = l_Lean_Syntax_node1(x_396, x_408, x_416);
lean_inc(x_396);
x_418 = l_Lean_Syntax_node1(x_396, x_405, x_417);
x_419 = lean_mk_syntax_ident(x_389);
lean_inc(x_396);
x_420 = l_Lean_Syntax_node2(x_396, x_403, x_418, x_419);
x_421 = l_Lean_Syntax_node1(x_396, x_401, x_420);
x_16 = x_23;
x_17 = x_421;
x_18 = x_393;
goto block_22;
}
else
{
lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; 
x_422 = lean_ctor_get(x_391, 1);
lean_inc(x_422);
lean_dec(x_391);
x_423 = lean_ctor_get(x_6, 5);
lean_inc(x_423);
x_424 = l_Lean_SourceInfo_fromRef(x_423, x_30);
lean_dec(x_423);
x_425 = lean_mk_string_unchecked("Lean", 4, 4);
x_426 = lean_mk_string_unchecked("Parser", 6, 6);
x_427 = lean_mk_string_unchecked("Tactic", 6, 6);
x_428 = lean_mk_string_unchecked("grindParam", 10, 10);
lean_inc(x_427);
lean_inc(x_426);
lean_inc(x_425);
x_429 = l_Lean_Name_mkStr4(x_425, x_426, x_427, x_428);
x_430 = lean_mk_string_unchecked("grindLemma", 10, 10);
lean_inc(x_426);
lean_inc(x_425);
x_431 = l_Lean_Name_mkStr4(x_425, x_426, x_427, x_430);
x_432 = lean_mk_string_unchecked("null", 4, 4);
x_433 = l_Lean_Name_mkStr1(x_432);
x_434 = lean_mk_string_unchecked("Attr", 4, 4);
x_435 = lean_mk_string_unchecked("grindMod", 8, 8);
lean_inc(x_434);
lean_inc(x_426);
lean_inc(x_425);
x_436 = l_Lean_Name_mkStr4(x_425, x_426, x_434, x_435);
x_437 = lean_mk_string_unchecked("grindLR", 7, 7);
x_438 = l_Lean_Name_mkStr4(x_425, x_426, x_434, x_437);
x_439 = lean_mk_string_unchecked("token", 5, 5);
x_440 = lean_mk_string_unchecked("=> ", 3, 3);
x_441 = l_Lean_Name_mkStr2(x_439, x_440);
x_442 = lean_mk_string_unchecked("=>", 2, 2);
lean_inc(x_424);
x_443 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_443, 0, x_424);
lean_ctor_set(x_443, 1, x_442);
lean_inc(x_424);
x_444 = l_Lean_Syntax_node1(x_424, x_441, x_443);
lean_inc(x_424);
x_445 = l_Lean_Syntax_node1(x_424, x_438, x_444);
lean_inc(x_424);
x_446 = l_Lean_Syntax_node1(x_424, x_436, x_445);
lean_inc(x_424);
x_447 = l_Lean_Syntax_node1(x_424, x_433, x_446);
x_448 = lean_mk_syntax_ident(x_389);
lean_inc(x_424);
x_449 = l_Lean_Syntax_node2(x_424, x_431, x_447, x_448);
x_450 = l_Lean_Syntax_node1(x_424, x_429, x_449);
x_16 = x_23;
x_17 = x_450;
x_18 = x_422;
goto block_22;
}
}
case 7:
{
lean_object* x_451; lean_object* x_452; lean_object* x_453; uint8_t x_454; 
lean_free_object(x_31);
x_451 = lean_ctor_get(x_36, 0);
lean_inc(x_451);
x_452 = lean_ctor_get(x_36, 1);
lean_inc(x_452);
lean_dec(x_36);
x_453 = lean_st_ref_get(x_7, x_452);
x_454 = !lean_is_exclusive(x_453);
if (x_454 == 0)
{
lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; 
x_455 = lean_ctor_get(x_453, 1);
x_456 = lean_ctor_get(x_453, 0);
lean_dec(x_456);
x_457 = lean_ctor_get(x_6, 5);
lean_inc(x_457);
x_458 = l_Lean_SourceInfo_fromRef(x_457, x_30);
lean_dec(x_457);
x_459 = lean_mk_string_unchecked("Lean", 4, 4);
x_460 = lean_mk_string_unchecked("Parser", 6, 6);
x_461 = lean_mk_string_unchecked("Tactic", 6, 6);
x_462 = lean_mk_string_unchecked("grindParam", 10, 10);
lean_inc(x_461);
lean_inc(x_460);
lean_inc(x_459);
x_463 = l_Lean_Name_mkStr4(x_459, x_460, x_461, x_462);
x_464 = lean_mk_string_unchecked("grindLemma", 10, 10);
lean_inc(x_460);
lean_inc(x_459);
x_465 = l_Lean_Name_mkStr4(x_459, x_460, x_461, x_464);
x_466 = lean_mk_string_unchecked("null", 4, 4);
x_467 = l_Lean_Name_mkStr1(x_466);
x_468 = lean_mk_string_unchecked("Attr", 4, 4);
x_469 = lean_mk_string_unchecked("grindMod", 8, 8);
lean_inc(x_468);
lean_inc(x_460);
lean_inc(x_459);
x_470 = l_Lean_Name_mkStr4(x_459, x_460, x_468, x_469);
x_471 = lean_mk_string_unchecked("grindRL", 7, 7);
x_472 = l_Lean_Name_mkStr4(x_459, x_460, x_468, x_471);
x_473 = lean_mk_string_unchecked("token", 5, 5);
x_474 = lean_mk_string_unchecked("<= ", 3, 3);
x_475 = l_Lean_Name_mkStr2(x_473, x_474);
x_476 = lean_mk_string_unchecked("<=", 2, 2);
lean_inc(x_458);
lean_ctor_set_tag(x_453, 2);
lean_ctor_set(x_453, 1, x_476);
lean_ctor_set(x_453, 0, x_458);
lean_inc(x_458);
x_477 = l_Lean_Syntax_node1(x_458, x_475, x_453);
lean_inc(x_458);
x_478 = l_Lean_Syntax_node1(x_458, x_472, x_477);
lean_inc(x_458);
x_479 = l_Lean_Syntax_node1(x_458, x_470, x_478);
lean_inc(x_458);
x_480 = l_Lean_Syntax_node1(x_458, x_467, x_479);
x_481 = lean_mk_syntax_ident(x_451);
lean_inc(x_458);
x_482 = l_Lean_Syntax_node2(x_458, x_465, x_480, x_481);
x_483 = l_Lean_Syntax_node1(x_458, x_463, x_482);
x_16 = x_23;
x_17 = x_483;
x_18 = x_455;
goto block_22;
}
else
{
lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; 
x_484 = lean_ctor_get(x_453, 1);
lean_inc(x_484);
lean_dec(x_453);
x_485 = lean_ctor_get(x_6, 5);
lean_inc(x_485);
x_486 = l_Lean_SourceInfo_fromRef(x_485, x_30);
lean_dec(x_485);
x_487 = lean_mk_string_unchecked("Lean", 4, 4);
x_488 = lean_mk_string_unchecked("Parser", 6, 6);
x_489 = lean_mk_string_unchecked("Tactic", 6, 6);
x_490 = lean_mk_string_unchecked("grindParam", 10, 10);
lean_inc(x_489);
lean_inc(x_488);
lean_inc(x_487);
x_491 = l_Lean_Name_mkStr4(x_487, x_488, x_489, x_490);
x_492 = lean_mk_string_unchecked("grindLemma", 10, 10);
lean_inc(x_488);
lean_inc(x_487);
x_493 = l_Lean_Name_mkStr4(x_487, x_488, x_489, x_492);
x_494 = lean_mk_string_unchecked("null", 4, 4);
x_495 = l_Lean_Name_mkStr1(x_494);
x_496 = lean_mk_string_unchecked("Attr", 4, 4);
x_497 = lean_mk_string_unchecked("grindMod", 8, 8);
lean_inc(x_496);
lean_inc(x_488);
lean_inc(x_487);
x_498 = l_Lean_Name_mkStr4(x_487, x_488, x_496, x_497);
x_499 = lean_mk_string_unchecked("grindRL", 7, 7);
x_500 = l_Lean_Name_mkStr4(x_487, x_488, x_496, x_499);
x_501 = lean_mk_string_unchecked("token", 5, 5);
x_502 = lean_mk_string_unchecked("<= ", 3, 3);
x_503 = l_Lean_Name_mkStr2(x_501, x_502);
x_504 = lean_mk_string_unchecked("<=", 2, 2);
lean_inc(x_486);
x_505 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_505, 0, x_486);
lean_ctor_set(x_505, 1, x_504);
lean_inc(x_486);
x_506 = l_Lean_Syntax_node1(x_486, x_503, x_505);
lean_inc(x_486);
x_507 = l_Lean_Syntax_node1(x_486, x_500, x_506);
lean_inc(x_486);
x_508 = l_Lean_Syntax_node1(x_486, x_498, x_507);
lean_inc(x_486);
x_509 = l_Lean_Syntax_node1(x_486, x_495, x_508);
x_510 = lean_mk_syntax_ident(x_451);
lean_inc(x_486);
x_511 = l_Lean_Syntax_node2(x_486, x_493, x_509, x_510);
x_512 = l_Lean_Syntax_node1(x_486, x_491, x_511);
x_16 = x_23;
x_17 = x_512;
x_18 = x_484;
goto block_22;
}
}
case 8:
{
lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; 
lean_free_object(x_31);
x_513 = lean_ctor_get(x_36, 0);
lean_inc(x_513);
x_514 = lean_ctor_get(x_36, 1);
lean_inc(x_514);
lean_dec(x_36);
x_515 = lean_st_ref_get(x_7, x_514);
x_516 = lean_ctor_get(x_515, 1);
lean_inc(x_516);
lean_dec(x_515);
x_517 = lean_ctor_get(x_6, 5);
lean_inc(x_517);
x_518 = l_Lean_SourceInfo_fromRef(x_517, x_30);
lean_dec(x_517);
x_519 = lean_mk_string_unchecked("Lean", 4, 4);
x_520 = lean_mk_string_unchecked("Parser", 6, 6);
x_521 = lean_mk_string_unchecked("Tactic", 6, 6);
x_522 = lean_mk_string_unchecked("grindParam", 10, 10);
lean_inc(x_521);
lean_inc(x_520);
lean_inc(x_519);
x_523 = l_Lean_Name_mkStr4(x_519, x_520, x_521, x_522);
x_524 = lean_mk_string_unchecked("grindLemma", 10, 10);
x_525 = l_Lean_Name_mkStr4(x_519, x_520, x_521, x_524);
x_526 = lean_mk_string_unchecked("null", 4, 4);
x_527 = l_Lean_Name_mkStr1(x_526);
x_528 = l_Array_mkArray0(lean_box(0));
lean_inc(x_518);
x_529 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_529, 0, x_518);
lean_ctor_set(x_529, 1, x_527);
lean_ctor_set(x_529, 2, x_528);
x_530 = lean_mk_syntax_ident(x_513);
lean_inc(x_518);
x_531 = l_Lean_Syntax_node2(x_518, x_525, x_529, x_530);
x_532 = l_Lean_Syntax_node1(x_518, x_523, x_531);
x_16 = x_23;
x_17 = x_532;
x_18 = x_516;
goto block_22;
}
default: 
{
lean_object* x_533; lean_object* x_534; lean_object* x_535; uint8_t x_536; 
lean_free_object(x_31);
x_533 = lean_ctor_get(x_36, 0);
lean_inc(x_533);
x_534 = lean_ctor_get(x_36, 1);
lean_inc(x_534);
lean_dec(x_36);
x_535 = lean_st_ref_get(x_7, x_534);
x_536 = !lean_is_exclusive(x_535);
if (x_536 == 0)
{
lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; 
x_537 = lean_ctor_get(x_535, 1);
x_538 = lean_ctor_get(x_535, 0);
lean_dec(x_538);
x_539 = lean_ctor_get(x_6, 5);
lean_inc(x_539);
x_540 = l_Lean_SourceInfo_fromRef(x_539, x_30);
lean_dec(x_539);
x_541 = lean_mk_string_unchecked("Lean", 4, 4);
x_542 = lean_mk_string_unchecked("Parser", 6, 6);
x_543 = lean_mk_string_unchecked("Tactic", 6, 6);
x_544 = lean_mk_string_unchecked("grindParam", 10, 10);
lean_inc(x_543);
lean_inc(x_542);
lean_inc(x_541);
x_545 = l_Lean_Name_mkStr4(x_541, x_542, x_543, x_544);
x_546 = lean_mk_string_unchecked("grindLemma", 10, 10);
lean_inc(x_542);
lean_inc(x_541);
x_547 = l_Lean_Name_mkStr4(x_541, x_542, x_543, x_546);
x_548 = lean_mk_string_unchecked("null", 4, 4);
x_549 = l_Lean_Name_mkStr1(x_548);
x_550 = lean_mk_string_unchecked("Attr", 4, 4);
x_551 = lean_mk_string_unchecked("grindMod", 8, 8);
lean_inc(x_550);
lean_inc(x_542);
lean_inc(x_541);
x_552 = l_Lean_Name_mkStr4(x_541, x_542, x_550, x_551);
x_553 = lean_mk_string_unchecked("grindUsr", 8, 8);
x_554 = l_Lean_Name_mkStr4(x_541, x_542, x_550, x_553);
x_555 = lean_mk_string_unchecked("usr", 3, 3);
lean_inc(x_540);
lean_ctor_set_tag(x_535, 2);
lean_ctor_set(x_535, 1, x_555);
lean_ctor_set(x_535, 0, x_540);
lean_inc(x_540);
x_556 = l_Lean_Syntax_node1(x_540, x_554, x_535);
lean_inc(x_540);
x_557 = l_Lean_Syntax_node1(x_540, x_552, x_556);
lean_inc(x_540);
x_558 = l_Lean_Syntax_node1(x_540, x_549, x_557);
x_559 = lean_mk_syntax_ident(x_533);
lean_inc(x_540);
x_560 = l_Lean_Syntax_node2(x_540, x_547, x_558, x_559);
x_561 = l_Lean_Syntax_node1(x_540, x_545, x_560);
x_16 = x_23;
x_17 = x_561;
x_18 = x_537;
goto block_22;
}
else
{
lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; 
x_562 = lean_ctor_get(x_535, 1);
lean_inc(x_562);
lean_dec(x_535);
x_563 = lean_ctor_get(x_6, 5);
lean_inc(x_563);
x_564 = l_Lean_SourceInfo_fromRef(x_563, x_30);
lean_dec(x_563);
x_565 = lean_mk_string_unchecked("Lean", 4, 4);
x_566 = lean_mk_string_unchecked("Parser", 6, 6);
x_567 = lean_mk_string_unchecked("Tactic", 6, 6);
x_568 = lean_mk_string_unchecked("grindParam", 10, 10);
lean_inc(x_567);
lean_inc(x_566);
lean_inc(x_565);
x_569 = l_Lean_Name_mkStr4(x_565, x_566, x_567, x_568);
x_570 = lean_mk_string_unchecked("grindLemma", 10, 10);
lean_inc(x_566);
lean_inc(x_565);
x_571 = l_Lean_Name_mkStr4(x_565, x_566, x_567, x_570);
x_572 = lean_mk_string_unchecked("null", 4, 4);
x_573 = l_Lean_Name_mkStr1(x_572);
x_574 = lean_mk_string_unchecked("Attr", 4, 4);
x_575 = lean_mk_string_unchecked("grindMod", 8, 8);
lean_inc(x_574);
lean_inc(x_566);
lean_inc(x_565);
x_576 = l_Lean_Name_mkStr4(x_565, x_566, x_574, x_575);
x_577 = lean_mk_string_unchecked("grindUsr", 8, 8);
x_578 = l_Lean_Name_mkStr4(x_565, x_566, x_574, x_577);
x_579 = lean_mk_string_unchecked("usr", 3, 3);
lean_inc(x_564);
x_580 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_580, 0, x_564);
lean_ctor_set(x_580, 1, x_579);
lean_inc(x_564);
x_581 = l_Lean_Syntax_node1(x_564, x_578, x_580);
lean_inc(x_564);
x_582 = l_Lean_Syntax_node1(x_564, x_576, x_581);
lean_inc(x_564);
x_583 = l_Lean_Syntax_node1(x_564, x_573, x_582);
x_584 = lean_mk_syntax_ident(x_533);
lean_inc(x_564);
x_585 = l_Lean_Syntax_node2(x_564, x_571, x_583, x_584);
x_586 = l_Lean_Syntax_node1(x_564, x_569, x_585);
x_16 = x_23;
x_17 = x_586;
x_18 = x_562;
goto block_22;
}
}
}
}
else
{
uint8_t x_587; 
lean_free_object(x_31);
lean_dec(x_23);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_587 = !lean_is_exclusive(x_36);
if (x_587 == 0)
{
return x_36;
}
else
{
lean_object* x_588; lean_object* x_589; lean_object* x_590; 
x_588 = lean_ctor_get(x_36, 0);
x_589 = lean_ctor_get(x_36, 1);
lean_inc(x_589);
lean_inc(x_588);
lean_dec(x_36);
x_590 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_590, 0, x_588);
lean_ctor_set(x_590, 1, x_589);
return x_590;
}
}
}
else
{
lean_object* x_591; lean_object* x_592; 
x_591 = lean_ctor_get(x_31, 1);
lean_inc(x_591);
lean_dec(x_31);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_592 = l_Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0(x_24, x_30, x_4, x_5, x_6, x_7, x_591);
if (lean_obj_tag(x_592) == 0)
{
switch (x_14) {
case 0:
{
lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; 
x_593 = lean_ctor_get(x_592, 0);
lean_inc(x_593);
x_594 = lean_ctor_get(x_592, 1);
lean_inc(x_594);
lean_dec(x_592);
x_595 = lean_st_ref_get(x_7, x_594);
x_596 = lean_ctor_get(x_595, 1);
lean_inc(x_596);
if (lean_is_exclusive(x_595)) {
 lean_ctor_release(x_595, 0);
 lean_ctor_release(x_595, 1);
 x_597 = x_595;
} else {
 lean_dec_ref(x_595);
 x_597 = lean_box(0);
}
x_598 = lean_ctor_get(x_6, 5);
lean_inc(x_598);
x_599 = l_Lean_SourceInfo_fromRef(x_598, x_30);
lean_dec(x_598);
x_600 = lean_mk_string_unchecked("Lean", 4, 4);
x_601 = lean_mk_string_unchecked("Parser", 6, 6);
x_602 = lean_mk_string_unchecked("Tactic", 6, 6);
x_603 = lean_mk_string_unchecked("grindParam", 10, 10);
lean_inc(x_602);
lean_inc(x_601);
lean_inc(x_600);
x_604 = l_Lean_Name_mkStr4(x_600, x_601, x_602, x_603);
x_605 = lean_mk_string_unchecked("grindLemma", 10, 10);
lean_inc(x_601);
lean_inc(x_600);
x_606 = l_Lean_Name_mkStr4(x_600, x_601, x_602, x_605);
x_607 = lean_mk_string_unchecked("null", 4, 4);
x_608 = l_Lean_Name_mkStr1(x_607);
x_609 = lean_mk_string_unchecked("Attr", 4, 4);
x_610 = lean_mk_string_unchecked("grindMod", 8, 8);
lean_inc(x_609);
lean_inc(x_601);
lean_inc(x_600);
x_611 = l_Lean_Name_mkStr4(x_600, x_601, x_609, x_610);
x_612 = lean_mk_string_unchecked("grindEq", 7, 7);
x_613 = l_Lean_Name_mkStr4(x_600, x_601, x_609, x_612);
x_614 = lean_mk_string_unchecked("=", 1, 1);
lean_inc(x_599);
if (lean_is_scalar(x_597)) {
 x_615 = lean_alloc_ctor(2, 2, 0);
} else {
 x_615 = x_597;
 lean_ctor_set_tag(x_615, 2);
}
lean_ctor_set(x_615, 0, x_599);
lean_ctor_set(x_615, 1, x_614);
lean_inc(x_599);
x_616 = l_Lean_Syntax_node1(x_599, x_613, x_615);
lean_inc(x_599);
x_617 = l_Lean_Syntax_node1(x_599, x_611, x_616);
lean_inc(x_599);
x_618 = l_Lean_Syntax_node1(x_599, x_608, x_617);
x_619 = lean_mk_syntax_ident(x_593);
lean_inc(x_599);
x_620 = l_Lean_Syntax_node2(x_599, x_606, x_618, x_619);
x_621 = l_Lean_Syntax_node1(x_599, x_604, x_620);
x_16 = x_23;
x_17 = x_621;
x_18 = x_596;
goto block_22;
}
case 1:
{
lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; 
x_622 = lean_ctor_get(x_592, 0);
lean_inc(x_622);
x_623 = lean_ctor_get(x_592, 1);
lean_inc(x_623);
lean_dec(x_592);
x_624 = lean_st_ref_get(x_7, x_623);
x_625 = lean_ctor_get(x_624, 1);
lean_inc(x_625);
if (lean_is_exclusive(x_624)) {
 lean_ctor_release(x_624, 0);
 lean_ctor_release(x_624, 1);
 x_626 = x_624;
} else {
 lean_dec_ref(x_624);
 x_626 = lean_box(0);
}
x_627 = lean_ctor_get(x_6, 5);
lean_inc(x_627);
x_628 = l_Lean_SourceInfo_fromRef(x_627, x_30);
lean_dec(x_627);
x_629 = lean_mk_string_unchecked("Lean", 4, 4);
x_630 = lean_mk_string_unchecked("Parser", 6, 6);
x_631 = lean_mk_string_unchecked("Tactic", 6, 6);
x_632 = lean_mk_string_unchecked("grindParam", 10, 10);
lean_inc(x_631);
lean_inc(x_630);
lean_inc(x_629);
x_633 = l_Lean_Name_mkStr4(x_629, x_630, x_631, x_632);
x_634 = lean_mk_string_unchecked("grindLemma", 10, 10);
lean_inc(x_630);
lean_inc(x_629);
x_635 = l_Lean_Name_mkStr4(x_629, x_630, x_631, x_634);
x_636 = lean_mk_string_unchecked("null", 4, 4);
x_637 = l_Lean_Name_mkStr1(x_636);
x_638 = lean_mk_string_unchecked("Attr", 4, 4);
x_639 = lean_mk_string_unchecked("grindMod", 8, 8);
lean_inc(x_638);
lean_inc(x_630);
lean_inc(x_629);
x_640 = l_Lean_Name_mkStr4(x_629, x_630, x_638, x_639);
x_641 = lean_mk_string_unchecked("grindEqRhs", 10, 10);
x_642 = l_Lean_Name_mkStr4(x_629, x_630, x_638, x_641);
x_643 = lean_mk_string_unchecked("=", 1, 1);
lean_inc(x_628);
if (lean_is_scalar(x_626)) {
 x_644 = lean_alloc_ctor(2, 2, 0);
} else {
 x_644 = x_626;
 lean_ctor_set_tag(x_644, 2);
}
lean_ctor_set(x_644, 0, x_628);
lean_ctor_set(x_644, 1, x_643);
x_645 = lean_mk_string_unchecked("_", 1, 1);
lean_inc(x_628);
x_646 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_646, 0, x_628);
lean_ctor_set(x_646, 1, x_645);
lean_inc(x_628);
x_647 = l_Lean_Syntax_node2(x_628, x_642, x_644, x_646);
lean_inc(x_628);
x_648 = l_Lean_Syntax_node1(x_628, x_640, x_647);
lean_inc(x_628);
x_649 = l_Lean_Syntax_node1(x_628, x_637, x_648);
x_650 = lean_mk_syntax_ident(x_622);
lean_inc(x_628);
x_651 = l_Lean_Syntax_node2(x_628, x_635, x_649, x_650);
x_652 = l_Lean_Syntax_node1(x_628, x_633, x_651);
x_16 = x_23;
x_17 = x_652;
x_18 = x_625;
goto block_22;
}
case 2:
{
lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; 
x_653 = lean_ctor_get(x_592, 0);
lean_inc(x_653);
x_654 = lean_ctor_get(x_592, 1);
lean_inc(x_654);
lean_dec(x_592);
x_655 = lean_st_ref_get(x_7, x_654);
x_656 = lean_ctor_get(x_655, 1);
lean_inc(x_656);
if (lean_is_exclusive(x_655)) {
 lean_ctor_release(x_655, 0);
 lean_ctor_release(x_655, 1);
 x_657 = x_655;
} else {
 lean_dec_ref(x_655);
 x_657 = lean_box(0);
}
x_658 = lean_ctor_get(x_6, 5);
lean_inc(x_658);
x_659 = l_Lean_SourceInfo_fromRef(x_658, x_30);
lean_dec(x_658);
x_660 = lean_mk_string_unchecked("Lean", 4, 4);
x_661 = lean_mk_string_unchecked("Parser", 6, 6);
x_662 = lean_mk_string_unchecked("Tactic", 6, 6);
x_663 = lean_mk_string_unchecked("grindParam", 10, 10);
lean_inc(x_662);
lean_inc(x_661);
lean_inc(x_660);
x_664 = l_Lean_Name_mkStr4(x_660, x_661, x_662, x_663);
x_665 = lean_mk_string_unchecked("grindLemma", 10, 10);
lean_inc(x_661);
lean_inc(x_660);
x_666 = l_Lean_Name_mkStr4(x_660, x_661, x_662, x_665);
x_667 = lean_mk_string_unchecked("null", 4, 4);
x_668 = l_Lean_Name_mkStr1(x_667);
x_669 = lean_mk_string_unchecked("Attr", 4, 4);
x_670 = lean_mk_string_unchecked("grindMod", 8, 8);
lean_inc(x_669);
lean_inc(x_661);
lean_inc(x_660);
x_671 = l_Lean_Name_mkStr4(x_660, x_661, x_669, x_670);
x_672 = lean_mk_string_unchecked("grindEqBoth", 11, 11);
x_673 = l_Lean_Name_mkStr4(x_660, x_661, x_669, x_672);
x_674 = lean_mk_string_unchecked("_", 1, 1);
lean_inc(x_659);
if (lean_is_scalar(x_657)) {
 x_675 = lean_alloc_ctor(2, 2, 0);
} else {
 x_675 = x_657;
 lean_ctor_set_tag(x_675, 2);
}
lean_ctor_set(x_675, 0, x_659);
lean_ctor_set(x_675, 1, x_674);
x_676 = lean_mk_string_unchecked("=", 1, 1);
lean_inc(x_659);
x_677 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_677, 0, x_659);
lean_ctor_set(x_677, 1, x_676);
lean_inc(x_675);
lean_inc(x_659);
x_678 = l_Lean_Syntax_node3(x_659, x_673, x_675, x_677, x_675);
lean_inc(x_659);
x_679 = l_Lean_Syntax_node1(x_659, x_671, x_678);
lean_inc(x_659);
x_680 = l_Lean_Syntax_node1(x_659, x_668, x_679);
x_681 = lean_mk_syntax_ident(x_653);
lean_inc(x_659);
x_682 = l_Lean_Syntax_node2(x_659, x_666, x_680, x_681);
x_683 = l_Lean_Syntax_node1(x_659, x_664, x_682);
x_16 = x_23;
x_17 = x_683;
x_18 = x_656;
goto block_22;
}
case 3:
{
lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; 
x_684 = lean_ctor_get(x_592, 0);
lean_inc(x_684);
x_685 = lean_ctor_get(x_592, 1);
lean_inc(x_685);
lean_dec(x_592);
x_686 = lean_st_ref_get(x_7, x_685);
x_687 = lean_ctor_get(x_686, 1);
lean_inc(x_687);
if (lean_is_exclusive(x_686)) {
 lean_ctor_release(x_686, 0);
 lean_ctor_release(x_686, 1);
 x_688 = x_686;
} else {
 lean_dec_ref(x_686);
 x_688 = lean_box(0);
}
x_689 = lean_ctor_get(x_6, 5);
lean_inc(x_689);
x_690 = l_Lean_SourceInfo_fromRef(x_689, x_30);
lean_dec(x_689);
x_691 = lean_mk_string_unchecked("Lean", 4, 4);
x_692 = lean_mk_string_unchecked("Parser", 6, 6);
x_693 = lean_mk_string_unchecked("Tactic", 6, 6);
x_694 = lean_mk_string_unchecked("grindParam", 10, 10);
lean_inc(x_693);
lean_inc(x_692);
lean_inc(x_691);
x_695 = l_Lean_Name_mkStr4(x_691, x_692, x_693, x_694);
x_696 = lean_mk_string_unchecked("grindLemma", 10, 10);
lean_inc(x_692);
lean_inc(x_691);
x_697 = l_Lean_Name_mkStr4(x_691, x_692, x_693, x_696);
x_698 = lean_mk_string_unchecked("null", 4, 4);
x_699 = l_Lean_Name_mkStr1(x_698);
x_700 = lean_mk_string_unchecked("Attr", 4, 4);
x_701 = lean_mk_string_unchecked("grindMod", 8, 8);
lean_inc(x_700);
lean_inc(x_692);
lean_inc(x_691);
x_702 = l_Lean_Name_mkStr4(x_691, x_692, x_700, x_701);
x_703 = lean_mk_string_unchecked("grindEqBwd", 10, 10);
x_704 = l_Lean_Name_mkStr4(x_691, x_692, x_700, x_703);
x_705 = lean_mk_string_unchecked("group", 5, 5);
x_706 = l_Lean_Name_mkStr1(x_705);
x_707 = lean_mk_string_unchecked("←", 3, 1);
lean_inc(x_690);
if (lean_is_scalar(x_688)) {
 x_708 = lean_alloc_ctor(2, 2, 0);
} else {
 x_708 = x_688;
 lean_ctor_set_tag(x_708, 2);
}
lean_ctor_set(x_708, 0, x_690);
lean_ctor_set(x_708, 1, x_707);
x_709 = lean_mk_string_unchecked("=", 1, 1);
lean_inc(x_690);
x_710 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_710, 0, x_690);
lean_ctor_set(x_710, 1, x_709);
lean_inc(x_690);
x_711 = l_Lean_Syntax_node2(x_690, x_706, x_708, x_710);
lean_inc(x_690);
x_712 = l_Lean_Syntax_node1(x_690, x_704, x_711);
lean_inc(x_690);
x_713 = l_Lean_Syntax_node1(x_690, x_702, x_712);
lean_inc(x_690);
x_714 = l_Lean_Syntax_node1(x_690, x_699, x_713);
x_715 = lean_mk_syntax_ident(x_684);
lean_inc(x_690);
x_716 = l_Lean_Syntax_node2(x_690, x_697, x_714, x_715);
x_717 = l_Lean_Syntax_node1(x_690, x_695, x_716);
x_16 = x_23;
x_17 = x_717;
x_18 = x_687;
goto block_22;
}
case 4:
{
lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; 
x_718 = lean_ctor_get(x_592, 0);
lean_inc(x_718);
x_719 = lean_ctor_get(x_592, 1);
lean_inc(x_719);
lean_dec(x_592);
x_720 = lean_st_ref_get(x_7, x_719);
x_721 = lean_ctor_get(x_720, 1);
lean_inc(x_721);
if (lean_is_exclusive(x_720)) {
 lean_ctor_release(x_720, 0);
 lean_ctor_release(x_720, 1);
 x_722 = x_720;
} else {
 lean_dec_ref(x_720);
 x_722 = lean_box(0);
}
x_723 = lean_ctor_get(x_6, 5);
lean_inc(x_723);
x_724 = l_Lean_SourceInfo_fromRef(x_723, x_30);
lean_dec(x_723);
x_725 = lean_mk_string_unchecked("Lean", 4, 4);
x_726 = lean_mk_string_unchecked("Parser", 6, 6);
x_727 = lean_mk_string_unchecked("Tactic", 6, 6);
x_728 = lean_mk_string_unchecked("grindParam", 10, 10);
lean_inc(x_727);
lean_inc(x_726);
lean_inc(x_725);
x_729 = l_Lean_Name_mkStr4(x_725, x_726, x_727, x_728);
x_730 = lean_mk_string_unchecked("grindLemma", 10, 10);
lean_inc(x_726);
lean_inc(x_725);
x_731 = l_Lean_Name_mkStr4(x_725, x_726, x_727, x_730);
x_732 = lean_mk_string_unchecked("null", 4, 4);
x_733 = l_Lean_Name_mkStr1(x_732);
x_734 = lean_mk_string_unchecked("Attr", 4, 4);
x_735 = lean_mk_string_unchecked("grindMod", 8, 8);
lean_inc(x_734);
lean_inc(x_726);
lean_inc(x_725);
x_736 = l_Lean_Name_mkStr4(x_725, x_726, x_734, x_735);
x_737 = lean_mk_string_unchecked("grindFwd", 8, 8);
x_738 = l_Lean_Name_mkStr4(x_725, x_726, x_734, x_737);
x_739 = lean_mk_string_unchecked("token", 5, 5);
x_740 = lean_mk_string_unchecked("→ ", 4, 2);
x_741 = l_Lean_Name_mkStr2(x_739, x_740);
x_742 = lean_mk_string_unchecked("→", 3, 1);
lean_inc(x_724);
if (lean_is_scalar(x_722)) {
 x_743 = lean_alloc_ctor(2, 2, 0);
} else {
 x_743 = x_722;
 lean_ctor_set_tag(x_743, 2);
}
lean_ctor_set(x_743, 0, x_724);
lean_ctor_set(x_743, 1, x_742);
lean_inc(x_724);
x_744 = l_Lean_Syntax_node1(x_724, x_741, x_743);
lean_inc(x_724);
x_745 = l_Lean_Syntax_node1(x_724, x_738, x_744);
lean_inc(x_724);
x_746 = l_Lean_Syntax_node1(x_724, x_736, x_745);
lean_inc(x_724);
x_747 = l_Lean_Syntax_node1(x_724, x_733, x_746);
x_748 = lean_mk_syntax_ident(x_718);
lean_inc(x_724);
x_749 = l_Lean_Syntax_node2(x_724, x_731, x_747, x_748);
x_750 = l_Lean_Syntax_node1(x_724, x_729, x_749);
x_16 = x_23;
x_17 = x_750;
x_18 = x_721;
goto block_22;
}
case 5:
{
lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; 
x_751 = lean_ctor_get(x_592, 0);
lean_inc(x_751);
x_752 = lean_ctor_get(x_592, 1);
lean_inc(x_752);
lean_dec(x_592);
x_753 = lean_st_ref_get(x_7, x_752);
x_754 = lean_ctor_get(x_753, 1);
lean_inc(x_754);
if (lean_is_exclusive(x_753)) {
 lean_ctor_release(x_753, 0);
 lean_ctor_release(x_753, 1);
 x_755 = x_753;
} else {
 lean_dec_ref(x_753);
 x_755 = lean_box(0);
}
x_756 = lean_ctor_get(x_6, 5);
lean_inc(x_756);
x_757 = l_Lean_SourceInfo_fromRef(x_756, x_30);
lean_dec(x_756);
x_758 = lean_mk_string_unchecked("Lean", 4, 4);
x_759 = lean_mk_string_unchecked("Parser", 6, 6);
x_760 = lean_mk_string_unchecked("Tactic", 6, 6);
x_761 = lean_mk_string_unchecked("grindParam", 10, 10);
lean_inc(x_760);
lean_inc(x_759);
lean_inc(x_758);
x_762 = l_Lean_Name_mkStr4(x_758, x_759, x_760, x_761);
x_763 = lean_mk_string_unchecked("grindLemma", 10, 10);
lean_inc(x_759);
lean_inc(x_758);
x_764 = l_Lean_Name_mkStr4(x_758, x_759, x_760, x_763);
x_765 = lean_mk_string_unchecked("null", 4, 4);
x_766 = l_Lean_Name_mkStr1(x_765);
x_767 = lean_mk_string_unchecked("Attr", 4, 4);
x_768 = lean_mk_string_unchecked("grindMod", 8, 8);
lean_inc(x_767);
lean_inc(x_759);
lean_inc(x_758);
x_769 = l_Lean_Name_mkStr4(x_758, x_759, x_767, x_768);
x_770 = lean_mk_string_unchecked("grindBwd", 8, 8);
x_771 = l_Lean_Name_mkStr4(x_758, x_759, x_767, x_770);
x_772 = lean_mk_string_unchecked("token", 5, 5);
x_773 = lean_mk_string_unchecked("← ", 4, 2);
x_774 = l_Lean_Name_mkStr2(x_772, x_773);
x_775 = lean_mk_string_unchecked("←", 3, 1);
lean_inc(x_757);
if (lean_is_scalar(x_755)) {
 x_776 = lean_alloc_ctor(2, 2, 0);
} else {
 x_776 = x_755;
 lean_ctor_set_tag(x_776, 2);
}
lean_ctor_set(x_776, 0, x_757);
lean_ctor_set(x_776, 1, x_775);
lean_inc(x_757);
x_777 = l_Lean_Syntax_node1(x_757, x_774, x_776);
lean_inc(x_757);
x_778 = l_Lean_Syntax_node1(x_757, x_771, x_777);
lean_inc(x_757);
x_779 = l_Lean_Syntax_node1(x_757, x_769, x_778);
lean_inc(x_757);
x_780 = l_Lean_Syntax_node1(x_757, x_766, x_779);
x_781 = lean_mk_syntax_ident(x_751);
lean_inc(x_757);
x_782 = l_Lean_Syntax_node2(x_757, x_764, x_780, x_781);
x_783 = l_Lean_Syntax_node1(x_757, x_762, x_782);
x_16 = x_23;
x_17 = x_783;
x_18 = x_754;
goto block_22;
}
case 6:
{
lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; 
x_784 = lean_ctor_get(x_592, 0);
lean_inc(x_784);
x_785 = lean_ctor_get(x_592, 1);
lean_inc(x_785);
lean_dec(x_592);
x_786 = lean_st_ref_get(x_7, x_785);
x_787 = lean_ctor_get(x_786, 1);
lean_inc(x_787);
if (lean_is_exclusive(x_786)) {
 lean_ctor_release(x_786, 0);
 lean_ctor_release(x_786, 1);
 x_788 = x_786;
} else {
 lean_dec_ref(x_786);
 x_788 = lean_box(0);
}
x_789 = lean_ctor_get(x_6, 5);
lean_inc(x_789);
x_790 = l_Lean_SourceInfo_fromRef(x_789, x_30);
lean_dec(x_789);
x_791 = lean_mk_string_unchecked("Lean", 4, 4);
x_792 = lean_mk_string_unchecked("Parser", 6, 6);
x_793 = lean_mk_string_unchecked("Tactic", 6, 6);
x_794 = lean_mk_string_unchecked("grindParam", 10, 10);
lean_inc(x_793);
lean_inc(x_792);
lean_inc(x_791);
x_795 = l_Lean_Name_mkStr4(x_791, x_792, x_793, x_794);
x_796 = lean_mk_string_unchecked("grindLemma", 10, 10);
lean_inc(x_792);
lean_inc(x_791);
x_797 = l_Lean_Name_mkStr4(x_791, x_792, x_793, x_796);
x_798 = lean_mk_string_unchecked("null", 4, 4);
x_799 = l_Lean_Name_mkStr1(x_798);
x_800 = lean_mk_string_unchecked("Attr", 4, 4);
x_801 = lean_mk_string_unchecked("grindMod", 8, 8);
lean_inc(x_800);
lean_inc(x_792);
lean_inc(x_791);
x_802 = l_Lean_Name_mkStr4(x_791, x_792, x_800, x_801);
x_803 = lean_mk_string_unchecked("grindLR", 7, 7);
x_804 = l_Lean_Name_mkStr4(x_791, x_792, x_800, x_803);
x_805 = lean_mk_string_unchecked("token", 5, 5);
x_806 = lean_mk_string_unchecked("=> ", 3, 3);
x_807 = l_Lean_Name_mkStr2(x_805, x_806);
x_808 = lean_mk_string_unchecked("=>", 2, 2);
lean_inc(x_790);
if (lean_is_scalar(x_788)) {
 x_809 = lean_alloc_ctor(2, 2, 0);
} else {
 x_809 = x_788;
 lean_ctor_set_tag(x_809, 2);
}
lean_ctor_set(x_809, 0, x_790);
lean_ctor_set(x_809, 1, x_808);
lean_inc(x_790);
x_810 = l_Lean_Syntax_node1(x_790, x_807, x_809);
lean_inc(x_790);
x_811 = l_Lean_Syntax_node1(x_790, x_804, x_810);
lean_inc(x_790);
x_812 = l_Lean_Syntax_node1(x_790, x_802, x_811);
lean_inc(x_790);
x_813 = l_Lean_Syntax_node1(x_790, x_799, x_812);
x_814 = lean_mk_syntax_ident(x_784);
lean_inc(x_790);
x_815 = l_Lean_Syntax_node2(x_790, x_797, x_813, x_814);
x_816 = l_Lean_Syntax_node1(x_790, x_795, x_815);
x_16 = x_23;
x_17 = x_816;
x_18 = x_787;
goto block_22;
}
case 7:
{
lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; lean_object* x_822; lean_object* x_823; lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; lean_object* x_834; lean_object* x_835; lean_object* x_836; lean_object* x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; lean_object* x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; lean_object* x_849; 
x_817 = lean_ctor_get(x_592, 0);
lean_inc(x_817);
x_818 = lean_ctor_get(x_592, 1);
lean_inc(x_818);
lean_dec(x_592);
x_819 = lean_st_ref_get(x_7, x_818);
x_820 = lean_ctor_get(x_819, 1);
lean_inc(x_820);
if (lean_is_exclusive(x_819)) {
 lean_ctor_release(x_819, 0);
 lean_ctor_release(x_819, 1);
 x_821 = x_819;
} else {
 lean_dec_ref(x_819);
 x_821 = lean_box(0);
}
x_822 = lean_ctor_get(x_6, 5);
lean_inc(x_822);
x_823 = l_Lean_SourceInfo_fromRef(x_822, x_30);
lean_dec(x_822);
x_824 = lean_mk_string_unchecked("Lean", 4, 4);
x_825 = lean_mk_string_unchecked("Parser", 6, 6);
x_826 = lean_mk_string_unchecked("Tactic", 6, 6);
x_827 = lean_mk_string_unchecked("grindParam", 10, 10);
lean_inc(x_826);
lean_inc(x_825);
lean_inc(x_824);
x_828 = l_Lean_Name_mkStr4(x_824, x_825, x_826, x_827);
x_829 = lean_mk_string_unchecked("grindLemma", 10, 10);
lean_inc(x_825);
lean_inc(x_824);
x_830 = l_Lean_Name_mkStr4(x_824, x_825, x_826, x_829);
x_831 = lean_mk_string_unchecked("null", 4, 4);
x_832 = l_Lean_Name_mkStr1(x_831);
x_833 = lean_mk_string_unchecked("Attr", 4, 4);
x_834 = lean_mk_string_unchecked("grindMod", 8, 8);
lean_inc(x_833);
lean_inc(x_825);
lean_inc(x_824);
x_835 = l_Lean_Name_mkStr4(x_824, x_825, x_833, x_834);
x_836 = lean_mk_string_unchecked("grindRL", 7, 7);
x_837 = l_Lean_Name_mkStr4(x_824, x_825, x_833, x_836);
x_838 = lean_mk_string_unchecked("token", 5, 5);
x_839 = lean_mk_string_unchecked("<= ", 3, 3);
x_840 = l_Lean_Name_mkStr2(x_838, x_839);
x_841 = lean_mk_string_unchecked("<=", 2, 2);
lean_inc(x_823);
if (lean_is_scalar(x_821)) {
 x_842 = lean_alloc_ctor(2, 2, 0);
} else {
 x_842 = x_821;
 lean_ctor_set_tag(x_842, 2);
}
lean_ctor_set(x_842, 0, x_823);
lean_ctor_set(x_842, 1, x_841);
lean_inc(x_823);
x_843 = l_Lean_Syntax_node1(x_823, x_840, x_842);
lean_inc(x_823);
x_844 = l_Lean_Syntax_node1(x_823, x_837, x_843);
lean_inc(x_823);
x_845 = l_Lean_Syntax_node1(x_823, x_835, x_844);
lean_inc(x_823);
x_846 = l_Lean_Syntax_node1(x_823, x_832, x_845);
x_847 = lean_mk_syntax_ident(x_817);
lean_inc(x_823);
x_848 = l_Lean_Syntax_node2(x_823, x_830, x_846, x_847);
x_849 = l_Lean_Syntax_node1(x_823, x_828, x_848);
x_16 = x_23;
x_17 = x_849;
x_18 = x_820;
goto block_22;
}
case 8:
{
lean_object* x_850; lean_object* x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; lean_object* x_864; lean_object* x_865; lean_object* x_866; lean_object* x_867; lean_object* x_868; lean_object* x_869; 
x_850 = lean_ctor_get(x_592, 0);
lean_inc(x_850);
x_851 = lean_ctor_get(x_592, 1);
lean_inc(x_851);
lean_dec(x_592);
x_852 = lean_st_ref_get(x_7, x_851);
x_853 = lean_ctor_get(x_852, 1);
lean_inc(x_853);
lean_dec(x_852);
x_854 = lean_ctor_get(x_6, 5);
lean_inc(x_854);
x_855 = l_Lean_SourceInfo_fromRef(x_854, x_30);
lean_dec(x_854);
x_856 = lean_mk_string_unchecked("Lean", 4, 4);
x_857 = lean_mk_string_unchecked("Parser", 6, 6);
x_858 = lean_mk_string_unchecked("Tactic", 6, 6);
x_859 = lean_mk_string_unchecked("grindParam", 10, 10);
lean_inc(x_858);
lean_inc(x_857);
lean_inc(x_856);
x_860 = l_Lean_Name_mkStr4(x_856, x_857, x_858, x_859);
x_861 = lean_mk_string_unchecked("grindLemma", 10, 10);
x_862 = l_Lean_Name_mkStr4(x_856, x_857, x_858, x_861);
x_863 = lean_mk_string_unchecked("null", 4, 4);
x_864 = l_Lean_Name_mkStr1(x_863);
x_865 = l_Array_mkArray0(lean_box(0));
lean_inc(x_855);
x_866 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_866, 0, x_855);
lean_ctor_set(x_866, 1, x_864);
lean_ctor_set(x_866, 2, x_865);
x_867 = lean_mk_syntax_ident(x_850);
lean_inc(x_855);
x_868 = l_Lean_Syntax_node2(x_855, x_862, x_866, x_867);
x_869 = l_Lean_Syntax_node1(x_855, x_860, x_868);
x_16 = x_23;
x_17 = x_869;
x_18 = x_853;
goto block_22;
}
default: 
{
lean_object* x_870; lean_object* x_871; lean_object* x_872; lean_object* x_873; lean_object* x_874; lean_object* x_875; lean_object* x_876; lean_object* x_877; lean_object* x_878; lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; lean_object* x_884; lean_object* x_885; lean_object* x_886; lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; lean_object* x_891; lean_object* x_892; lean_object* x_893; lean_object* x_894; lean_object* x_895; lean_object* x_896; lean_object* x_897; lean_object* x_898; 
x_870 = lean_ctor_get(x_592, 0);
lean_inc(x_870);
x_871 = lean_ctor_get(x_592, 1);
lean_inc(x_871);
lean_dec(x_592);
x_872 = lean_st_ref_get(x_7, x_871);
x_873 = lean_ctor_get(x_872, 1);
lean_inc(x_873);
if (lean_is_exclusive(x_872)) {
 lean_ctor_release(x_872, 0);
 lean_ctor_release(x_872, 1);
 x_874 = x_872;
} else {
 lean_dec_ref(x_872);
 x_874 = lean_box(0);
}
x_875 = lean_ctor_get(x_6, 5);
lean_inc(x_875);
x_876 = l_Lean_SourceInfo_fromRef(x_875, x_30);
lean_dec(x_875);
x_877 = lean_mk_string_unchecked("Lean", 4, 4);
x_878 = lean_mk_string_unchecked("Parser", 6, 6);
x_879 = lean_mk_string_unchecked("Tactic", 6, 6);
x_880 = lean_mk_string_unchecked("grindParam", 10, 10);
lean_inc(x_879);
lean_inc(x_878);
lean_inc(x_877);
x_881 = l_Lean_Name_mkStr4(x_877, x_878, x_879, x_880);
x_882 = lean_mk_string_unchecked("grindLemma", 10, 10);
lean_inc(x_878);
lean_inc(x_877);
x_883 = l_Lean_Name_mkStr4(x_877, x_878, x_879, x_882);
x_884 = lean_mk_string_unchecked("null", 4, 4);
x_885 = l_Lean_Name_mkStr1(x_884);
x_886 = lean_mk_string_unchecked("Attr", 4, 4);
x_887 = lean_mk_string_unchecked("grindMod", 8, 8);
lean_inc(x_886);
lean_inc(x_878);
lean_inc(x_877);
x_888 = l_Lean_Name_mkStr4(x_877, x_878, x_886, x_887);
x_889 = lean_mk_string_unchecked("grindUsr", 8, 8);
x_890 = l_Lean_Name_mkStr4(x_877, x_878, x_886, x_889);
x_891 = lean_mk_string_unchecked("usr", 3, 3);
lean_inc(x_876);
if (lean_is_scalar(x_874)) {
 x_892 = lean_alloc_ctor(2, 2, 0);
} else {
 x_892 = x_874;
 lean_ctor_set_tag(x_892, 2);
}
lean_ctor_set(x_892, 0, x_876);
lean_ctor_set(x_892, 1, x_891);
lean_inc(x_876);
x_893 = l_Lean_Syntax_node1(x_876, x_890, x_892);
lean_inc(x_876);
x_894 = l_Lean_Syntax_node1(x_876, x_888, x_893);
lean_inc(x_876);
x_895 = l_Lean_Syntax_node1(x_876, x_885, x_894);
x_896 = lean_mk_syntax_ident(x_870);
lean_inc(x_876);
x_897 = l_Lean_Syntax_node2(x_876, x_883, x_895, x_896);
x_898 = l_Lean_Syntax_node1(x_876, x_881, x_897);
x_16 = x_23;
x_17 = x_898;
x_18 = x_873;
goto block_22;
}
}
}
else
{
lean_object* x_899; lean_object* x_900; lean_object* x_901; lean_object* x_902; 
lean_dec(x_23);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_899 = lean_ctor_get(x_592, 0);
lean_inc(x_899);
x_900 = lean_ctor_get(x_592, 1);
lean_inc(x_900);
if (lean_is_exclusive(x_592)) {
 lean_ctor_release(x_592, 0);
 lean_ctor_release(x_592, 1);
 x_901 = x_592;
} else {
 lean_dec_ref(x_592);
 x_901 = lean_box(0);
}
if (lean_is_scalar(x_901)) {
 x_902 = lean_alloc_ctor(1, 2, 0);
} else {
 x_902 = x_901;
}
lean_ctor_set(x_902, 0, x_899);
lean_ctor_set(x_902, 1, x_900);
return x_902;
}
}
}
else
{
uint8_t x_903; 
lean_dec(x_24);
lean_dec(x_12);
x_903 = !lean_is_exclusive(x_31);
if (x_903 == 0)
{
lean_object* x_904; lean_object* x_905; lean_object* x_906; uint8_t x_907; 
x_904 = lean_ctor_get(x_31, 1);
x_905 = lean_ctor_get(x_31, 0);
lean_dec(x_905);
x_906 = lean_ctor_get(x_32, 0);
lean_inc(x_906);
lean_dec(x_32);
x_907 = l_Lean_NameSet_contains(x_15, x_906);
if (x_907 == 0)
{
lean_object* x_908; 
lean_free_object(x_31);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_906);
x_908 = l_Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0(x_906, x_907, x_4, x_5, x_6, x_7, x_904);
if (lean_obj_tag(x_908) == 0)
{
lean_object* x_909; lean_object* x_910; lean_object* x_911; uint8_t x_912; 
x_909 = lean_ctor_get(x_908, 0);
lean_inc(x_909);
x_910 = lean_ctor_get(x_908, 1);
lean_inc(x_910);
lean_dec(x_908);
x_911 = lean_st_ref_get(x_7, x_910);
x_912 = !lean_is_exclusive(x_911);
if (x_912 == 0)
{
lean_object* x_913; lean_object* x_914; lean_object* x_915; lean_object* x_916; lean_object* x_917; lean_object* x_918; lean_object* x_919; lean_object* x_920; lean_object* x_921; lean_object* x_922; lean_object* x_923; lean_object* x_924; lean_object* x_925; lean_object* x_926; lean_object* x_927; lean_object* x_928; lean_object* x_929; lean_object* x_930; lean_object* x_931; lean_object* x_932; lean_object* x_933; 
x_913 = lean_ctor_get(x_911, 1);
x_914 = lean_ctor_get(x_911, 0);
lean_dec(x_914);
x_915 = lean_ctor_get(x_6, 5);
lean_inc(x_915);
x_916 = l_Lean_NameSet_insert(x_15, x_906);
x_917 = l_Lean_SourceInfo_fromRef(x_915, x_907);
lean_dec(x_915);
x_918 = lean_mk_string_unchecked("Lean", 4, 4);
x_919 = lean_mk_string_unchecked("Parser", 6, 6);
x_920 = lean_mk_string_unchecked("Tactic", 6, 6);
x_921 = lean_mk_string_unchecked("grindParam", 10, 10);
lean_inc(x_920);
lean_inc(x_919);
lean_inc(x_918);
x_922 = l_Lean_Name_mkStr4(x_918, x_919, x_920, x_921);
x_923 = lean_mk_string_unchecked("grindLemma", 10, 10);
x_924 = l_Lean_Name_mkStr4(x_918, x_919, x_920, x_923);
x_925 = lean_mk_string_unchecked("null", 4, 4);
x_926 = l_Lean_Name_mkStr1(x_925);
x_927 = l_Array_mkArray0(lean_box(0));
lean_inc(x_917);
x_928 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_928, 0, x_917);
lean_ctor_set(x_928, 1, x_926);
lean_ctor_set(x_928, 2, x_927);
x_929 = lean_mk_syntax_ident(x_909);
lean_inc(x_917);
x_930 = l_Lean_Syntax_node2(x_917, x_924, x_928, x_929);
x_931 = l_Lean_Syntax_node1(x_917, x_922, x_930);
x_932 = lean_array_push(x_23, x_931);
lean_ctor_set(x_911, 1, x_932);
lean_ctor_set(x_911, 0, x_916);
x_933 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Tactic_mkGrindOnly_spec__3_spec__3___redArg(x_11, x_911, x_4, x_5, x_6, x_7, x_913);
return x_933;
}
else
{
lean_object* x_934; lean_object* x_935; lean_object* x_936; lean_object* x_937; lean_object* x_938; lean_object* x_939; lean_object* x_940; lean_object* x_941; lean_object* x_942; lean_object* x_943; lean_object* x_944; lean_object* x_945; lean_object* x_946; lean_object* x_947; lean_object* x_948; lean_object* x_949; lean_object* x_950; lean_object* x_951; lean_object* x_952; lean_object* x_953; lean_object* x_954; 
x_934 = lean_ctor_get(x_911, 1);
lean_inc(x_934);
lean_dec(x_911);
x_935 = lean_ctor_get(x_6, 5);
lean_inc(x_935);
x_936 = l_Lean_NameSet_insert(x_15, x_906);
x_937 = l_Lean_SourceInfo_fromRef(x_935, x_907);
lean_dec(x_935);
x_938 = lean_mk_string_unchecked("Lean", 4, 4);
x_939 = lean_mk_string_unchecked("Parser", 6, 6);
x_940 = lean_mk_string_unchecked("Tactic", 6, 6);
x_941 = lean_mk_string_unchecked("grindParam", 10, 10);
lean_inc(x_940);
lean_inc(x_939);
lean_inc(x_938);
x_942 = l_Lean_Name_mkStr4(x_938, x_939, x_940, x_941);
x_943 = lean_mk_string_unchecked("grindLemma", 10, 10);
x_944 = l_Lean_Name_mkStr4(x_938, x_939, x_940, x_943);
x_945 = lean_mk_string_unchecked("null", 4, 4);
x_946 = l_Lean_Name_mkStr1(x_945);
x_947 = l_Array_mkArray0(lean_box(0));
lean_inc(x_937);
x_948 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_948, 0, x_937);
lean_ctor_set(x_948, 1, x_946);
lean_ctor_set(x_948, 2, x_947);
x_949 = lean_mk_syntax_ident(x_909);
lean_inc(x_937);
x_950 = l_Lean_Syntax_node2(x_937, x_944, x_948, x_949);
x_951 = l_Lean_Syntax_node1(x_937, x_942, x_950);
x_952 = lean_array_push(x_23, x_951);
x_953 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_953, 0, x_936);
lean_ctor_set(x_953, 1, x_952);
x_954 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Tactic_mkGrindOnly_spec__3_spec__3___redArg(x_11, x_953, x_4, x_5, x_6, x_7, x_934);
return x_954;
}
}
else
{
uint8_t x_955; 
lean_dec(x_906);
lean_dec(x_23);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_955 = !lean_is_exclusive(x_908);
if (x_955 == 0)
{
return x_908;
}
else
{
lean_object* x_956; lean_object* x_957; lean_object* x_958; 
x_956 = lean_ctor_get(x_908, 0);
x_957 = lean_ctor_get(x_908, 1);
lean_inc(x_957);
lean_inc(x_956);
lean_dec(x_908);
x_958 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_958, 0, x_956);
lean_ctor_set(x_958, 1, x_957);
return x_958;
}
}
}
else
{
lean_object* x_959; 
lean_dec(x_906);
lean_ctor_set(x_31, 1, x_23);
lean_ctor_set(x_31, 0, x_15);
x_959 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Tactic_mkGrindOnly_spec__3_spec__3___redArg(x_11, x_31, x_4, x_5, x_6, x_7, x_904);
return x_959;
}
}
else
{
lean_object* x_960; lean_object* x_961; uint8_t x_962; 
x_960 = lean_ctor_get(x_31, 1);
lean_inc(x_960);
lean_dec(x_31);
x_961 = lean_ctor_get(x_32, 0);
lean_inc(x_961);
lean_dec(x_32);
x_962 = l_Lean_NameSet_contains(x_15, x_961);
if (x_962 == 0)
{
lean_object* x_963; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_961);
x_963 = l_Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0(x_961, x_962, x_4, x_5, x_6, x_7, x_960);
if (lean_obj_tag(x_963) == 0)
{
lean_object* x_964; lean_object* x_965; lean_object* x_966; lean_object* x_967; lean_object* x_968; lean_object* x_969; lean_object* x_970; lean_object* x_971; lean_object* x_972; lean_object* x_973; lean_object* x_974; lean_object* x_975; lean_object* x_976; lean_object* x_977; lean_object* x_978; lean_object* x_979; lean_object* x_980; lean_object* x_981; lean_object* x_982; lean_object* x_983; lean_object* x_984; lean_object* x_985; lean_object* x_986; lean_object* x_987; lean_object* x_988; 
x_964 = lean_ctor_get(x_963, 0);
lean_inc(x_964);
x_965 = lean_ctor_get(x_963, 1);
lean_inc(x_965);
lean_dec(x_963);
x_966 = lean_st_ref_get(x_7, x_965);
x_967 = lean_ctor_get(x_966, 1);
lean_inc(x_967);
if (lean_is_exclusive(x_966)) {
 lean_ctor_release(x_966, 0);
 lean_ctor_release(x_966, 1);
 x_968 = x_966;
} else {
 lean_dec_ref(x_966);
 x_968 = lean_box(0);
}
x_969 = lean_ctor_get(x_6, 5);
lean_inc(x_969);
x_970 = l_Lean_NameSet_insert(x_15, x_961);
x_971 = l_Lean_SourceInfo_fromRef(x_969, x_962);
lean_dec(x_969);
x_972 = lean_mk_string_unchecked("Lean", 4, 4);
x_973 = lean_mk_string_unchecked("Parser", 6, 6);
x_974 = lean_mk_string_unchecked("Tactic", 6, 6);
x_975 = lean_mk_string_unchecked("grindParam", 10, 10);
lean_inc(x_974);
lean_inc(x_973);
lean_inc(x_972);
x_976 = l_Lean_Name_mkStr4(x_972, x_973, x_974, x_975);
x_977 = lean_mk_string_unchecked("grindLemma", 10, 10);
x_978 = l_Lean_Name_mkStr4(x_972, x_973, x_974, x_977);
x_979 = lean_mk_string_unchecked("null", 4, 4);
x_980 = l_Lean_Name_mkStr1(x_979);
x_981 = l_Array_mkArray0(lean_box(0));
lean_inc(x_971);
x_982 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_982, 0, x_971);
lean_ctor_set(x_982, 1, x_980);
lean_ctor_set(x_982, 2, x_981);
x_983 = lean_mk_syntax_ident(x_964);
lean_inc(x_971);
x_984 = l_Lean_Syntax_node2(x_971, x_978, x_982, x_983);
x_985 = l_Lean_Syntax_node1(x_971, x_976, x_984);
x_986 = lean_array_push(x_23, x_985);
if (lean_is_scalar(x_968)) {
 x_987 = lean_alloc_ctor(0, 2, 0);
} else {
 x_987 = x_968;
}
lean_ctor_set(x_987, 0, x_970);
lean_ctor_set(x_987, 1, x_986);
x_988 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Tactic_mkGrindOnly_spec__3_spec__3___redArg(x_11, x_987, x_4, x_5, x_6, x_7, x_967);
return x_988;
}
else
{
lean_object* x_989; lean_object* x_990; lean_object* x_991; lean_object* x_992; 
lean_dec(x_961);
lean_dec(x_23);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_989 = lean_ctor_get(x_963, 0);
lean_inc(x_989);
x_990 = lean_ctor_get(x_963, 1);
lean_inc(x_990);
if (lean_is_exclusive(x_963)) {
 lean_ctor_release(x_963, 0);
 lean_ctor_release(x_963, 1);
 x_991 = x_963;
} else {
 lean_dec_ref(x_963);
 x_991 = lean_box(0);
}
if (lean_is_scalar(x_991)) {
 x_992 = lean_alloc_ctor(1, 2, 0);
} else {
 x_992 = x_991;
}
lean_ctor_set(x_992, 0, x_989);
lean_ctor_set(x_992, 1, x_990);
return x_992;
}
}
else
{
lean_object* x_993; lean_object* x_994; 
lean_dec(x_961);
x_993 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_993, 0, x_15);
lean_ctor_set(x_993, 1, x_23);
x_994 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Tactic_mkGrindOnly_spec__3_spec__3___redArg(x_11, x_993, x_4, x_5, x_6, x_7, x_960);
return x_994;
}
}
}
}
else
{
lean_object* x_995; 
lean_dec(x_24);
lean_dec(x_12);
lean_ctor_set(x_25, 1, x_23);
lean_ctor_set(x_25, 0, x_15);
x_995 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Tactic_mkGrindOnly_spec__3_spec__3___redArg(x_11, x_25, x_4, x_5, x_6, x_7, x_28);
return x_995;
}
}
else
{
lean_object* x_996; lean_object* x_997; lean_object* x_998; uint8_t x_999; 
x_996 = lean_ctor_get(x_25, 0);
x_997 = lean_ctor_get(x_25, 1);
lean_inc(x_997);
lean_inc(x_996);
lean_dec(x_25);
x_998 = lean_ctor_get(x_996, 0);
lean_inc(x_998);
lean_dec(x_996);
lean_inc(x_24);
x_999 = l_Lean_Meta_Match_isMatchEqnTheorem(x_998, x_24);
if (x_999 == 0)
{
lean_object* x_1000; lean_object* x_1001; 
x_1000 = l_Lean_Meta_isEqnThm_x3f(x_24, x_6, x_7, x_997);
x_1001 = lean_ctor_get(x_1000, 0);
lean_inc(x_1001);
if (lean_obj_tag(x_1001) == 0)
{
lean_object* x_1002; lean_object* x_1003; lean_object* x_1004; 
x_1002 = lean_ctor_get(x_1000, 1);
lean_inc(x_1002);
if (lean_is_exclusive(x_1000)) {
 lean_ctor_release(x_1000, 0);
 lean_ctor_release(x_1000, 1);
 x_1003 = x_1000;
} else {
 lean_dec_ref(x_1000);
 x_1003 = lean_box(0);
}
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_1004 = l_Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0(x_24, x_999, x_4, x_5, x_6, x_7, x_1002);
if (lean_obj_tag(x_1004) == 0)
{
switch (x_14) {
case 0:
{
lean_object* x_1005; lean_object* x_1006; lean_object* x_1007; lean_object* x_1008; lean_object* x_1009; lean_object* x_1010; lean_object* x_1011; lean_object* x_1012; lean_object* x_1013; lean_object* x_1014; lean_object* x_1015; lean_object* x_1016; lean_object* x_1017; lean_object* x_1018; lean_object* x_1019; lean_object* x_1020; lean_object* x_1021; lean_object* x_1022; lean_object* x_1023; lean_object* x_1024; lean_object* x_1025; lean_object* x_1026; lean_object* x_1027; lean_object* x_1028; lean_object* x_1029; lean_object* x_1030; lean_object* x_1031; lean_object* x_1032; lean_object* x_1033; 
lean_dec(x_1003);
x_1005 = lean_ctor_get(x_1004, 0);
lean_inc(x_1005);
x_1006 = lean_ctor_get(x_1004, 1);
lean_inc(x_1006);
lean_dec(x_1004);
x_1007 = lean_st_ref_get(x_7, x_1006);
x_1008 = lean_ctor_get(x_1007, 1);
lean_inc(x_1008);
if (lean_is_exclusive(x_1007)) {
 lean_ctor_release(x_1007, 0);
 lean_ctor_release(x_1007, 1);
 x_1009 = x_1007;
} else {
 lean_dec_ref(x_1007);
 x_1009 = lean_box(0);
}
x_1010 = lean_ctor_get(x_6, 5);
lean_inc(x_1010);
x_1011 = l_Lean_SourceInfo_fromRef(x_1010, x_999);
lean_dec(x_1010);
x_1012 = lean_mk_string_unchecked("Lean", 4, 4);
x_1013 = lean_mk_string_unchecked("Parser", 6, 6);
x_1014 = lean_mk_string_unchecked("Tactic", 6, 6);
x_1015 = lean_mk_string_unchecked("grindParam", 10, 10);
lean_inc(x_1014);
lean_inc(x_1013);
lean_inc(x_1012);
x_1016 = l_Lean_Name_mkStr4(x_1012, x_1013, x_1014, x_1015);
x_1017 = lean_mk_string_unchecked("grindLemma", 10, 10);
lean_inc(x_1013);
lean_inc(x_1012);
x_1018 = l_Lean_Name_mkStr4(x_1012, x_1013, x_1014, x_1017);
x_1019 = lean_mk_string_unchecked("null", 4, 4);
x_1020 = l_Lean_Name_mkStr1(x_1019);
x_1021 = lean_mk_string_unchecked("Attr", 4, 4);
x_1022 = lean_mk_string_unchecked("grindMod", 8, 8);
lean_inc(x_1021);
lean_inc(x_1013);
lean_inc(x_1012);
x_1023 = l_Lean_Name_mkStr4(x_1012, x_1013, x_1021, x_1022);
x_1024 = lean_mk_string_unchecked("grindEq", 7, 7);
x_1025 = l_Lean_Name_mkStr4(x_1012, x_1013, x_1021, x_1024);
x_1026 = lean_mk_string_unchecked("=", 1, 1);
lean_inc(x_1011);
if (lean_is_scalar(x_1009)) {
 x_1027 = lean_alloc_ctor(2, 2, 0);
} else {
 x_1027 = x_1009;
 lean_ctor_set_tag(x_1027, 2);
}
lean_ctor_set(x_1027, 0, x_1011);
lean_ctor_set(x_1027, 1, x_1026);
lean_inc(x_1011);
x_1028 = l_Lean_Syntax_node1(x_1011, x_1025, x_1027);
lean_inc(x_1011);
x_1029 = l_Lean_Syntax_node1(x_1011, x_1023, x_1028);
lean_inc(x_1011);
x_1030 = l_Lean_Syntax_node1(x_1011, x_1020, x_1029);
x_1031 = lean_mk_syntax_ident(x_1005);
lean_inc(x_1011);
x_1032 = l_Lean_Syntax_node2(x_1011, x_1018, x_1030, x_1031);
x_1033 = l_Lean_Syntax_node1(x_1011, x_1016, x_1032);
x_16 = x_23;
x_17 = x_1033;
x_18 = x_1008;
goto block_22;
}
case 1:
{
lean_object* x_1034; lean_object* x_1035; lean_object* x_1036; lean_object* x_1037; lean_object* x_1038; lean_object* x_1039; lean_object* x_1040; lean_object* x_1041; lean_object* x_1042; lean_object* x_1043; lean_object* x_1044; lean_object* x_1045; lean_object* x_1046; lean_object* x_1047; lean_object* x_1048; lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; lean_object* x_1052; lean_object* x_1053; lean_object* x_1054; lean_object* x_1055; lean_object* x_1056; lean_object* x_1057; lean_object* x_1058; lean_object* x_1059; lean_object* x_1060; lean_object* x_1061; lean_object* x_1062; lean_object* x_1063; lean_object* x_1064; 
x_1034 = lean_ctor_get(x_1004, 0);
lean_inc(x_1034);
x_1035 = lean_ctor_get(x_1004, 1);
lean_inc(x_1035);
lean_dec(x_1004);
x_1036 = lean_st_ref_get(x_7, x_1035);
x_1037 = lean_ctor_get(x_1036, 1);
lean_inc(x_1037);
if (lean_is_exclusive(x_1036)) {
 lean_ctor_release(x_1036, 0);
 lean_ctor_release(x_1036, 1);
 x_1038 = x_1036;
} else {
 lean_dec_ref(x_1036);
 x_1038 = lean_box(0);
}
x_1039 = lean_ctor_get(x_6, 5);
lean_inc(x_1039);
x_1040 = l_Lean_SourceInfo_fromRef(x_1039, x_999);
lean_dec(x_1039);
x_1041 = lean_mk_string_unchecked("Lean", 4, 4);
x_1042 = lean_mk_string_unchecked("Parser", 6, 6);
x_1043 = lean_mk_string_unchecked("Tactic", 6, 6);
x_1044 = lean_mk_string_unchecked("grindParam", 10, 10);
lean_inc(x_1043);
lean_inc(x_1042);
lean_inc(x_1041);
x_1045 = l_Lean_Name_mkStr4(x_1041, x_1042, x_1043, x_1044);
x_1046 = lean_mk_string_unchecked("grindLemma", 10, 10);
lean_inc(x_1042);
lean_inc(x_1041);
x_1047 = l_Lean_Name_mkStr4(x_1041, x_1042, x_1043, x_1046);
x_1048 = lean_mk_string_unchecked("null", 4, 4);
x_1049 = l_Lean_Name_mkStr1(x_1048);
x_1050 = lean_mk_string_unchecked("Attr", 4, 4);
x_1051 = lean_mk_string_unchecked("grindMod", 8, 8);
lean_inc(x_1050);
lean_inc(x_1042);
lean_inc(x_1041);
x_1052 = l_Lean_Name_mkStr4(x_1041, x_1042, x_1050, x_1051);
x_1053 = lean_mk_string_unchecked("grindEqRhs", 10, 10);
x_1054 = l_Lean_Name_mkStr4(x_1041, x_1042, x_1050, x_1053);
x_1055 = lean_mk_string_unchecked("=", 1, 1);
lean_inc(x_1040);
if (lean_is_scalar(x_1038)) {
 x_1056 = lean_alloc_ctor(2, 2, 0);
} else {
 x_1056 = x_1038;
 lean_ctor_set_tag(x_1056, 2);
}
lean_ctor_set(x_1056, 0, x_1040);
lean_ctor_set(x_1056, 1, x_1055);
x_1057 = lean_mk_string_unchecked("_", 1, 1);
lean_inc(x_1040);
if (lean_is_scalar(x_1003)) {
 x_1058 = lean_alloc_ctor(2, 2, 0);
} else {
 x_1058 = x_1003;
 lean_ctor_set_tag(x_1058, 2);
}
lean_ctor_set(x_1058, 0, x_1040);
lean_ctor_set(x_1058, 1, x_1057);
lean_inc(x_1040);
x_1059 = l_Lean_Syntax_node2(x_1040, x_1054, x_1056, x_1058);
lean_inc(x_1040);
x_1060 = l_Lean_Syntax_node1(x_1040, x_1052, x_1059);
lean_inc(x_1040);
x_1061 = l_Lean_Syntax_node1(x_1040, x_1049, x_1060);
x_1062 = lean_mk_syntax_ident(x_1034);
lean_inc(x_1040);
x_1063 = l_Lean_Syntax_node2(x_1040, x_1047, x_1061, x_1062);
x_1064 = l_Lean_Syntax_node1(x_1040, x_1045, x_1063);
x_16 = x_23;
x_17 = x_1064;
x_18 = x_1037;
goto block_22;
}
case 2:
{
lean_object* x_1065; lean_object* x_1066; lean_object* x_1067; lean_object* x_1068; lean_object* x_1069; lean_object* x_1070; lean_object* x_1071; lean_object* x_1072; lean_object* x_1073; lean_object* x_1074; lean_object* x_1075; lean_object* x_1076; lean_object* x_1077; lean_object* x_1078; lean_object* x_1079; lean_object* x_1080; lean_object* x_1081; lean_object* x_1082; lean_object* x_1083; lean_object* x_1084; lean_object* x_1085; lean_object* x_1086; lean_object* x_1087; lean_object* x_1088; lean_object* x_1089; lean_object* x_1090; lean_object* x_1091; lean_object* x_1092; lean_object* x_1093; lean_object* x_1094; lean_object* x_1095; 
x_1065 = lean_ctor_get(x_1004, 0);
lean_inc(x_1065);
x_1066 = lean_ctor_get(x_1004, 1);
lean_inc(x_1066);
lean_dec(x_1004);
x_1067 = lean_st_ref_get(x_7, x_1066);
x_1068 = lean_ctor_get(x_1067, 1);
lean_inc(x_1068);
if (lean_is_exclusive(x_1067)) {
 lean_ctor_release(x_1067, 0);
 lean_ctor_release(x_1067, 1);
 x_1069 = x_1067;
} else {
 lean_dec_ref(x_1067);
 x_1069 = lean_box(0);
}
x_1070 = lean_ctor_get(x_6, 5);
lean_inc(x_1070);
x_1071 = l_Lean_SourceInfo_fromRef(x_1070, x_999);
lean_dec(x_1070);
x_1072 = lean_mk_string_unchecked("Lean", 4, 4);
x_1073 = lean_mk_string_unchecked("Parser", 6, 6);
x_1074 = lean_mk_string_unchecked("Tactic", 6, 6);
x_1075 = lean_mk_string_unchecked("grindParam", 10, 10);
lean_inc(x_1074);
lean_inc(x_1073);
lean_inc(x_1072);
x_1076 = l_Lean_Name_mkStr4(x_1072, x_1073, x_1074, x_1075);
x_1077 = lean_mk_string_unchecked("grindLemma", 10, 10);
lean_inc(x_1073);
lean_inc(x_1072);
x_1078 = l_Lean_Name_mkStr4(x_1072, x_1073, x_1074, x_1077);
x_1079 = lean_mk_string_unchecked("null", 4, 4);
x_1080 = l_Lean_Name_mkStr1(x_1079);
x_1081 = lean_mk_string_unchecked("Attr", 4, 4);
x_1082 = lean_mk_string_unchecked("grindMod", 8, 8);
lean_inc(x_1081);
lean_inc(x_1073);
lean_inc(x_1072);
x_1083 = l_Lean_Name_mkStr4(x_1072, x_1073, x_1081, x_1082);
x_1084 = lean_mk_string_unchecked("grindEqBoth", 11, 11);
x_1085 = l_Lean_Name_mkStr4(x_1072, x_1073, x_1081, x_1084);
x_1086 = lean_mk_string_unchecked("_", 1, 1);
lean_inc(x_1071);
if (lean_is_scalar(x_1069)) {
 x_1087 = lean_alloc_ctor(2, 2, 0);
} else {
 x_1087 = x_1069;
 lean_ctor_set_tag(x_1087, 2);
}
lean_ctor_set(x_1087, 0, x_1071);
lean_ctor_set(x_1087, 1, x_1086);
x_1088 = lean_mk_string_unchecked("=", 1, 1);
lean_inc(x_1071);
if (lean_is_scalar(x_1003)) {
 x_1089 = lean_alloc_ctor(2, 2, 0);
} else {
 x_1089 = x_1003;
 lean_ctor_set_tag(x_1089, 2);
}
lean_ctor_set(x_1089, 0, x_1071);
lean_ctor_set(x_1089, 1, x_1088);
lean_inc(x_1087);
lean_inc(x_1071);
x_1090 = l_Lean_Syntax_node3(x_1071, x_1085, x_1087, x_1089, x_1087);
lean_inc(x_1071);
x_1091 = l_Lean_Syntax_node1(x_1071, x_1083, x_1090);
lean_inc(x_1071);
x_1092 = l_Lean_Syntax_node1(x_1071, x_1080, x_1091);
x_1093 = lean_mk_syntax_ident(x_1065);
lean_inc(x_1071);
x_1094 = l_Lean_Syntax_node2(x_1071, x_1078, x_1092, x_1093);
x_1095 = l_Lean_Syntax_node1(x_1071, x_1076, x_1094);
x_16 = x_23;
x_17 = x_1095;
x_18 = x_1068;
goto block_22;
}
case 3:
{
lean_object* x_1096; lean_object* x_1097; lean_object* x_1098; lean_object* x_1099; lean_object* x_1100; lean_object* x_1101; lean_object* x_1102; lean_object* x_1103; lean_object* x_1104; lean_object* x_1105; lean_object* x_1106; lean_object* x_1107; lean_object* x_1108; lean_object* x_1109; lean_object* x_1110; lean_object* x_1111; lean_object* x_1112; lean_object* x_1113; lean_object* x_1114; lean_object* x_1115; lean_object* x_1116; lean_object* x_1117; lean_object* x_1118; lean_object* x_1119; lean_object* x_1120; lean_object* x_1121; lean_object* x_1122; lean_object* x_1123; lean_object* x_1124; lean_object* x_1125; lean_object* x_1126; lean_object* x_1127; lean_object* x_1128; lean_object* x_1129; 
x_1096 = lean_ctor_get(x_1004, 0);
lean_inc(x_1096);
x_1097 = lean_ctor_get(x_1004, 1);
lean_inc(x_1097);
lean_dec(x_1004);
x_1098 = lean_st_ref_get(x_7, x_1097);
x_1099 = lean_ctor_get(x_1098, 1);
lean_inc(x_1099);
if (lean_is_exclusive(x_1098)) {
 lean_ctor_release(x_1098, 0);
 lean_ctor_release(x_1098, 1);
 x_1100 = x_1098;
} else {
 lean_dec_ref(x_1098);
 x_1100 = lean_box(0);
}
x_1101 = lean_ctor_get(x_6, 5);
lean_inc(x_1101);
x_1102 = l_Lean_SourceInfo_fromRef(x_1101, x_999);
lean_dec(x_1101);
x_1103 = lean_mk_string_unchecked("Lean", 4, 4);
x_1104 = lean_mk_string_unchecked("Parser", 6, 6);
x_1105 = lean_mk_string_unchecked("Tactic", 6, 6);
x_1106 = lean_mk_string_unchecked("grindParam", 10, 10);
lean_inc(x_1105);
lean_inc(x_1104);
lean_inc(x_1103);
x_1107 = l_Lean_Name_mkStr4(x_1103, x_1104, x_1105, x_1106);
x_1108 = lean_mk_string_unchecked("grindLemma", 10, 10);
lean_inc(x_1104);
lean_inc(x_1103);
x_1109 = l_Lean_Name_mkStr4(x_1103, x_1104, x_1105, x_1108);
x_1110 = lean_mk_string_unchecked("null", 4, 4);
x_1111 = l_Lean_Name_mkStr1(x_1110);
x_1112 = lean_mk_string_unchecked("Attr", 4, 4);
x_1113 = lean_mk_string_unchecked("grindMod", 8, 8);
lean_inc(x_1112);
lean_inc(x_1104);
lean_inc(x_1103);
x_1114 = l_Lean_Name_mkStr4(x_1103, x_1104, x_1112, x_1113);
x_1115 = lean_mk_string_unchecked("grindEqBwd", 10, 10);
x_1116 = l_Lean_Name_mkStr4(x_1103, x_1104, x_1112, x_1115);
x_1117 = lean_mk_string_unchecked("group", 5, 5);
x_1118 = l_Lean_Name_mkStr1(x_1117);
x_1119 = lean_mk_string_unchecked("←", 3, 1);
lean_inc(x_1102);
if (lean_is_scalar(x_1100)) {
 x_1120 = lean_alloc_ctor(2, 2, 0);
} else {
 x_1120 = x_1100;
 lean_ctor_set_tag(x_1120, 2);
}
lean_ctor_set(x_1120, 0, x_1102);
lean_ctor_set(x_1120, 1, x_1119);
x_1121 = lean_mk_string_unchecked("=", 1, 1);
lean_inc(x_1102);
if (lean_is_scalar(x_1003)) {
 x_1122 = lean_alloc_ctor(2, 2, 0);
} else {
 x_1122 = x_1003;
 lean_ctor_set_tag(x_1122, 2);
}
lean_ctor_set(x_1122, 0, x_1102);
lean_ctor_set(x_1122, 1, x_1121);
lean_inc(x_1102);
x_1123 = l_Lean_Syntax_node2(x_1102, x_1118, x_1120, x_1122);
lean_inc(x_1102);
x_1124 = l_Lean_Syntax_node1(x_1102, x_1116, x_1123);
lean_inc(x_1102);
x_1125 = l_Lean_Syntax_node1(x_1102, x_1114, x_1124);
lean_inc(x_1102);
x_1126 = l_Lean_Syntax_node1(x_1102, x_1111, x_1125);
x_1127 = lean_mk_syntax_ident(x_1096);
lean_inc(x_1102);
x_1128 = l_Lean_Syntax_node2(x_1102, x_1109, x_1126, x_1127);
x_1129 = l_Lean_Syntax_node1(x_1102, x_1107, x_1128);
x_16 = x_23;
x_17 = x_1129;
x_18 = x_1099;
goto block_22;
}
case 4:
{
lean_object* x_1130; lean_object* x_1131; lean_object* x_1132; lean_object* x_1133; lean_object* x_1134; lean_object* x_1135; lean_object* x_1136; lean_object* x_1137; lean_object* x_1138; lean_object* x_1139; lean_object* x_1140; lean_object* x_1141; lean_object* x_1142; lean_object* x_1143; lean_object* x_1144; lean_object* x_1145; lean_object* x_1146; lean_object* x_1147; lean_object* x_1148; lean_object* x_1149; lean_object* x_1150; lean_object* x_1151; lean_object* x_1152; lean_object* x_1153; lean_object* x_1154; lean_object* x_1155; lean_object* x_1156; lean_object* x_1157; lean_object* x_1158; lean_object* x_1159; lean_object* x_1160; lean_object* x_1161; lean_object* x_1162; 
lean_dec(x_1003);
x_1130 = lean_ctor_get(x_1004, 0);
lean_inc(x_1130);
x_1131 = lean_ctor_get(x_1004, 1);
lean_inc(x_1131);
lean_dec(x_1004);
x_1132 = lean_st_ref_get(x_7, x_1131);
x_1133 = lean_ctor_get(x_1132, 1);
lean_inc(x_1133);
if (lean_is_exclusive(x_1132)) {
 lean_ctor_release(x_1132, 0);
 lean_ctor_release(x_1132, 1);
 x_1134 = x_1132;
} else {
 lean_dec_ref(x_1132);
 x_1134 = lean_box(0);
}
x_1135 = lean_ctor_get(x_6, 5);
lean_inc(x_1135);
x_1136 = l_Lean_SourceInfo_fromRef(x_1135, x_999);
lean_dec(x_1135);
x_1137 = lean_mk_string_unchecked("Lean", 4, 4);
x_1138 = lean_mk_string_unchecked("Parser", 6, 6);
x_1139 = lean_mk_string_unchecked("Tactic", 6, 6);
x_1140 = lean_mk_string_unchecked("grindParam", 10, 10);
lean_inc(x_1139);
lean_inc(x_1138);
lean_inc(x_1137);
x_1141 = l_Lean_Name_mkStr4(x_1137, x_1138, x_1139, x_1140);
x_1142 = lean_mk_string_unchecked("grindLemma", 10, 10);
lean_inc(x_1138);
lean_inc(x_1137);
x_1143 = l_Lean_Name_mkStr4(x_1137, x_1138, x_1139, x_1142);
x_1144 = lean_mk_string_unchecked("null", 4, 4);
x_1145 = l_Lean_Name_mkStr1(x_1144);
x_1146 = lean_mk_string_unchecked("Attr", 4, 4);
x_1147 = lean_mk_string_unchecked("grindMod", 8, 8);
lean_inc(x_1146);
lean_inc(x_1138);
lean_inc(x_1137);
x_1148 = l_Lean_Name_mkStr4(x_1137, x_1138, x_1146, x_1147);
x_1149 = lean_mk_string_unchecked("grindFwd", 8, 8);
x_1150 = l_Lean_Name_mkStr4(x_1137, x_1138, x_1146, x_1149);
x_1151 = lean_mk_string_unchecked("token", 5, 5);
x_1152 = lean_mk_string_unchecked("→ ", 4, 2);
x_1153 = l_Lean_Name_mkStr2(x_1151, x_1152);
x_1154 = lean_mk_string_unchecked("→", 3, 1);
lean_inc(x_1136);
if (lean_is_scalar(x_1134)) {
 x_1155 = lean_alloc_ctor(2, 2, 0);
} else {
 x_1155 = x_1134;
 lean_ctor_set_tag(x_1155, 2);
}
lean_ctor_set(x_1155, 0, x_1136);
lean_ctor_set(x_1155, 1, x_1154);
lean_inc(x_1136);
x_1156 = l_Lean_Syntax_node1(x_1136, x_1153, x_1155);
lean_inc(x_1136);
x_1157 = l_Lean_Syntax_node1(x_1136, x_1150, x_1156);
lean_inc(x_1136);
x_1158 = l_Lean_Syntax_node1(x_1136, x_1148, x_1157);
lean_inc(x_1136);
x_1159 = l_Lean_Syntax_node1(x_1136, x_1145, x_1158);
x_1160 = lean_mk_syntax_ident(x_1130);
lean_inc(x_1136);
x_1161 = l_Lean_Syntax_node2(x_1136, x_1143, x_1159, x_1160);
x_1162 = l_Lean_Syntax_node1(x_1136, x_1141, x_1161);
x_16 = x_23;
x_17 = x_1162;
x_18 = x_1133;
goto block_22;
}
case 5:
{
lean_object* x_1163; lean_object* x_1164; lean_object* x_1165; lean_object* x_1166; lean_object* x_1167; lean_object* x_1168; lean_object* x_1169; lean_object* x_1170; lean_object* x_1171; lean_object* x_1172; lean_object* x_1173; lean_object* x_1174; lean_object* x_1175; lean_object* x_1176; lean_object* x_1177; lean_object* x_1178; lean_object* x_1179; lean_object* x_1180; lean_object* x_1181; lean_object* x_1182; lean_object* x_1183; lean_object* x_1184; lean_object* x_1185; lean_object* x_1186; lean_object* x_1187; lean_object* x_1188; lean_object* x_1189; lean_object* x_1190; lean_object* x_1191; lean_object* x_1192; lean_object* x_1193; lean_object* x_1194; lean_object* x_1195; 
lean_dec(x_1003);
x_1163 = lean_ctor_get(x_1004, 0);
lean_inc(x_1163);
x_1164 = lean_ctor_get(x_1004, 1);
lean_inc(x_1164);
lean_dec(x_1004);
x_1165 = lean_st_ref_get(x_7, x_1164);
x_1166 = lean_ctor_get(x_1165, 1);
lean_inc(x_1166);
if (lean_is_exclusive(x_1165)) {
 lean_ctor_release(x_1165, 0);
 lean_ctor_release(x_1165, 1);
 x_1167 = x_1165;
} else {
 lean_dec_ref(x_1165);
 x_1167 = lean_box(0);
}
x_1168 = lean_ctor_get(x_6, 5);
lean_inc(x_1168);
x_1169 = l_Lean_SourceInfo_fromRef(x_1168, x_999);
lean_dec(x_1168);
x_1170 = lean_mk_string_unchecked("Lean", 4, 4);
x_1171 = lean_mk_string_unchecked("Parser", 6, 6);
x_1172 = lean_mk_string_unchecked("Tactic", 6, 6);
x_1173 = lean_mk_string_unchecked("grindParam", 10, 10);
lean_inc(x_1172);
lean_inc(x_1171);
lean_inc(x_1170);
x_1174 = l_Lean_Name_mkStr4(x_1170, x_1171, x_1172, x_1173);
x_1175 = lean_mk_string_unchecked("grindLemma", 10, 10);
lean_inc(x_1171);
lean_inc(x_1170);
x_1176 = l_Lean_Name_mkStr4(x_1170, x_1171, x_1172, x_1175);
x_1177 = lean_mk_string_unchecked("null", 4, 4);
x_1178 = l_Lean_Name_mkStr1(x_1177);
x_1179 = lean_mk_string_unchecked("Attr", 4, 4);
x_1180 = lean_mk_string_unchecked("grindMod", 8, 8);
lean_inc(x_1179);
lean_inc(x_1171);
lean_inc(x_1170);
x_1181 = l_Lean_Name_mkStr4(x_1170, x_1171, x_1179, x_1180);
x_1182 = lean_mk_string_unchecked("grindBwd", 8, 8);
x_1183 = l_Lean_Name_mkStr4(x_1170, x_1171, x_1179, x_1182);
x_1184 = lean_mk_string_unchecked("token", 5, 5);
x_1185 = lean_mk_string_unchecked("← ", 4, 2);
x_1186 = l_Lean_Name_mkStr2(x_1184, x_1185);
x_1187 = lean_mk_string_unchecked("←", 3, 1);
lean_inc(x_1169);
if (lean_is_scalar(x_1167)) {
 x_1188 = lean_alloc_ctor(2, 2, 0);
} else {
 x_1188 = x_1167;
 lean_ctor_set_tag(x_1188, 2);
}
lean_ctor_set(x_1188, 0, x_1169);
lean_ctor_set(x_1188, 1, x_1187);
lean_inc(x_1169);
x_1189 = l_Lean_Syntax_node1(x_1169, x_1186, x_1188);
lean_inc(x_1169);
x_1190 = l_Lean_Syntax_node1(x_1169, x_1183, x_1189);
lean_inc(x_1169);
x_1191 = l_Lean_Syntax_node1(x_1169, x_1181, x_1190);
lean_inc(x_1169);
x_1192 = l_Lean_Syntax_node1(x_1169, x_1178, x_1191);
x_1193 = lean_mk_syntax_ident(x_1163);
lean_inc(x_1169);
x_1194 = l_Lean_Syntax_node2(x_1169, x_1176, x_1192, x_1193);
x_1195 = l_Lean_Syntax_node1(x_1169, x_1174, x_1194);
x_16 = x_23;
x_17 = x_1195;
x_18 = x_1166;
goto block_22;
}
case 6:
{
lean_object* x_1196; lean_object* x_1197; lean_object* x_1198; lean_object* x_1199; lean_object* x_1200; lean_object* x_1201; lean_object* x_1202; lean_object* x_1203; lean_object* x_1204; lean_object* x_1205; lean_object* x_1206; lean_object* x_1207; lean_object* x_1208; lean_object* x_1209; lean_object* x_1210; lean_object* x_1211; lean_object* x_1212; lean_object* x_1213; lean_object* x_1214; lean_object* x_1215; lean_object* x_1216; lean_object* x_1217; lean_object* x_1218; lean_object* x_1219; lean_object* x_1220; lean_object* x_1221; lean_object* x_1222; lean_object* x_1223; lean_object* x_1224; lean_object* x_1225; lean_object* x_1226; lean_object* x_1227; lean_object* x_1228; 
lean_dec(x_1003);
x_1196 = lean_ctor_get(x_1004, 0);
lean_inc(x_1196);
x_1197 = lean_ctor_get(x_1004, 1);
lean_inc(x_1197);
lean_dec(x_1004);
x_1198 = lean_st_ref_get(x_7, x_1197);
x_1199 = lean_ctor_get(x_1198, 1);
lean_inc(x_1199);
if (lean_is_exclusive(x_1198)) {
 lean_ctor_release(x_1198, 0);
 lean_ctor_release(x_1198, 1);
 x_1200 = x_1198;
} else {
 lean_dec_ref(x_1198);
 x_1200 = lean_box(0);
}
x_1201 = lean_ctor_get(x_6, 5);
lean_inc(x_1201);
x_1202 = l_Lean_SourceInfo_fromRef(x_1201, x_999);
lean_dec(x_1201);
x_1203 = lean_mk_string_unchecked("Lean", 4, 4);
x_1204 = lean_mk_string_unchecked("Parser", 6, 6);
x_1205 = lean_mk_string_unchecked("Tactic", 6, 6);
x_1206 = lean_mk_string_unchecked("grindParam", 10, 10);
lean_inc(x_1205);
lean_inc(x_1204);
lean_inc(x_1203);
x_1207 = l_Lean_Name_mkStr4(x_1203, x_1204, x_1205, x_1206);
x_1208 = lean_mk_string_unchecked("grindLemma", 10, 10);
lean_inc(x_1204);
lean_inc(x_1203);
x_1209 = l_Lean_Name_mkStr4(x_1203, x_1204, x_1205, x_1208);
x_1210 = lean_mk_string_unchecked("null", 4, 4);
x_1211 = l_Lean_Name_mkStr1(x_1210);
x_1212 = lean_mk_string_unchecked("Attr", 4, 4);
x_1213 = lean_mk_string_unchecked("grindMod", 8, 8);
lean_inc(x_1212);
lean_inc(x_1204);
lean_inc(x_1203);
x_1214 = l_Lean_Name_mkStr4(x_1203, x_1204, x_1212, x_1213);
x_1215 = lean_mk_string_unchecked("grindLR", 7, 7);
x_1216 = l_Lean_Name_mkStr4(x_1203, x_1204, x_1212, x_1215);
x_1217 = lean_mk_string_unchecked("token", 5, 5);
x_1218 = lean_mk_string_unchecked("=> ", 3, 3);
x_1219 = l_Lean_Name_mkStr2(x_1217, x_1218);
x_1220 = lean_mk_string_unchecked("=>", 2, 2);
lean_inc(x_1202);
if (lean_is_scalar(x_1200)) {
 x_1221 = lean_alloc_ctor(2, 2, 0);
} else {
 x_1221 = x_1200;
 lean_ctor_set_tag(x_1221, 2);
}
lean_ctor_set(x_1221, 0, x_1202);
lean_ctor_set(x_1221, 1, x_1220);
lean_inc(x_1202);
x_1222 = l_Lean_Syntax_node1(x_1202, x_1219, x_1221);
lean_inc(x_1202);
x_1223 = l_Lean_Syntax_node1(x_1202, x_1216, x_1222);
lean_inc(x_1202);
x_1224 = l_Lean_Syntax_node1(x_1202, x_1214, x_1223);
lean_inc(x_1202);
x_1225 = l_Lean_Syntax_node1(x_1202, x_1211, x_1224);
x_1226 = lean_mk_syntax_ident(x_1196);
lean_inc(x_1202);
x_1227 = l_Lean_Syntax_node2(x_1202, x_1209, x_1225, x_1226);
x_1228 = l_Lean_Syntax_node1(x_1202, x_1207, x_1227);
x_16 = x_23;
x_17 = x_1228;
x_18 = x_1199;
goto block_22;
}
case 7:
{
lean_object* x_1229; lean_object* x_1230; lean_object* x_1231; lean_object* x_1232; lean_object* x_1233; lean_object* x_1234; lean_object* x_1235; lean_object* x_1236; lean_object* x_1237; lean_object* x_1238; lean_object* x_1239; lean_object* x_1240; lean_object* x_1241; lean_object* x_1242; lean_object* x_1243; lean_object* x_1244; lean_object* x_1245; lean_object* x_1246; lean_object* x_1247; lean_object* x_1248; lean_object* x_1249; lean_object* x_1250; lean_object* x_1251; lean_object* x_1252; lean_object* x_1253; lean_object* x_1254; lean_object* x_1255; lean_object* x_1256; lean_object* x_1257; lean_object* x_1258; lean_object* x_1259; lean_object* x_1260; lean_object* x_1261; 
lean_dec(x_1003);
x_1229 = lean_ctor_get(x_1004, 0);
lean_inc(x_1229);
x_1230 = lean_ctor_get(x_1004, 1);
lean_inc(x_1230);
lean_dec(x_1004);
x_1231 = lean_st_ref_get(x_7, x_1230);
x_1232 = lean_ctor_get(x_1231, 1);
lean_inc(x_1232);
if (lean_is_exclusive(x_1231)) {
 lean_ctor_release(x_1231, 0);
 lean_ctor_release(x_1231, 1);
 x_1233 = x_1231;
} else {
 lean_dec_ref(x_1231);
 x_1233 = lean_box(0);
}
x_1234 = lean_ctor_get(x_6, 5);
lean_inc(x_1234);
x_1235 = l_Lean_SourceInfo_fromRef(x_1234, x_999);
lean_dec(x_1234);
x_1236 = lean_mk_string_unchecked("Lean", 4, 4);
x_1237 = lean_mk_string_unchecked("Parser", 6, 6);
x_1238 = lean_mk_string_unchecked("Tactic", 6, 6);
x_1239 = lean_mk_string_unchecked("grindParam", 10, 10);
lean_inc(x_1238);
lean_inc(x_1237);
lean_inc(x_1236);
x_1240 = l_Lean_Name_mkStr4(x_1236, x_1237, x_1238, x_1239);
x_1241 = lean_mk_string_unchecked("grindLemma", 10, 10);
lean_inc(x_1237);
lean_inc(x_1236);
x_1242 = l_Lean_Name_mkStr4(x_1236, x_1237, x_1238, x_1241);
x_1243 = lean_mk_string_unchecked("null", 4, 4);
x_1244 = l_Lean_Name_mkStr1(x_1243);
x_1245 = lean_mk_string_unchecked("Attr", 4, 4);
x_1246 = lean_mk_string_unchecked("grindMod", 8, 8);
lean_inc(x_1245);
lean_inc(x_1237);
lean_inc(x_1236);
x_1247 = l_Lean_Name_mkStr4(x_1236, x_1237, x_1245, x_1246);
x_1248 = lean_mk_string_unchecked("grindRL", 7, 7);
x_1249 = l_Lean_Name_mkStr4(x_1236, x_1237, x_1245, x_1248);
x_1250 = lean_mk_string_unchecked("token", 5, 5);
x_1251 = lean_mk_string_unchecked("<= ", 3, 3);
x_1252 = l_Lean_Name_mkStr2(x_1250, x_1251);
x_1253 = lean_mk_string_unchecked("<=", 2, 2);
lean_inc(x_1235);
if (lean_is_scalar(x_1233)) {
 x_1254 = lean_alloc_ctor(2, 2, 0);
} else {
 x_1254 = x_1233;
 lean_ctor_set_tag(x_1254, 2);
}
lean_ctor_set(x_1254, 0, x_1235);
lean_ctor_set(x_1254, 1, x_1253);
lean_inc(x_1235);
x_1255 = l_Lean_Syntax_node1(x_1235, x_1252, x_1254);
lean_inc(x_1235);
x_1256 = l_Lean_Syntax_node1(x_1235, x_1249, x_1255);
lean_inc(x_1235);
x_1257 = l_Lean_Syntax_node1(x_1235, x_1247, x_1256);
lean_inc(x_1235);
x_1258 = l_Lean_Syntax_node1(x_1235, x_1244, x_1257);
x_1259 = lean_mk_syntax_ident(x_1229);
lean_inc(x_1235);
x_1260 = l_Lean_Syntax_node2(x_1235, x_1242, x_1258, x_1259);
x_1261 = l_Lean_Syntax_node1(x_1235, x_1240, x_1260);
x_16 = x_23;
x_17 = x_1261;
x_18 = x_1232;
goto block_22;
}
case 8:
{
lean_object* x_1262; lean_object* x_1263; lean_object* x_1264; lean_object* x_1265; lean_object* x_1266; lean_object* x_1267; lean_object* x_1268; lean_object* x_1269; lean_object* x_1270; lean_object* x_1271; lean_object* x_1272; lean_object* x_1273; lean_object* x_1274; lean_object* x_1275; lean_object* x_1276; lean_object* x_1277; lean_object* x_1278; lean_object* x_1279; lean_object* x_1280; lean_object* x_1281; 
lean_dec(x_1003);
x_1262 = lean_ctor_get(x_1004, 0);
lean_inc(x_1262);
x_1263 = lean_ctor_get(x_1004, 1);
lean_inc(x_1263);
lean_dec(x_1004);
x_1264 = lean_st_ref_get(x_7, x_1263);
x_1265 = lean_ctor_get(x_1264, 1);
lean_inc(x_1265);
lean_dec(x_1264);
x_1266 = lean_ctor_get(x_6, 5);
lean_inc(x_1266);
x_1267 = l_Lean_SourceInfo_fromRef(x_1266, x_999);
lean_dec(x_1266);
x_1268 = lean_mk_string_unchecked("Lean", 4, 4);
x_1269 = lean_mk_string_unchecked("Parser", 6, 6);
x_1270 = lean_mk_string_unchecked("Tactic", 6, 6);
x_1271 = lean_mk_string_unchecked("grindParam", 10, 10);
lean_inc(x_1270);
lean_inc(x_1269);
lean_inc(x_1268);
x_1272 = l_Lean_Name_mkStr4(x_1268, x_1269, x_1270, x_1271);
x_1273 = lean_mk_string_unchecked("grindLemma", 10, 10);
x_1274 = l_Lean_Name_mkStr4(x_1268, x_1269, x_1270, x_1273);
x_1275 = lean_mk_string_unchecked("null", 4, 4);
x_1276 = l_Lean_Name_mkStr1(x_1275);
x_1277 = l_Array_mkArray0(lean_box(0));
lean_inc(x_1267);
x_1278 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1278, 0, x_1267);
lean_ctor_set(x_1278, 1, x_1276);
lean_ctor_set(x_1278, 2, x_1277);
x_1279 = lean_mk_syntax_ident(x_1262);
lean_inc(x_1267);
x_1280 = l_Lean_Syntax_node2(x_1267, x_1274, x_1278, x_1279);
x_1281 = l_Lean_Syntax_node1(x_1267, x_1272, x_1280);
x_16 = x_23;
x_17 = x_1281;
x_18 = x_1265;
goto block_22;
}
default: 
{
lean_object* x_1282; lean_object* x_1283; lean_object* x_1284; lean_object* x_1285; lean_object* x_1286; lean_object* x_1287; lean_object* x_1288; lean_object* x_1289; lean_object* x_1290; lean_object* x_1291; lean_object* x_1292; lean_object* x_1293; lean_object* x_1294; lean_object* x_1295; lean_object* x_1296; lean_object* x_1297; lean_object* x_1298; lean_object* x_1299; lean_object* x_1300; lean_object* x_1301; lean_object* x_1302; lean_object* x_1303; lean_object* x_1304; lean_object* x_1305; lean_object* x_1306; lean_object* x_1307; lean_object* x_1308; lean_object* x_1309; lean_object* x_1310; 
lean_dec(x_1003);
x_1282 = lean_ctor_get(x_1004, 0);
lean_inc(x_1282);
x_1283 = lean_ctor_get(x_1004, 1);
lean_inc(x_1283);
lean_dec(x_1004);
x_1284 = lean_st_ref_get(x_7, x_1283);
x_1285 = lean_ctor_get(x_1284, 1);
lean_inc(x_1285);
if (lean_is_exclusive(x_1284)) {
 lean_ctor_release(x_1284, 0);
 lean_ctor_release(x_1284, 1);
 x_1286 = x_1284;
} else {
 lean_dec_ref(x_1284);
 x_1286 = lean_box(0);
}
x_1287 = lean_ctor_get(x_6, 5);
lean_inc(x_1287);
x_1288 = l_Lean_SourceInfo_fromRef(x_1287, x_999);
lean_dec(x_1287);
x_1289 = lean_mk_string_unchecked("Lean", 4, 4);
x_1290 = lean_mk_string_unchecked("Parser", 6, 6);
x_1291 = lean_mk_string_unchecked("Tactic", 6, 6);
x_1292 = lean_mk_string_unchecked("grindParam", 10, 10);
lean_inc(x_1291);
lean_inc(x_1290);
lean_inc(x_1289);
x_1293 = l_Lean_Name_mkStr4(x_1289, x_1290, x_1291, x_1292);
x_1294 = lean_mk_string_unchecked("grindLemma", 10, 10);
lean_inc(x_1290);
lean_inc(x_1289);
x_1295 = l_Lean_Name_mkStr4(x_1289, x_1290, x_1291, x_1294);
x_1296 = lean_mk_string_unchecked("null", 4, 4);
x_1297 = l_Lean_Name_mkStr1(x_1296);
x_1298 = lean_mk_string_unchecked("Attr", 4, 4);
x_1299 = lean_mk_string_unchecked("grindMod", 8, 8);
lean_inc(x_1298);
lean_inc(x_1290);
lean_inc(x_1289);
x_1300 = l_Lean_Name_mkStr4(x_1289, x_1290, x_1298, x_1299);
x_1301 = lean_mk_string_unchecked("grindUsr", 8, 8);
x_1302 = l_Lean_Name_mkStr4(x_1289, x_1290, x_1298, x_1301);
x_1303 = lean_mk_string_unchecked("usr", 3, 3);
lean_inc(x_1288);
if (lean_is_scalar(x_1286)) {
 x_1304 = lean_alloc_ctor(2, 2, 0);
} else {
 x_1304 = x_1286;
 lean_ctor_set_tag(x_1304, 2);
}
lean_ctor_set(x_1304, 0, x_1288);
lean_ctor_set(x_1304, 1, x_1303);
lean_inc(x_1288);
x_1305 = l_Lean_Syntax_node1(x_1288, x_1302, x_1304);
lean_inc(x_1288);
x_1306 = l_Lean_Syntax_node1(x_1288, x_1300, x_1305);
lean_inc(x_1288);
x_1307 = l_Lean_Syntax_node1(x_1288, x_1297, x_1306);
x_1308 = lean_mk_syntax_ident(x_1282);
lean_inc(x_1288);
x_1309 = l_Lean_Syntax_node2(x_1288, x_1295, x_1307, x_1308);
x_1310 = l_Lean_Syntax_node1(x_1288, x_1293, x_1309);
x_16 = x_23;
x_17 = x_1310;
x_18 = x_1285;
goto block_22;
}
}
}
else
{
lean_object* x_1311; lean_object* x_1312; lean_object* x_1313; lean_object* x_1314; 
lean_dec(x_1003);
lean_dec(x_23);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_1311 = lean_ctor_get(x_1004, 0);
lean_inc(x_1311);
x_1312 = lean_ctor_get(x_1004, 1);
lean_inc(x_1312);
if (lean_is_exclusive(x_1004)) {
 lean_ctor_release(x_1004, 0);
 lean_ctor_release(x_1004, 1);
 x_1313 = x_1004;
} else {
 lean_dec_ref(x_1004);
 x_1313 = lean_box(0);
}
if (lean_is_scalar(x_1313)) {
 x_1314 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1314 = x_1313;
}
lean_ctor_set(x_1314, 0, x_1311);
lean_ctor_set(x_1314, 1, x_1312);
return x_1314;
}
}
else
{
lean_object* x_1315; lean_object* x_1316; lean_object* x_1317; uint8_t x_1318; 
lean_dec(x_24);
lean_dec(x_12);
x_1315 = lean_ctor_get(x_1000, 1);
lean_inc(x_1315);
if (lean_is_exclusive(x_1000)) {
 lean_ctor_release(x_1000, 0);
 lean_ctor_release(x_1000, 1);
 x_1316 = x_1000;
} else {
 lean_dec_ref(x_1000);
 x_1316 = lean_box(0);
}
x_1317 = lean_ctor_get(x_1001, 0);
lean_inc(x_1317);
lean_dec(x_1001);
x_1318 = l_Lean_NameSet_contains(x_15, x_1317);
if (x_1318 == 0)
{
lean_object* x_1319; 
lean_dec(x_1316);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1317);
x_1319 = l_Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0(x_1317, x_1318, x_4, x_5, x_6, x_7, x_1315);
if (lean_obj_tag(x_1319) == 0)
{
lean_object* x_1320; lean_object* x_1321; lean_object* x_1322; lean_object* x_1323; lean_object* x_1324; lean_object* x_1325; lean_object* x_1326; lean_object* x_1327; lean_object* x_1328; lean_object* x_1329; lean_object* x_1330; lean_object* x_1331; lean_object* x_1332; lean_object* x_1333; lean_object* x_1334; lean_object* x_1335; lean_object* x_1336; lean_object* x_1337; lean_object* x_1338; lean_object* x_1339; lean_object* x_1340; lean_object* x_1341; lean_object* x_1342; lean_object* x_1343; lean_object* x_1344; 
x_1320 = lean_ctor_get(x_1319, 0);
lean_inc(x_1320);
x_1321 = lean_ctor_get(x_1319, 1);
lean_inc(x_1321);
lean_dec(x_1319);
x_1322 = lean_st_ref_get(x_7, x_1321);
x_1323 = lean_ctor_get(x_1322, 1);
lean_inc(x_1323);
if (lean_is_exclusive(x_1322)) {
 lean_ctor_release(x_1322, 0);
 lean_ctor_release(x_1322, 1);
 x_1324 = x_1322;
} else {
 lean_dec_ref(x_1322);
 x_1324 = lean_box(0);
}
x_1325 = lean_ctor_get(x_6, 5);
lean_inc(x_1325);
x_1326 = l_Lean_NameSet_insert(x_15, x_1317);
x_1327 = l_Lean_SourceInfo_fromRef(x_1325, x_1318);
lean_dec(x_1325);
x_1328 = lean_mk_string_unchecked("Lean", 4, 4);
x_1329 = lean_mk_string_unchecked("Parser", 6, 6);
x_1330 = lean_mk_string_unchecked("Tactic", 6, 6);
x_1331 = lean_mk_string_unchecked("grindParam", 10, 10);
lean_inc(x_1330);
lean_inc(x_1329);
lean_inc(x_1328);
x_1332 = l_Lean_Name_mkStr4(x_1328, x_1329, x_1330, x_1331);
x_1333 = lean_mk_string_unchecked("grindLemma", 10, 10);
x_1334 = l_Lean_Name_mkStr4(x_1328, x_1329, x_1330, x_1333);
x_1335 = lean_mk_string_unchecked("null", 4, 4);
x_1336 = l_Lean_Name_mkStr1(x_1335);
x_1337 = l_Array_mkArray0(lean_box(0));
lean_inc(x_1327);
x_1338 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1338, 0, x_1327);
lean_ctor_set(x_1338, 1, x_1336);
lean_ctor_set(x_1338, 2, x_1337);
x_1339 = lean_mk_syntax_ident(x_1320);
lean_inc(x_1327);
x_1340 = l_Lean_Syntax_node2(x_1327, x_1334, x_1338, x_1339);
x_1341 = l_Lean_Syntax_node1(x_1327, x_1332, x_1340);
x_1342 = lean_array_push(x_23, x_1341);
if (lean_is_scalar(x_1324)) {
 x_1343 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1343 = x_1324;
}
lean_ctor_set(x_1343, 0, x_1326);
lean_ctor_set(x_1343, 1, x_1342);
x_1344 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Tactic_mkGrindOnly_spec__3_spec__3___redArg(x_11, x_1343, x_4, x_5, x_6, x_7, x_1323);
return x_1344;
}
else
{
lean_object* x_1345; lean_object* x_1346; lean_object* x_1347; lean_object* x_1348; 
lean_dec(x_1317);
lean_dec(x_23);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_1345 = lean_ctor_get(x_1319, 0);
lean_inc(x_1345);
x_1346 = lean_ctor_get(x_1319, 1);
lean_inc(x_1346);
if (lean_is_exclusive(x_1319)) {
 lean_ctor_release(x_1319, 0);
 lean_ctor_release(x_1319, 1);
 x_1347 = x_1319;
} else {
 lean_dec_ref(x_1319);
 x_1347 = lean_box(0);
}
if (lean_is_scalar(x_1347)) {
 x_1348 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1348 = x_1347;
}
lean_ctor_set(x_1348, 0, x_1345);
lean_ctor_set(x_1348, 1, x_1346);
return x_1348;
}
}
else
{
lean_object* x_1349; lean_object* x_1350; 
lean_dec(x_1317);
if (lean_is_scalar(x_1316)) {
 x_1349 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1349 = x_1316;
}
lean_ctor_set(x_1349, 0, x_15);
lean_ctor_set(x_1349, 1, x_23);
x_1350 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Tactic_mkGrindOnly_spec__3_spec__3___redArg(x_11, x_1349, x_4, x_5, x_6, x_7, x_1315);
return x_1350;
}
}
}
else
{
lean_object* x_1351; lean_object* x_1352; 
lean_dec(x_24);
lean_dec(x_12);
x_1351 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1351, 0, x_15);
lean_ctor_set(x_1351, 1, x_23);
x_1352 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Tactic_mkGrindOnly_spec__3_spec__3___redArg(x_11, x_1351, x_4, x_5, x_6, x_7, x_997);
return x_1352;
}
}
}
else
{
lean_object* x_1353; lean_object* x_1354; lean_object* x_1355; 
lean_dec(x_13);
lean_dec(x_12);
x_1353 = lean_ctor_get(x_3, 1);
lean_inc(x_1353);
lean_dec(x_3);
x_1354 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1354, 0, x_15);
lean_ctor_set(x_1354, 1, x_1353);
x_1355 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Tactic_mkGrindOnly_spec__3_spec__3___redArg(x_11, x_1354, x_4, x_5, x_6, x_7, x_8);
return x_1355;
}
block_22:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_array_push(x_16, x_17);
if (lean_is_scalar(x_12)) {
 x_20 = lean_alloc_ctor(0, 2, 0);
} else {
 x_20 = x_12;
 lean_ctor_set_tag(x_20, 0);
}
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Tactic_mkGrindOnly_spec__3_spec__3___redArg(x_11, x_20, x_4, x_5, x_6, x_7, x_18);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Elab_Tactic_mkGrindOnly_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_List_forIn_x27_loop___at___Lean_Elab_Tactic_mkGrindOnly_spec__3___redArg(x_1, x_2, x_3, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_PersistentHashSet_toList___at___Lean_Elab_Tactic_mkGrindOnly_spec__5_spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_7);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_2);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_toList___at___Lean_Elab_Tactic_mkGrindOnly_spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_PersistentHashMap_toList___at___Lean_Environment_dbgFormatAsyncState_spec__14___redArg(x_1);
x_3 = lean_box(0);
x_4 = l_List_mapTR_loop___at___Lean_PersistentHashSet_toList___at___Lean_Elab_Tactic_mkGrindOnly_spec__5_spec__5(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Tactic_mkGrindOnly_spec__7_spec__7___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
x_12 = l_Lean_Meta_Grind_isBuiltinEagerCases(x_10);
if (x_12 == 0)
{
lean_object* x_13; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_13 = l_Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0(x_10, x_12, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_st_ref_get(x_6, x_15);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_18 = lean_ctor_get(x_16, 1);
x_19 = lean_ctor_get(x_16, 0);
lean_dec(x_19);
x_20 = lean_ctor_get(x_5, 5);
lean_inc(x_20);
x_21 = l_Lean_SourceInfo_fromRef(x_20, x_12);
lean_dec(x_20);
x_22 = lean_mk_string_unchecked("Lean", 4, 4);
x_23 = lean_mk_string_unchecked("Parser", 6, 6);
x_24 = lean_mk_string_unchecked("Tactic", 6, 6);
x_25 = lean_mk_string_unchecked("grindParam", 10, 10);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
x_26 = l_Lean_Name_mkStr4(x_22, x_23, x_24, x_25);
x_27 = lean_mk_string_unchecked("grindLemma", 10, 10);
lean_inc(x_23);
lean_inc(x_22);
x_28 = l_Lean_Name_mkStr4(x_22, x_23, x_24, x_27);
x_29 = lean_mk_string_unchecked("null", 4, 4);
x_30 = l_Lean_Name_mkStr1(x_29);
x_31 = lean_mk_string_unchecked("Attr", 4, 4);
x_32 = lean_mk_string_unchecked("grindMod", 8, 8);
lean_inc(x_31);
lean_inc(x_23);
lean_inc(x_22);
x_33 = l_Lean_Name_mkStr4(x_22, x_23, x_31, x_32);
x_34 = lean_mk_string_unchecked("grindCasesEager", 15, 15);
x_35 = l_Lean_Name_mkStr4(x_22, x_23, x_31, x_34);
x_36 = lean_mk_string_unchecked("cases", 5, 5);
lean_inc(x_21);
lean_ctor_set_tag(x_16, 2);
lean_ctor_set(x_16, 1, x_36);
lean_ctor_set(x_16, 0, x_21);
x_37 = lean_mk_string_unchecked("eager", 5, 5);
lean_inc(x_21);
lean_ctor_set_tag(x_1, 2);
lean_ctor_set(x_1, 1, x_37);
lean_ctor_set(x_1, 0, x_21);
lean_inc(x_21);
x_38 = l_Lean_Syntax_node2(x_21, x_35, x_16, x_1);
lean_inc(x_21);
x_39 = l_Lean_Syntax_node1(x_21, x_33, x_38);
lean_inc(x_21);
x_40 = l_Lean_Syntax_node1(x_21, x_30, x_39);
x_41 = lean_mk_syntax_ident(x_14);
lean_inc(x_21);
x_42 = l_Lean_Syntax_node2(x_21, x_28, x_40, x_41);
x_43 = l_Lean_Syntax_node1(x_21, x_26, x_42);
x_44 = lean_array_push(x_2, x_43);
x_1 = x_11;
x_2 = x_44;
x_7 = x_18;
goto _start;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_46 = lean_ctor_get(x_16, 1);
lean_inc(x_46);
lean_dec(x_16);
x_47 = lean_ctor_get(x_5, 5);
lean_inc(x_47);
x_48 = l_Lean_SourceInfo_fromRef(x_47, x_12);
lean_dec(x_47);
x_49 = lean_mk_string_unchecked("Lean", 4, 4);
x_50 = lean_mk_string_unchecked("Parser", 6, 6);
x_51 = lean_mk_string_unchecked("Tactic", 6, 6);
x_52 = lean_mk_string_unchecked("grindParam", 10, 10);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
x_53 = l_Lean_Name_mkStr4(x_49, x_50, x_51, x_52);
x_54 = lean_mk_string_unchecked("grindLemma", 10, 10);
lean_inc(x_50);
lean_inc(x_49);
x_55 = l_Lean_Name_mkStr4(x_49, x_50, x_51, x_54);
x_56 = lean_mk_string_unchecked("null", 4, 4);
x_57 = l_Lean_Name_mkStr1(x_56);
x_58 = lean_mk_string_unchecked("Attr", 4, 4);
x_59 = lean_mk_string_unchecked("grindMod", 8, 8);
lean_inc(x_58);
lean_inc(x_50);
lean_inc(x_49);
x_60 = l_Lean_Name_mkStr4(x_49, x_50, x_58, x_59);
x_61 = lean_mk_string_unchecked("grindCasesEager", 15, 15);
x_62 = l_Lean_Name_mkStr4(x_49, x_50, x_58, x_61);
x_63 = lean_mk_string_unchecked("cases", 5, 5);
lean_inc(x_48);
x_64 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_64, 0, x_48);
lean_ctor_set(x_64, 1, x_63);
x_65 = lean_mk_string_unchecked("eager", 5, 5);
lean_inc(x_48);
lean_ctor_set_tag(x_1, 2);
lean_ctor_set(x_1, 1, x_65);
lean_ctor_set(x_1, 0, x_48);
lean_inc(x_48);
x_66 = l_Lean_Syntax_node2(x_48, x_62, x_64, x_1);
lean_inc(x_48);
x_67 = l_Lean_Syntax_node1(x_48, x_60, x_66);
lean_inc(x_48);
x_68 = l_Lean_Syntax_node1(x_48, x_57, x_67);
x_69 = lean_mk_syntax_ident(x_14);
lean_inc(x_48);
x_70 = l_Lean_Syntax_node2(x_48, x_55, x_68, x_69);
x_71 = l_Lean_Syntax_node1(x_48, x_53, x_70);
x_72 = lean_array_push(x_2, x_71);
x_1 = x_11;
x_2 = x_72;
x_7 = x_46;
goto _start;
}
}
else
{
uint8_t x_74; 
lean_free_object(x_1);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_74 = !lean_is_exclusive(x_13);
if (x_74 == 0)
{
return x_13;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_13, 0);
x_76 = lean_ctor_get(x_13, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_13);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
else
{
lean_free_object(x_1);
lean_dec(x_10);
x_1 = x_11;
goto _start;
}
}
else
{
lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_79 = lean_ctor_get(x_1, 0);
x_80 = lean_ctor_get(x_1, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_1);
x_81 = l_Lean_Meta_Grind_isBuiltinEagerCases(x_79);
if (x_81 == 0)
{
lean_object* x_82; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_82 = l_Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0(x_79, x_81, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = lean_st_ref_get(x_6, x_84);
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_87 = x_85;
} else {
 lean_dec_ref(x_85);
 x_87 = lean_box(0);
}
x_88 = lean_ctor_get(x_5, 5);
lean_inc(x_88);
x_89 = l_Lean_SourceInfo_fromRef(x_88, x_81);
lean_dec(x_88);
x_90 = lean_mk_string_unchecked("Lean", 4, 4);
x_91 = lean_mk_string_unchecked("Parser", 6, 6);
x_92 = lean_mk_string_unchecked("Tactic", 6, 6);
x_93 = lean_mk_string_unchecked("grindParam", 10, 10);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
x_94 = l_Lean_Name_mkStr4(x_90, x_91, x_92, x_93);
x_95 = lean_mk_string_unchecked("grindLemma", 10, 10);
lean_inc(x_91);
lean_inc(x_90);
x_96 = l_Lean_Name_mkStr4(x_90, x_91, x_92, x_95);
x_97 = lean_mk_string_unchecked("null", 4, 4);
x_98 = l_Lean_Name_mkStr1(x_97);
x_99 = lean_mk_string_unchecked("Attr", 4, 4);
x_100 = lean_mk_string_unchecked("grindMod", 8, 8);
lean_inc(x_99);
lean_inc(x_91);
lean_inc(x_90);
x_101 = l_Lean_Name_mkStr4(x_90, x_91, x_99, x_100);
x_102 = lean_mk_string_unchecked("grindCasesEager", 15, 15);
x_103 = l_Lean_Name_mkStr4(x_90, x_91, x_99, x_102);
x_104 = lean_mk_string_unchecked("cases", 5, 5);
lean_inc(x_89);
if (lean_is_scalar(x_87)) {
 x_105 = lean_alloc_ctor(2, 2, 0);
} else {
 x_105 = x_87;
 lean_ctor_set_tag(x_105, 2);
}
lean_ctor_set(x_105, 0, x_89);
lean_ctor_set(x_105, 1, x_104);
x_106 = lean_mk_string_unchecked("eager", 5, 5);
lean_inc(x_89);
x_107 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_107, 0, x_89);
lean_ctor_set(x_107, 1, x_106);
lean_inc(x_89);
x_108 = l_Lean_Syntax_node2(x_89, x_103, x_105, x_107);
lean_inc(x_89);
x_109 = l_Lean_Syntax_node1(x_89, x_101, x_108);
lean_inc(x_89);
x_110 = l_Lean_Syntax_node1(x_89, x_98, x_109);
x_111 = lean_mk_syntax_ident(x_83);
lean_inc(x_89);
x_112 = l_Lean_Syntax_node2(x_89, x_96, x_110, x_111);
x_113 = l_Lean_Syntax_node1(x_89, x_94, x_112);
x_114 = lean_array_push(x_2, x_113);
x_1 = x_80;
x_2 = x_114;
x_7 = x_86;
goto _start;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_80);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_116 = lean_ctor_get(x_82, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_82, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_118 = x_82;
} else {
 lean_dec_ref(x_82);
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
lean_dec(x_79);
x_1 = x_80;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Tactic_mkGrindOnly_spec__7_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Tactic_mkGrindOnly_spec__7_spec__7___redArg(x_2, x_3, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Elab_Tactic_mkGrindOnly_spec__7___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_ctor_get(x_2, 1);
x_13 = l_Lean_Meta_Grind_isBuiltinEagerCases(x_11);
if (x_13 == 0)
{
lean_object* x_14; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_14 = l_Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0(x_11, x_13, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_st_ref_get(x_7, x_16);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_19 = lean_ctor_get(x_17, 1);
x_20 = lean_ctor_get(x_17, 0);
lean_dec(x_20);
x_21 = lean_ctor_get(x_6, 5);
lean_inc(x_21);
x_22 = l_Lean_SourceInfo_fromRef(x_21, x_13);
lean_dec(x_21);
x_23 = lean_mk_string_unchecked("Lean", 4, 4);
x_24 = lean_mk_string_unchecked("Parser", 6, 6);
x_25 = lean_mk_string_unchecked("Tactic", 6, 6);
x_26 = lean_mk_string_unchecked("grindParam", 10, 10);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
x_27 = l_Lean_Name_mkStr4(x_23, x_24, x_25, x_26);
x_28 = lean_mk_string_unchecked("grindLemma", 10, 10);
lean_inc(x_24);
lean_inc(x_23);
x_29 = l_Lean_Name_mkStr4(x_23, x_24, x_25, x_28);
x_30 = lean_mk_string_unchecked("null", 4, 4);
x_31 = l_Lean_Name_mkStr1(x_30);
x_32 = lean_mk_string_unchecked("Attr", 4, 4);
x_33 = lean_mk_string_unchecked("grindMod", 8, 8);
lean_inc(x_32);
lean_inc(x_24);
lean_inc(x_23);
x_34 = l_Lean_Name_mkStr4(x_23, x_24, x_32, x_33);
x_35 = lean_mk_string_unchecked("grindCasesEager", 15, 15);
x_36 = l_Lean_Name_mkStr4(x_23, x_24, x_32, x_35);
x_37 = lean_mk_string_unchecked("cases", 5, 5);
lean_inc(x_22);
lean_ctor_set_tag(x_17, 2);
lean_ctor_set(x_17, 1, x_37);
lean_ctor_set(x_17, 0, x_22);
x_38 = lean_mk_string_unchecked("eager", 5, 5);
lean_inc(x_22);
lean_ctor_set_tag(x_2, 2);
lean_ctor_set(x_2, 1, x_38);
lean_ctor_set(x_2, 0, x_22);
lean_inc(x_22);
x_39 = l_Lean_Syntax_node2(x_22, x_36, x_17, x_2);
lean_inc(x_22);
x_40 = l_Lean_Syntax_node1(x_22, x_34, x_39);
lean_inc(x_22);
x_41 = l_Lean_Syntax_node1(x_22, x_31, x_40);
x_42 = lean_mk_syntax_ident(x_15);
lean_inc(x_22);
x_43 = l_Lean_Syntax_node2(x_22, x_29, x_41, x_42);
x_44 = l_Lean_Syntax_node1(x_22, x_27, x_43);
x_45 = lean_array_push(x_3, x_44);
x_46 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Tactic_mkGrindOnly_spec__7_spec__7___redArg(x_12, x_45, x_4, x_5, x_6, x_7, x_19);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_47 = lean_ctor_get(x_17, 1);
lean_inc(x_47);
lean_dec(x_17);
x_48 = lean_ctor_get(x_6, 5);
lean_inc(x_48);
x_49 = l_Lean_SourceInfo_fromRef(x_48, x_13);
lean_dec(x_48);
x_50 = lean_mk_string_unchecked("Lean", 4, 4);
x_51 = lean_mk_string_unchecked("Parser", 6, 6);
x_52 = lean_mk_string_unchecked("Tactic", 6, 6);
x_53 = lean_mk_string_unchecked("grindParam", 10, 10);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
x_54 = l_Lean_Name_mkStr4(x_50, x_51, x_52, x_53);
x_55 = lean_mk_string_unchecked("grindLemma", 10, 10);
lean_inc(x_51);
lean_inc(x_50);
x_56 = l_Lean_Name_mkStr4(x_50, x_51, x_52, x_55);
x_57 = lean_mk_string_unchecked("null", 4, 4);
x_58 = l_Lean_Name_mkStr1(x_57);
x_59 = lean_mk_string_unchecked("Attr", 4, 4);
x_60 = lean_mk_string_unchecked("grindMod", 8, 8);
lean_inc(x_59);
lean_inc(x_51);
lean_inc(x_50);
x_61 = l_Lean_Name_mkStr4(x_50, x_51, x_59, x_60);
x_62 = lean_mk_string_unchecked("grindCasesEager", 15, 15);
x_63 = l_Lean_Name_mkStr4(x_50, x_51, x_59, x_62);
x_64 = lean_mk_string_unchecked("cases", 5, 5);
lean_inc(x_49);
x_65 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_65, 0, x_49);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_mk_string_unchecked("eager", 5, 5);
lean_inc(x_49);
lean_ctor_set_tag(x_2, 2);
lean_ctor_set(x_2, 1, x_66);
lean_ctor_set(x_2, 0, x_49);
lean_inc(x_49);
x_67 = l_Lean_Syntax_node2(x_49, x_63, x_65, x_2);
lean_inc(x_49);
x_68 = l_Lean_Syntax_node1(x_49, x_61, x_67);
lean_inc(x_49);
x_69 = l_Lean_Syntax_node1(x_49, x_58, x_68);
x_70 = lean_mk_syntax_ident(x_15);
lean_inc(x_49);
x_71 = l_Lean_Syntax_node2(x_49, x_56, x_69, x_70);
x_72 = l_Lean_Syntax_node1(x_49, x_54, x_71);
x_73 = lean_array_push(x_3, x_72);
x_74 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Tactic_mkGrindOnly_spec__7_spec__7___redArg(x_12, x_73, x_4, x_5, x_6, x_7, x_47);
return x_74;
}
}
else
{
uint8_t x_75; 
lean_free_object(x_2);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_75 = !lean_is_exclusive(x_14);
if (x_75 == 0)
{
return x_14;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_14, 0);
x_77 = lean_ctor_get(x_14, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_14);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
else
{
lean_object* x_79; 
lean_free_object(x_2);
lean_dec(x_11);
x_79 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Tactic_mkGrindOnly_spec__7_spec__7___redArg(x_12, x_3, x_4, x_5, x_6, x_7, x_8);
return x_79;
}
}
else
{
lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_80 = lean_ctor_get(x_2, 0);
x_81 = lean_ctor_get(x_2, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_2);
x_82 = l_Lean_Meta_Grind_isBuiltinEagerCases(x_80);
if (x_82 == 0)
{
lean_object* x_83; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_83 = l_Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0(x_80, x_82, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_86 = lean_st_ref_get(x_7, x_85);
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_88 = x_86;
} else {
 lean_dec_ref(x_86);
 x_88 = lean_box(0);
}
x_89 = lean_ctor_get(x_6, 5);
lean_inc(x_89);
x_90 = l_Lean_SourceInfo_fromRef(x_89, x_82);
lean_dec(x_89);
x_91 = lean_mk_string_unchecked("Lean", 4, 4);
x_92 = lean_mk_string_unchecked("Parser", 6, 6);
x_93 = lean_mk_string_unchecked("Tactic", 6, 6);
x_94 = lean_mk_string_unchecked("grindParam", 10, 10);
lean_inc(x_93);
lean_inc(x_92);
lean_inc(x_91);
x_95 = l_Lean_Name_mkStr4(x_91, x_92, x_93, x_94);
x_96 = lean_mk_string_unchecked("grindLemma", 10, 10);
lean_inc(x_92);
lean_inc(x_91);
x_97 = l_Lean_Name_mkStr4(x_91, x_92, x_93, x_96);
x_98 = lean_mk_string_unchecked("null", 4, 4);
x_99 = l_Lean_Name_mkStr1(x_98);
x_100 = lean_mk_string_unchecked("Attr", 4, 4);
x_101 = lean_mk_string_unchecked("grindMod", 8, 8);
lean_inc(x_100);
lean_inc(x_92);
lean_inc(x_91);
x_102 = l_Lean_Name_mkStr4(x_91, x_92, x_100, x_101);
x_103 = lean_mk_string_unchecked("grindCasesEager", 15, 15);
x_104 = l_Lean_Name_mkStr4(x_91, x_92, x_100, x_103);
x_105 = lean_mk_string_unchecked("cases", 5, 5);
lean_inc(x_90);
if (lean_is_scalar(x_88)) {
 x_106 = lean_alloc_ctor(2, 2, 0);
} else {
 x_106 = x_88;
 lean_ctor_set_tag(x_106, 2);
}
lean_ctor_set(x_106, 0, x_90);
lean_ctor_set(x_106, 1, x_105);
x_107 = lean_mk_string_unchecked("eager", 5, 5);
lean_inc(x_90);
x_108 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_108, 0, x_90);
lean_ctor_set(x_108, 1, x_107);
lean_inc(x_90);
x_109 = l_Lean_Syntax_node2(x_90, x_104, x_106, x_108);
lean_inc(x_90);
x_110 = l_Lean_Syntax_node1(x_90, x_102, x_109);
lean_inc(x_90);
x_111 = l_Lean_Syntax_node1(x_90, x_99, x_110);
x_112 = lean_mk_syntax_ident(x_84);
lean_inc(x_90);
x_113 = l_Lean_Syntax_node2(x_90, x_97, x_111, x_112);
x_114 = l_Lean_Syntax_node1(x_90, x_95, x_113);
x_115 = lean_array_push(x_3, x_114);
x_116 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Tactic_mkGrindOnly_spec__7_spec__7___redArg(x_81, x_115, x_4, x_5, x_6, x_7, x_87);
return x_116;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec(x_81);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_117 = lean_ctor_get(x_83, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_83, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_119 = x_83;
} else {
 lean_dec_ref(x_83);
 x_119 = lean_box(0);
}
if (lean_is_scalar(x_119)) {
 x_120 = lean_alloc_ctor(1, 2, 0);
} else {
 x_120 = x_119;
}
lean_ctor_set(x_120, 0, x_117);
lean_ctor_set(x_120, 1, x_118);
return x_120;
}
}
else
{
lean_object* x_121; 
lean_dec(x_80);
x_121 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Tactic_mkGrindOnly_spec__7_spec__7___redArg(x_81, x_3, x_4, x_5, x_6, x_7, x_8);
return x_121;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Elab_Tactic_mkGrindOnly_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_List_forIn_x27_loop___at___Lean_Elab_Tactic_mkGrindOnly_spec__7___redArg(x_1, x_2, x_3, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Tactic_mkGrindOnly_spec__9_spec__9___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_9; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_78; uint8_t x_79; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_dec(x_2);
x_78 = lean_ctor_get(x_1, 1);
lean_inc(x_78);
x_79 = l_Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_Environment_addExtraName_spec__0_spec__0(lean_box(0), x_78, x_10);
if (x_79 == 0)
{
uint8_t x_80; 
x_80 = l_Lean_Meta_Grind_isBuiltinEagerCases(x_10);
x_12 = x_80;
goto block_77;
}
else
{
x_12 = x_79;
goto block_77;
}
block_77:
{
if (x_12 == 0)
{
lean_object* x_13; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_13 = l_Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0(x_10, x_12, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_st_ref_get(x_7, x_15);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_18 = lean_ctor_get(x_16, 1);
x_19 = lean_ctor_get(x_16, 0);
lean_dec(x_19);
x_20 = lean_ctor_get(x_6, 5);
lean_inc(x_20);
x_21 = l_Lean_SourceInfo_fromRef(x_20, x_12);
lean_dec(x_20);
x_22 = lean_mk_string_unchecked("Lean", 4, 4);
x_23 = lean_mk_string_unchecked("Parser", 6, 6);
x_24 = lean_mk_string_unchecked("Tactic", 6, 6);
x_25 = lean_mk_string_unchecked("grindParam", 10, 10);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
x_26 = l_Lean_Name_mkStr4(x_22, x_23, x_24, x_25);
x_27 = lean_mk_string_unchecked("grindLemma", 10, 10);
lean_inc(x_23);
lean_inc(x_22);
x_28 = l_Lean_Name_mkStr4(x_22, x_23, x_24, x_27);
x_29 = lean_mk_string_unchecked("null", 4, 4);
x_30 = l_Lean_Name_mkStr1(x_29);
x_31 = lean_mk_string_unchecked("Attr", 4, 4);
x_32 = lean_mk_string_unchecked("grindMod", 8, 8);
lean_inc(x_31);
lean_inc(x_23);
lean_inc(x_22);
x_33 = l_Lean_Name_mkStr4(x_22, x_23, x_31, x_32);
x_34 = lean_mk_string_unchecked("grindCases", 10, 10);
x_35 = l_Lean_Name_mkStr4(x_22, x_23, x_31, x_34);
x_36 = lean_mk_string_unchecked("cases", 5, 5);
lean_inc(x_21);
lean_ctor_set_tag(x_16, 2);
lean_ctor_set(x_16, 1, x_36);
lean_ctor_set(x_16, 0, x_21);
lean_inc(x_21);
x_37 = l_Lean_Syntax_node1(x_21, x_35, x_16);
lean_inc(x_21);
x_38 = l_Lean_Syntax_node1(x_21, x_33, x_37);
lean_inc(x_21);
x_39 = l_Lean_Syntax_node1(x_21, x_30, x_38);
x_40 = lean_mk_syntax_ident(x_14);
lean_inc(x_21);
x_41 = l_Lean_Syntax_node2(x_21, x_28, x_39, x_40);
x_42 = l_Lean_Syntax_node1(x_21, x_26, x_41);
x_43 = lean_array_push(x_3, x_42);
x_2 = x_11;
x_3 = x_43;
x_8 = x_18;
goto _start;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_45 = lean_ctor_get(x_16, 1);
lean_inc(x_45);
lean_dec(x_16);
x_46 = lean_ctor_get(x_6, 5);
lean_inc(x_46);
x_47 = l_Lean_SourceInfo_fromRef(x_46, x_12);
lean_dec(x_46);
x_48 = lean_mk_string_unchecked("Lean", 4, 4);
x_49 = lean_mk_string_unchecked("Parser", 6, 6);
x_50 = lean_mk_string_unchecked("Tactic", 6, 6);
x_51 = lean_mk_string_unchecked("grindParam", 10, 10);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
x_52 = l_Lean_Name_mkStr4(x_48, x_49, x_50, x_51);
x_53 = lean_mk_string_unchecked("grindLemma", 10, 10);
lean_inc(x_49);
lean_inc(x_48);
x_54 = l_Lean_Name_mkStr4(x_48, x_49, x_50, x_53);
x_55 = lean_mk_string_unchecked("null", 4, 4);
x_56 = l_Lean_Name_mkStr1(x_55);
x_57 = lean_mk_string_unchecked("Attr", 4, 4);
x_58 = lean_mk_string_unchecked("grindMod", 8, 8);
lean_inc(x_57);
lean_inc(x_49);
lean_inc(x_48);
x_59 = l_Lean_Name_mkStr4(x_48, x_49, x_57, x_58);
x_60 = lean_mk_string_unchecked("grindCases", 10, 10);
x_61 = l_Lean_Name_mkStr4(x_48, x_49, x_57, x_60);
x_62 = lean_mk_string_unchecked("cases", 5, 5);
lean_inc(x_47);
x_63 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_63, 0, x_47);
lean_ctor_set(x_63, 1, x_62);
lean_inc(x_47);
x_64 = l_Lean_Syntax_node1(x_47, x_61, x_63);
lean_inc(x_47);
x_65 = l_Lean_Syntax_node1(x_47, x_59, x_64);
lean_inc(x_47);
x_66 = l_Lean_Syntax_node1(x_47, x_56, x_65);
x_67 = lean_mk_syntax_ident(x_14);
lean_inc(x_47);
x_68 = l_Lean_Syntax_node2(x_47, x_54, x_66, x_67);
x_69 = l_Lean_Syntax_node1(x_47, x_52, x_68);
x_70 = lean_array_push(x_3, x_69);
x_2 = x_11;
x_3 = x_70;
x_8 = x_45;
goto _start;
}
}
else
{
uint8_t x_72; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_72 = !lean_is_exclusive(x_13);
if (x_72 == 0)
{
return x_13;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_13, 0);
x_74 = lean_ctor_get(x_13, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_13);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
else
{
lean_dec(x_10);
x_2 = x_11;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Tactic_mkGrindOnly_spec__9_spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Tactic_mkGrindOnly_spec__9_spec__9___redArg(x_1, x_3, x_4, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Elab_Tactic_mkGrindOnly_spec__9___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_10; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_79; uint8_t x_80; 
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_dec(x_3);
x_79 = lean_ctor_get(x_1, 1);
lean_inc(x_79);
x_80 = l_Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_Environment_addExtraName_spec__0_spec__0(lean_box(0), x_79, x_11);
if (x_80 == 0)
{
uint8_t x_81; 
x_81 = l_Lean_Meta_Grind_isBuiltinEagerCases(x_11);
x_13 = x_81;
goto block_78;
}
else
{
x_13 = x_80;
goto block_78;
}
block_78:
{
if (x_13 == 0)
{
lean_object* x_14; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_14 = l_Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0(x_11, x_13, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_st_ref_get(x_8, x_16);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_19 = lean_ctor_get(x_17, 1);
x_20 = lean_ctor_get(x_17, 0);
lean_dec(x_20);
x_21 = lean_ctor_get(x_7, 5);
lean_inc(x_21);
x_22 = l_Lean_SourceInfo_fromRef(x_21, x_13);
lean_dec(x_21);
x_23 = lean_mk_string_unchecked("Lean", 4, 4);
x_24 = lean_mk_string_unchecked("Parser", 6, 6);
x_25 = lean_mk_string_unchecked("Tactic", 6, 6);
x_26 = lean_mk_string_unchecked("grindParam", 10, 10);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
x_27 = l_Lean_Name_mkStr4(x_23, x_24, x_25, x_26);
x_28 = lean_mk_string_unchecked("grindLemma", 10, 10);
lean_inc(x_24);
lean_inc(x_23);
x_29 = l_Lean_Name_mkStr4(x_23, x_24, x_25, x_28);
x_30 = lean_mk_string_unchecked("null", 4, 4);
x_31 = l_Lean_Name_mkStr1(x_30);
x_32 = lean_mk_string_unchecked("Attr", 4, 4);
x_33 = lean_mk_string_unchecked("grindMod", 8, 8);
lean_inc(x_32);
lean_inc(x_24);
lean_inc(x_23);
x_34 = l_Lean_Name_mkStr4(x_23, x_24, x_32, x_33);
x_35 = lean_mk_string_unchecked("grindCases", 10, 10);
x_36 = l_Lean_Name_mkStr4(x_23, x_24, x_32, x_35);
x_37 = lean_mk_string_unchecked("cases", 5, 5);
lean_inc(x_22);
lean_ctor_set_tag(x_17, 2);
lean_ctor_set(x_17, 1, x_37);
lean_ctor_set(x_17, 0, x_22);
lean_inc(x_22);
x_38 = l_Lean_Syntax_node1(x_22, x_36, x_17);
lean_inc(x_22);
x_39 = l_Lean_Syntax_node1(x_22, x_34, x_38);
lean_inc(x_22);
x_40 = l_Lean_Syntax_node1(x_22, x_31, x_39);
x_41 = lean_mk_syntax_ident(x_15);
lean_inc(x_22);
x_42 = l_Lean_Syntax_node2(x_22, x_29, x_40, x_41);
x_43 = l_Lean_Syntax_node1(x_22, x_27, x_42);
x_44 = lean_array_push(x_4, x_43);
x_45 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Tactic_mkGrindOnly_spec__9_spec__9___redArg(x_1, x_12, x_44, x_5, x_6, x_7, x_8, x_19);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_46 = lean_ctor_get(x_17, 1);
lean_inc(x_46);
lean_dec(x_17);
x_47 = lean_ctor_get(x_7, 5);
lean_inc(x_47);
x_48 = l_Lean_SourceInfo_fromRef(x_47, x_13);
lean_dec(x_47);
x_49 = lean_mk_string_unchecked("Lean", 4, 4);
x_50 = lean_mk_string_unchecked("Parser", 6, 6);
x_51 = lean_mk_string_unchecked("Tactic", 6, 6);
x_52 = lean_mk_string_unchecked("grindParam", 10, 10);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
x_53 = l_Lean_Name_mkStr4(x_49, x_50, x_51, x_52);
x_54 = lean_mk_string_unchecked("grindLemma", 10, 10);
lean_inc(x_50);
lean_inc(x_49);
x_55 = l_Lean_Name_mkStr4(x_49, x_50, x_51, x_54);
x_56 = lean_mk_string_unchecked("null", 4, 4);
x_57 = l_Lean_Name_mkStr1(x_56);
x_58 = lean_mk_string_unchecked("Attr", 4, 4);
x_59 = lean_mk_string_unchecked("grindMod", 8, 8);
lean_inc(x_58);
lean_inc(x_50);
lean_inc(x_49);
x_60 = l_Lean_Name_mkStr4(x_49, x_50, x_58, x_59);
x_61 = lean_mk_string_unchecked("grindCases", 10, 10);
x_62 = l_Lean_Name_mkStr4(x_49, x_50, x_58, x_61);
x_63 = lean_mk_string_unchecked("cases", 5, 5);
lean_inc(x_48);
x_64 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_64, 0, x_48);
lean_ctor_set(x_64, 1, x_63);
lean_inc(x_48);
x_65 = l_Lean_Syntax_node1(x_48, x_62, x_64);
lean_inc(x_48);
x_66 = l_Lean_Syntax_node1(x_48, x_60, x_65);
lean_inc(x_48);
x_67 = l_Lean_Syntax_node1(x_48, x_57, x_66);
x_68 = lean_mk_syntax_ident(x_15);
lean_inc(x_48);
x_69 = l_Lean_Syntax_node2(x_48, x_55, x_67, x_68);
x_70 = l_Lean_Syntax_node1(x_48, x_53, x_69);
x_71 = lean_array_push(x_4, x_70);
x_72 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Tactic_mkGrindOnly_spec__9_spec__9___redArg(x_1, x_12, x_71, x_5, x_6, x_7, x_8, x_46);
return x_72;
}
}
else
{
uint8_t x_73; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_73 = !lean_is_exclusive(x_14);
if (x_73 == 0)
{
return x_14;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_14, 0);
x_75 = lean_ctor_get(x_14, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_14);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
else
{
lean_object* x_77; 
lean_dec(x_11);
x_77 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Tactic_mkGrindOnly_spec__9_spec__9___redArg(x_1, x_12, x_4, x_5, x_6, x_7, x_8, x_9);
return x_77;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Elab_Tactic_mkGrindOnly_spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_List_forIn_x27_loop___at___Lean_Elab_Tactic_mkGrindOnly_spec__9___redArg(x_1, x_2, x_3, x_4, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkGrindOnly(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_mk_empty_array_with_capacity(x_9);
x_11 = lean_box(0);
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
x_13 = l_Lean_PersistentHashSet_toList___at___Lean_Elab_Tactic_mkGrindOnly_spec__0(x_12);
lean_dec(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_10);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_13);
x_15 = l_List_forIn_x27_loop___at___Lean_Elab_Tactic_mkGrindOnly_spec__3___redArg(x_13, x_13, x_14, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_16, 1);
x_20 = lean_ctor_get(x_16, 0);
lean_dec(x_20);
x_21 = lean_ctor_get(x_3, 1);
lean_inc(x_21);
x_22 = l_Lean_PersistentHashSet_toList___at___Lean_Elab_Tactic_mkGrindOnly_spec__5(x_21);
lean_dec(x_21);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_22);
x_23 = l_List_forIn_x27_loop___at___Lean_Elab_Tactic_mkGrindOnly_spec__7___redArg(x_22, x_22, x_19, x_4, x_5, x_6, x_7, x_17);
lean_dec(x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_3, 2);
lean_inc(x_26);
x_27 = l_Lean_PersistentHashSet_toList___at___Lean_Elab_Tactic_mkGrindOnly_spec__5(x_26);
lean_dec(x_26);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_27);
x_28 = l_List_forIn_x27_loop___at___Lean_Elab_Tactic_mkGrindOnly_spec__9___redArg(x_3, x_27, x_27, x_24, x_4, x_5, x_6, x_7, x_25);
lean_dec(x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_31 = x_28;
} else {
 lean_dec_ref(x_28);
 x_31 = lean_box(0);
}
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_st_ref_get(x_7, x_30);
lean_dec(x_7);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_39 = lean_ctor_get(x_37, 1);
x_40 = lean_ctor_get(x_37, 0);
lean_dec(x_40);
x_41 = lean_ctor_get(x_6, 5);
lean_inc(x_41);
lean_dec(x_6);
x_42 = lean_box(0);
x_43 = lean_unbox(x_42);
x_44 = l_Lean_SourceInfo_fromRef(x_41, x_43);
lean_dec(x_41);
x_45 = lean_mk_string_unchecked("Lean", 4, 4);
x_46 = lean_mk_string_unchecked("Parser", 6, 6);
x_47 = lean_mk_string_unchecked("Tactic", 6, 6);
x_48 = lean_mk_string_unchecked("grind", 5, 5);
lean_inc(x_48);
x_49 = l_Lean_Name_mkStr4(x_45, x_46, x_47, x_48);
lean_inc(x_44);
lean_ctor_set_tag(x_37, 2);
lean_ctor_set(x_37, 1, x_48);
lean_ctor_set(x_37, 0, x_44);
x_50 = lean_mk_string_unchecked("null", 4, 4);
x_51 = l_Lean_Name_mkStr1(x_50);
x_52 = lean_mk_string_unchecked("only", 4, 4);
lean_inc(x_44);
lean_ctor_set_tag(x_16, 2);
lean_ctor_set(x_16, 1, x_52);
lean_ctor_set(x_16, 0, x_44);
lean_inc(x_51);
lean_inc(x_44);
x_53 = l_Lean_Syntax_node1(x_44, x_51, x_16);
x_54 = l_Array_mkArray0(lean_box(0));
lean_inc(x_44);
x_55 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_55, 0, x_44);
lean_ctor_set(x_55, 1, x_51);
lean_ctor_set(x_55, 2, x_54);
lean_inc(x_55);
x_56 = l_Lean_Syntax_node5(x_44, x_49, x_37, x_1, x_53, x_55, x_55);
x_32 = x_56;
x_33 = x_39;
goto block_36;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_57 = lean_ctor_get(x_37, 1);
lean_inc(x_57);
lean_dec(x_37);
x_58 = lean_ctor_get(x_6, 5);
lean_inc(x_58);
lean_dec(x_6);
x_59 = lean_box(0);
x_60 = lean_unbox(x_59);
x_61 = l_Lean_SourceInfo_fromRef(x_58, x_60);
lean_dec(x_58);
x_62 = lean_mk_string_unchecked("Lean", 4, 4);
x_63 = lean_mk_string_unchecked("Parser", 6, 6);
x_64 = lean_mk_string_unchecked("Tactic", 6, 6);
x_65 = lean_mk_string_unchecked("grind", 5, 5);
lean_inc(x_65);
x_66 = l_Lean_Name_mkStr4(x_62, x_63, x_64, x_65);
lean_inc(x_61);
x_67 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_67, 0, x_61);
lean_ctor_set(x_67, 1, x_65);
x_68 = lean_mk_string_unchecked("null", 4, 4);
x_69 = l_Lean_Name_mkStr1(x_68);
x_70 = lean_mk_string_unchecked("only", 4, 4);
lean_inc(x_61);
lean_ctor_set_tag(x_16, 2);
lean_ctor_set(x_16, 1, x_70);
lean_ctor_set(x_16, 0, x_61);
lean_inc(x_69);
lean_inc(x_61);
x_71 = l_Lean_Syntax_node1(x_61, x_69, x_16);
x_72 = l_Array_mkArray0(lean_box(0));
lean_inc(x_61);
x_73 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_73, 0, x_61);
lean_ctor_set(x_73, 1, x_69);
lean_ctor_set(x_73, 2, x_72);
lean_inc(x_73);
x_74 = l_Lean_Syntax_node5(x_61, x_66, x_67, x_1, x_71, x_73, x_73);
x_32 = x_74;
x_33 = x_57;
goto block_36;
}
}
else
{
lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_75 = lean_ctor_get(x_2, 0);
lean_inc(x_75);
lean_dec(x_2);
x_76 = lean_st_ref_get(x_7, x_30);
lean_dec(x_7);
x_77 = !lean_is_exclusive(x_76);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_78 = lean_ctor_get(x_76, 1);
x_79 = lean_ctor_get(x_76, 0);
lean_dec(x_79);
x_80 = lean_ctor_get(x_6, 5);
lean_inc(x_80);
lean_dec(x_6);
x_81 = lean_box(0);
x_82 = lean_unbox(x_81);
x_83 = l_Lean_SourceInfo_fromRef(x_80, x_82);
lean_dec(x_80);
x_84 = lean_mk_string_unchecked("Lean", 4, 4);
x_85 = lean_mk_string_unchecked("Parser", 6, 6);
x_86 = lean_mk_string_unchecked("Tactic", 6, 6);
x_87 = lean_mk_string_unchecked("grind", 5, 5);
lean_inc(x_87);
x_88 = l_Lean_Name_mkStr4(x_84, x_85, x_86, x_87);
lean_inc(x_83);
lean_ctor_set_tag(x_76, 2);
lean_ctor_set(x_76, 1, x_87);
lean_ctor_set(x_76, 0, x_83);
x_89 = lean_mk_string_unchecked("null", 4, 4);
x_90 = l_Lean_Name_mkStr1(x_89);
x_91 = lean_mk_string_unchecked("only", 4, 4);
lean_inc(x_83);
lean_ctor_set_tag(x_16, 2);
lean_ctor_set(x_16, 1, x_91);
lean_ctor_set(x_16, 0, x_83);
lean_inc(x_90);
lean_inc(x_83);
x_92 = l_Lean_Syntax_node1(x_83, x_90, x_16);
x_93 = l_Array_mkArray0(lean_box(0));
lean_inc(x_90);
lean_inc(x_83);
x_94 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_94, 0, x_83);
lean_ctor_set(x_94, 1, x_90);
lean_ctor_set(x_94, 2, x_93);
x_95 = lean_mk_string_unchecked("on_failure", 10, 10);
lean_inc(x_83);
x_96 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_96, 0, x_83);
lean_ctor_set(x_96, 1, x_95);
lean_inc(x_83);
x_97 = l_Lean_Syntax_node2(x_83, x_90, x_96, x_75);
x_98 = l_Lean_Syntax_node5(x_83, x_88, x_76, x_1, x_92, x_94, x_97);
x_32 = x_98;
x_33 = x_78;
goto block_36;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_99 = lean_ctor_get(x_76, 1);
lean_inc(x_99);
lean_dec(x_76);
x_100 = lean_ctor_get(x_6, 5);
lean_inc(x_100);
lean_dec(x_6);
x_101 = lean_box(0);
x_102 = lean_unbox(x_101);
x_103 = l_Lean_SourceInfo_fromRef(x_100, x_102);
lean_dec(x_100);
x_104 = lean_mk_string_unchecked("Lean", 4, 4);
x_105 = lean_mk_string_unchecked("Parser", 6, 6);
x_106 = lean_mk_string_unchecked("Tactic", 6, 6);
x_107 = lean_mk_string_unchecked("grind", 5, 5);
lean_inc(x_107);
x_108 = l_Lean_Name_mkStr4(x_104, x_105, x_106, x_107);
lean_inc(x_103);
x_109 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_109, 0, x_103);
lean_ctor_set(x_109, 1, x_107);
x_110 = lean_mk_string_unchecked("null", 4, 4);
x_111 = l_Lean_Name_mkStr1(x_110);
x_112 = lean_mk_string_unchecked("only", 4, 4);
lean_inc(x_103);
lean_ctor_set_tag(x_16, 2);
lean_ctor_set(x_16, 1, x_112);
lean_ctor_set(x_16, 0, x_103);
lean_inc(x_111);
lean_inc(x_103);
x_113 = l_Lean_Syntax_node1(x_103, x_111, x_16);
x_114 = l_Array_mkArray0(lean_box(0));
lean_inc(x_111);
lean_inc(x_103);
x_115 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_115, 0, x_103);
lean_ctor_set(x_115, 1, x_111);
lean_ctor_set(x_115, 2, x_114);
x_116 = lean_mk_string_unchecked("on_failure", 10, 10);
lean_inc(x_103);
x_117 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_117, 0, x_103);
lean_ctor_set(x_117, 1, x_116);
lean_inc(x_103);
x_118 = l_Lean_Syntax_node2(x_103, x_111, x_117, x_75);
x_119 = l_Lean_Syntax_node5(x_103, x_108, x_109, x_1, x_113, x_115, x_118);
x_32 = x_119;
x_33 = x_99;
goto block_36;
}
}
block_36:
{
lean_object* x_34; lean_object* x_35; 
x_34 = l_Lean_Elab_Tactic_setGrindParams(x_32, x_29);
lean_dec(x_29);
if (lean_is_scalar(x_31)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_31;
}
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
else
{
uint8_t x_120; 
lean_free_object(x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_120 = !lean_is_exclusive(x_28);
if (x_120 == 0)
{
return x_28;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_28, 0);
x_122 = lean_ctor_get(x_28, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_28);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
return x_123;
}
}
}
else
{
uint8_t x_124; 
lean_free_object(x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_124 = !lean_is_exclusive(x_23);
if (x_124 == 0)
{
return x_23;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_23, 0);
x_126 = lean_ctor_get(x_23, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_23);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
return x_127;
}
}
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_128 = lean_ctor_get(x_16, 1);
lean_inc(x_128);
lean_dec(x_16);
x_129 = lean_ctor_get(x_3, 1);
lean_inc(x_129);
x_130 = l_Lean_PersistentHashSet_toList___at___Lean_Elab_Tactic_mkGrindOnly_spec__5(x_129);
lean_dec(x_129);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_130);
x_131 = l_List_forIn_x27_loop___at___Lean_Elab_Tactic_mkGrindOnly_spec__7___redArg(x_130, x_130, x_128, x_4, x_5, x_6, x_7, x_17);
lean_dec(x_130);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
lean_dec(x_131);
x_134 = lean_ctor_get(x_3, 2);
lean_inc(x_134);
x_135 = l_Lean_PersistentHashSet_toList___at___Lean_Elab_Tactic_mkGrindOnly_spec__5(x_134);
lean_dec(x_134);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_135);
x_136 = l_List_forIn_x27_loop___at___Lean_Elab_Tactic_mkGrindOnly_spec__9___redArg(x_3, x_135, x_135, x_132, x_4, x_5, x_6, x_7, x_133);
lean_dec(x_135);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_136, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_139 = x_136;
} else {
 lean_dec_ref(x_136);
 x_139 = lean_box(0);
}
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_145 = lean_st_ref_get(x_7, x_138);
lean_dec(x_7);
x_146 = lean_ctor_get(x_145, 1);
lean_inc(x_146);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 x_147 = x_145;
} else {
 lean_dec_ref(x_145);
 x_147 = lean_box(0);
}
x_148 = lean_ctor_get(x_6, 5);
lean_inc(x_148);
lean_dec(x_6);
x_149 = lean_box(0);
x_150 = lean_unbox(x_149);
x_151 = l_Lean_SourceInfo_fromRef(x_148, x_150);
lean_dec(x_148);
x_152 = lean_mk_string_unchecked("Lean", 4, 4);
x_153 = lean_mk_string_unchecked("Parser", 6, 6);
x_154 = lean_mk_string_unchecked("Tactic", 6, 6);
x_155 = lean_mk_string_unchecked("grind", 5, 5);
lean_inc(x_155);
x_156 = l_Lean_Name_mkStr4(x_152, x_153, x_154, x_155);
lean_inc(x_151);
if (lean_is_scalar(x_147)) {
 x_157 = lean_alloc_ctor(2, 2, 0);
} else {
 x_157 = x_147;
 lean_ctor_set_tag(x_157, 2);
}
lean_ctor_set(x_157, 0, x_151);
lean_ctor_set(x_157, 1, x_155);
x_158 = lean_mk_string_unchecked("null", 4, 4);
x_159 = l_Lean_Name_mkStr1(x_158);
x_160 = lean_mk_string_unchecked("only", 4, 4);
lean_inc(x_151);
x_161 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_161, 0, x_151);
lean_ctor_set(x_161, 1, x_160);
lean_inc(x_159);
lean_inc(x_151);
x_162 = l_Lean_Syntax_node1(x_151, x_159, x_161);
x_163 = l_Array_mkArray0(lean_box(0));
lean_inc(x_151);
x_164 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_164, 0, x_151);
lean_ctor_set(x_164, 1, x_159);
lean_ctor_set(x_164, 2, x_163);
lean_inc(x_164);
x_165 = l_Lean_Syntax_node5(x_151, x_156, x_157, x_1, x_162, x_164, x_164);
x_140 = x_165;
x_141 = x_146;
goto block_144;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; uint8_t x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_166 = lean_ctor_get(x_2, 0);
lean_inc(x_166);
lean_dec(x_2);
x_167 = lean_st_ref_get(x_7, x_138);
lean_dec(x_7);
x_168 = lean_ctor_get(x_167, 1);
lean_inc(x_168);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 lean_ctor_release(x_167, 1);
 x_169 = x_167;
} else {
 lean_dec_ref(x_167);
 x_169 = lean_box(0);
}
x_170 = lean_ctor_get(x_6, 5);
lean_inc(x_170);
lean_dec(x_6);
x_171 = lean_box(0);
x_172 = lean_unbox(x_171);
x_173 = l_Lean_SourceInfo_fromRef(x_170, x_172);
lean_dec(x_170);
x_174 = lean_mk_string_unchecked("Lean", 4, 4);
x_175 = lean_mk_string_unchecked("Parser", 6, 6);
x_176 = lean_mk_string_unchecked("Tactic", 6, 6);
x_177 = lean_mk_string_unchecked("grind", 5, 5);
lean_inc(x_177);
x_178 = l_Lean_Name_mkStr4(x_174, x_175, x_176, x_177);
lean_inc(x_173);
if (lean_is_scalar(x_169)) {
 x_179 = lean_alloc_ctor(2, 2, 0);
} else {
 x_179 = x_169;
 lean_ctor_set_tag(x_179, 2);
}
lean_ctor_set(x_179, 0, x_173);
lean_ctor_set(x_179, 1, x_177);
x_180 = lean_mk_string_unchecked("null", 4, 4);
x_181 = l_Lean_Name_mkStr1(x_180);
x_182 = lean_mk_string_unchecked("only", 4, 4);
lean_inc(x_173);
x_183 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_183, 0, x_173);
lean_ctor_set(x_183, 1, x_182);
lean_inc(x_181);
lean_inc(x_173);
x_184 = l_Lean_Syntax_node1(x_173, x_181, x_183);
x_185 = l_Array_mkArray0(lean_box(0));
lean_inc(x_181);
lean_inc(x_173);
x_186 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_186, 0, x_173);
lean_ctor_set(x_186, 1, x_181);
lean_ctor_set(x_186, 2, x_185);
x_187 = lean_mk_string_unchecked("on_failure", 10, 10);
lean_inc(x_173);
x_188 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_188, 0, x_173);
lean_ctor_set(x_188, 1, x_187);
lean_inc(x_173);
x_189 = l_Lean_Syntax_node2(x_173, x_181, x_188, x_166);
x_190 = l_Lean_Syntax_node5(x_173, x_178, x_179, x_1, x_184, x_186, x_189);
x_140 = x_190;
x_141 = x_168;
goto block_144;
}
block_144:
{
lean_object* x_142; lean_object* x_143; 
x_142 = l_Lean_Elab_Tactic_setGrindParams(x_140, x_137);
lean_dec(x_137);
if (lean_is_scalar(x_139)) {
 x_143 = lean_alloc_ctor(0, 2, 0);
} else {
 x_143 = x_139;
}
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_141);
return x_143;
}
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_191 = lean_ctor_get(x_136, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_136, 1);
lean_inc(x_192);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_193 = x_136;
} else {
 lean_dec_ref(x_136);
 x_193 = lean_box(0);
}
if (lean_is_scalar(x_193)) {
 x_194 = lean_alloc_ctor(1, 2, 0);
} else {
 x_194 = x_193;
}
lean_ctor_set(x_194, 0, x_191);
lean_ctor_set(x_194, 1, x_192);
return x_194;
}
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_195 = lean_ctor_get(x_131, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_131, 1);
lean_inc(x_196);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_197 = x_131;
} else {
 lean_dec_ref(x_131);
 x_197 = lean_box(0);
}
if (lean_is_scalar(x_197)) {
 x_198 = lean_alloc_ctor(1, 2, 0);
} else {
 x_198 = x_197;
}
lean_ctor_set(x_198, 0, x_195);
lean_ctor_set(x_198, 1, x_196);
return x_198;
}
}
}
else
{
uint8_t x_199; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_199 = !lean_is_exclusive(x_15);
if (x_199 == 0)
{
return x_15;
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_200 = lean_ctor_get(x_15, 0);
x_201 = lean_ctor_get(x_15, 1);
lean_inc(x_201);
lean_inc(x_200);
lean_dec(x_15);
x_202 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_202, 0, x_200);
lean_ctor_set(x_202, 1, x_201);
return x_202;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___Lean_PersistentHashSet_toList___at___Lean_Elab_Tactic_mkGrindOnly_spec__0_spec__0___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PersistentHashMap_toList___at___Lean_PersistentHashSet_toList___at___Lean_Elab_Tactic_mkGrindOnly_spec__0_spec__0___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___Lean_PersistentHashSet_toList___at___Lean_Elab_Tactic_mkGrindOnly_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PersistentHashMap_toList___at___Lean_PersistentHashSet_toList___at___Lean_Elab_Tactic_mkGrindOnly_spec__0_spec__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_toList___at___Lean_Elab_Tactic_mkGrindOnly_spec__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PersistentHashSet_toList___at___Lean_Elab_Tactic_mkGrindOnly_spec__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Tactic_mkGrindOnly_spec__3_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Tactic_mkGrindOnly_spec__3_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Elab_Tactic_mkGrindOnly_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_forIn_x27_loop___at___Lean_Elab_Tactic_mkGrindOnly_spec__3___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Elab_Tactic_mkGrindOnly_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_List_forIn_x27_loop___at___Lean_Elab_Tactic_mkGrindOnly_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_toList___at___Lean_Elab_Tactic_mkGrindOnly_spec__5___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PersistentHashSet_toList___at___Lean_Elab_Tactic_mkGrindOnly_spec__5(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Tactic_mkGrindOnly_spec__7_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Tactic_mkGrindOnly_spec__7_spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Elab_Tactic_mkGrindOnly_spec__7___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_forIn_x27_loop___at___Lean_Elab_Tactic_mkGrindOnly_spec__7___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Elab_Tactic_mkGrindOnly_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_List_forIn_x27_loop___at___Lean_Elab_Tactic_mkGrindOnly_spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Tactic_mkGrindOnly_spec__9_spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Tactic_mkGrindOnly_spec__9_spec__9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Elab_Tactic_mkGrindOnly_spec__9___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_List_forIn_x27_loop___at___Lean_Elab_Tactic_mkGrindOnly_spec__9___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Elab_Tactic_mkGrindOnly_spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_List_forIn_x27_loop___at___Lean_Elab_Tactic_mkGrindOnly_spec__9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGrind(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_mk_string_unchecked("Lean", 4, 4);
x_12 = lean_mk_string_unchecked("Parser", 6, 6);
x_13 = lean_mk_string_unchecked("Tactic", 6, 6);
x_14 = lean_mk_string_unchecked("grind", 5, 5);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_15 = l_Lean_Name_mkStr4(x_11, x_12, x_13, x_14);
lean_inc(x_1);
x_16 = l_Lean_Syntax_isOfKind(x_1, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
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
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_18 = lean_unsigned_to_nat(1u);
x_19 = l_Lean_Syntax_getArg(x_1, x_18);
x_51 = lean_mk_string_unchecked("optConfig", 9, 9);
x_52 = l_Lean_Name_mkStr4(x_11, x_12, x_13, x_51);
lean_inc(x_19);
x_53 = l_Lean_Syntax_isOfKind(x_19, x_52);
lean_dec(x_52);
if (x_53 == 0)
{
lean_object* x_54; 
lean_dec(x_19);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_54 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_10);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_96; uint8_t x_97; 
x_55 = lean_unsigned_to_nat(2u);
x_96 = l_Lean_Syntax_getArg(x_1, x_55);
x_97 = l_Lean_Syntax_isNone(x_96);
if (x_97 == 0)
{
uint8_t x_98; 
lean_inc(x_96);
x_98 = l_Lean_Syntax_matchesNull(x_96, x_18);
if (x_98 == 0)
{
lean_object* x_99; 
lean_dec(x_96);
lean_dec(x_19);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_99 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_10);
return x_99;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_unsigned_to_nat(0u);
x_101 = l_Lean_Syntax_getArg(x_96, x_100);
lean_dec(x_96);
x_102 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_102, 0, x_101);
x_76 = x_102;
x_77 = x_2;
x_78 = x_3;
x_79 = x_4;
x_80 = x_5;
x_81 = x_6;
x_82 = x_7;
x_83 = x_8;
x_84 = x_9;
x_85 = x_10;
goto block_95;
}
}
else
{
lean_object* x_103; 
lean_dec(x_96);
x_103 = lean_box(0);
x_76 = x_103;
x_77 = x_2;
x_78 = x_3;
x_79 = x_4;
x_80 = x_5;
x_81 = x_6;
x_82 = x_7;
x_83 = x_8;
x_84 = x_9;
x_85 = x_10;
goto block_95;
}
block_75:
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_67 = lean_unsigned_to_nat(4u);
x_68 = l_Lean_Syntax_getArg(x_1, x_67);
x_69 = l_Lean_Syntax_isNone(x_68);
if (x_69 == 0)
{
uint8_t x_70; 
lean_inc(x_68);
x_70 = l_Lean_Syntax_matchesNull(x_68, x_55);
if (x_70 == 0)
{
lean_object* x_71; 
lean_dec(x_68);
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_19);
lean_dec(x_1);
x_71 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_66);
return x_71;
}
else
{
lean_object* x_72; lean_object* x_73; 
x_72 = l_Lean_Syntax_getArg(x_68, x_18);
lean_dec(x_68);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_72);
x_20 = x_56;
x_21 = x_57;
x_22 = x_73;
x_23 = x_58;
x_24 = x_59;
x_25 = x_60;
x_26 = x_61;
x_27 = x_62;
x_28 = x_63;
x_29 = x_64;
x_30 = x_65;
x_31 = x_66;
goto block_50;
}
}
else
{
lean_object* x_74; 
lean_dec(x_68);
x_74 = lean_box(0);
x_20 = x_56;
x_21 = x_57;
x_22 = x_74;
x_23 = x_58;
x_24 = x_59;
x_25 = x_60;
x_26 = x_61;
x_27 = x_62;
x_28 = x_63;
x_29 = x_64;
x_30 = x_65;
x_31 = x_66;
goto block_50;
}
}
block_95:
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_86 = lean_unsigned_to_nat(3u);
x_87 = l_Lean_Syntax_getArg(x_1, x_86);
x_88 = l_Lean_Syntax_isNone(x_87);
if (x_88 == 0)
{
uint8_t x_89; 
lean_inc(x_87);
x_89 = l_Lean_Syntax_matchesNull(x_87, x_86);
if (x_89 == 0)
{
lean_object* x_90; 
lean_dec(x_87);
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_19);
lean_dec(x_1);
x_90 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_85);
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = l_Lean_Syntax_getArg(x_87, x_18);
lean_dec(x_87);
x_92 = l_Lean_Syntax_getArgs(x_91);
lean_dec(x_91);
x_93 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_93, 0, x_92);
x_56 = x_76;
x_57 = x_93;
x_58 = x_77;
x_59 = x_78;
x_60 = x_79;
x_61 = x_80;
x_62 = x_81;
x_63 = x_82;
x_64 = x_83;
x_65 = x_84;
x_66 = x_85;
goto block_75;
}
}
else
{
lean_object* x_94; 
lean_dec(x_87);
x_94 = lean_box(0);
x_56 = x_76;
x_57 = x_94;
x_58 = x_77;
x_59 = x_78;
x_60 = x_79;
x_61 = x_80;
x_62 = x_81;
x_63 = x_82;
x_64 = x_83;
x_65 = x_84;
x_66 = x_85;
goto block_75;
}
}
}
block_50:
{
lean_object* x_32; 
lean_inc(x_30);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
x_32 = l_Lean_Elab_Tactic_elabGrindConfig___redArg(x_19, x_23, x_25, x_26, x_27, x_28, x_29, x_30, x_31);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = l_Lean_Elab_Tactic_evalGrindCore(x_1, x_33, x_20, x_21, x_22, x_23, x_24, x_25, x_26, x_27, x_28, x_29, x_30, x_34);
lean_dec(x_27);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_1);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_35, 0);
lean_dec(x_37);
x_38 = lean_box(0);
lean_ctor_set(x_35, 0, x_38);
return x_35;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_35, 1);
lean_inc(x_39);
lean_dec(x_35);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_35);
if (x_42 == 0)
{
return x_35;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_35, 0);
x_44 = lean_ctor_get(x_35, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_35);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_32);
if (x_46 == 0)
{
return x_32;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_32, 0);
x_48 = lean_ctor_get(x_32, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_32);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalGrind__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Tactic", 6, 6);
x_6 = lean_mk_string_unchecked("grind", 5, 5);
lean_inc(x_5);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("Elab", 4, 4);
x_9 = lean_mk_string_unchecked("evalGrind", 9, 9);
x_10 = l_Lean_Name_mkStr4(x_3, x_8, x_5, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalGrind), 10, 0);
x_12 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_10, x_11, x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGrindTrace(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_mk_string_unchecked("Lean", 4, 4);
x_12 = lean_mk_string_unchecked("Parser", 6, 6);
x_13 = lean_mk_string_unchecked("Tactic", 6, 6);
x_14 = lean_mk_string_unchecked("grindTrace", 10, 10);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_15 = l_Lean_Name_mkStr4(x_11, x_12, x_13, x_14);
lean_inc(x_1);
x_16 = l_Lean_Syntax_isOfKind(x_1, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
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
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_unsigned_to_nat(1u);
x_19 = l_Lean_Syntax_getArg(x_1, x_18);
x_20 = lean_mk_string_unchecked("optConfig", 9, 9);
x_21 = l_Lean_Name_mkStr4(x_11, x_12, x_13, x_20);
lean_inc(x_19);
x_22 = l_Lean_Syntax_isOfKind(x_19, x_21);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_19);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_23 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_10);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_138; uint8_t x_139; 
x_24 = lean_unsigned_to_nat(0u);
x_97 = lean_unsigned_to_nat(2u);
x_138 = l_Lean_Syntax_getArg(x_1, x_97);
x_139 = l_Lean_Syntax_isNone(x_138);
if (x_139 == 0)
{
uint8_t x_140; 
lean_inc(x_138);
x_140 = l_Lean_Syntax_matchesNull(x_138, x_18);
if (x_140 == 0)
{
lean_object* x_141; 
lean_dec(x_138);
lean_dec(x_19);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_141 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_10);
return x_141;
}
else
{
lean_object* x_142; lean_object* x_143; 
x_142 = l_Lean_Syntax_getArg(x_138, x_24);
lean_dec(x_138);
x_143 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_143, 0, x_142);
x_118 = x_143;
x_119 = x_2;
x_120 = x_3;
x_121 = x_4;
x_122 = x_5;
x_123 = x_6;
x_124 = x_7;
x_125 = x_8;
x_126 = x_9;
x_127 = x_10;
goto block_137;
}
}
else
{
lean_object* x_144; 
lean_dec(x_138);
x_144 = lean_box(0);
x_118 = x_144;
x_119 = x_2;
x_120 = x_3;
x_121 = x_4;
x_122 = x_5;
x_123 = x_6;
x_124 = x_7;
x_125 = x_8;
x_126 = x_9;
x_127 = x_10;
goto block_137;
}
block_96:
{
lean_object* x_37; 
lean_inc(x_35);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_19);
x_37 = l_Lean_Elab_Tactic_elabGrindConfig___redArg(x_19, x_28, x_30, x_31, x_32, x_33, x_34, x_35, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; uint8_t x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
x_42 = lean_ctor_get(x_38, 2);
lean_inc(x_42);
x_43 = lean_ctor_get(x_38, 3);
lean_inc(x_43);
x_44 = lean_ctor_get_uint8(x_38, sizeof(void*)*7 + 1);
x_45 = lean_ctor_get_uint8(x_38, sizeof(void*)*7 + 2);
x_46 = lean_ctor_get_uint8(x_38, sizeof(void*)*7 + 3);
x_47 = lean_ctor_get_uint8(x_38, sizeof(void*)*7 + 4);
x_48 = lean_ctor_get_uint8(x_38, sizeof(void*)*7 + 5);
x_49 = lean_ctor_get(x_38, 4);
lean_inc(x_49);
x_50 = lean_ctor_get(x_38, 5);
lean_inc(x_50);
x_51 = lean_ctor_get_uint8(x_38, sizeof(void*)*7 + 6);
x_52 = lean_ctor_get_uint8(x_38, sizeof(void*)*7 + 7);
x_53 = lean_ctor_get_uint8(x_38, sizeof(void*)*7 + 8);
x_54 = lean_ctor_get_uint8(x_38, sizeof(void*)*7 + 9);
x_55 = lean_ctor_get_uint8(x_38, sizeof(void*)*7 + 10);
x_56 = lean_ctor_get_uint8(x_38, sizeof(void*)*7 + 11);
x_57 = lean_ctor_get_uint8(x_38, sizeof(void*)*7 + 12);
x_58 = lean_ctor_get_uint8(x_38, sizeof(void*)*7 + 13);
x_59 = lean_ctor_get_uint8(x_38, sizeof(void*)*7 + 14);
x_60 = lean_ctor_get_uint8(x_38, sizeof(void*)*7 + 15);
x_61 = lean_ctor_get_uint8(x_38, sizeof(void*)*7 + 16);
x_62 = lean_ctor_get(x_38, 6);
lean_inc(x_62);
x_63 = lean_ctor_get_uint8(x_38, sizeof(void*)*7 + 17);
lean_dec(x_38);
x_64 = lean_alloc_ctor(0, 7, 18);
lean_ctor_set(x_64, 0, x_40);
lean_ctor_set(x_64, 1, x_41);
lean_ctor_set(x_64, 2, x_42);
lean_ctor_set(x_64, 3, x_43);
lean_ctor_set(x_64, 4, x_49);
lean_ctor_set(x_64, 5, x_50);
lean_ctor_set(x_64, 6, x_62);
lean_ctor_set_uint8(x_64, sizeof(void*)*7, x_22);
lean_ctor_set_uint8(x_64, sizeof(void*)*7 + 1, x_44);
lean_ctor_set_uint8(x_64, sizeof(void*)*7 + 2, x_45);
lean_ctor_set_uint8(x_64, sizeof(void*)*7 + 3, x_46);
lean_ctor_set_uint8(x_64, sizeof(void*)*7 + 4, x_47);
lean_ctor_set_uint8(x_64, sizeof(void*)*7 + 5, x_48);
lean_ctor_set_uint8(x_64, sizeof(void*)*7 + 6, x_51);
lean_ctor_set_uint8(x_64, sizeof(void*)*7 + 7, x_52);
lean_ctor_set_uint8(x_64, sizeof(void*)*7 + 8, x_53);
lean_ctor_set_uint8(x_64, sizeof(void*)*7 + 9, x_54);
lean_ctor_set_uint8(x_64, sizeof(void*)*7 + 10, x_55);
lean_ctor_set_uint8(x_64, sizeof(void*)*7 + 11, x_56);
lean_ctor_set_uint8(x_64, sizeof(void*)*7 + 12, x_57);
lean_ctor_set_uint8(x_64, sizeof(void*)*7 + 13, x_58);
lean_ctor_set_uint8(x_64, sizeof(void*)*7 + 14, x_59);
lean_ctor_set_uint8(x_64, sizeof(void*)*7 + 15, x_60);
lean_ctor_set_uint8(x_64, sizeof(void*)*7 + 16, x_61);
lean_ctor_set_uint8(x_64, sizeof(void*)*7 + 17, x_63);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_27);
x_65 = l_Lean_Elab_Tactic_evalGrindCore(x_1, x_64, x_26, x_25, x_27, x_28, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_39);
lean_dec(x_25);
lean_dec(x_26);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
x_68 = l_Lean_Elab_Tactic_mkGrindOnly(x_19, x_27, x_66, x_32, x_33, x_34, x_35, x_67);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = l_Lean_Syntax_getArg(x_1, x_24);
lean_dec(x_1);
x_72 = lean_ctor_get(x_34, 5);
lean_inc(x_72);
x_73 = lean_mk_string_unchecked("tactic", 6, 6);
x_74 = l_Lean_Name_mkStr1(x_73);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_69);
x_76 = lean_box(0);
x_77 = lean_box(0);
x_78 = lean_box(0);
x_79 = lean_box(0);
x_80 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_80, 0, x_75);
lean_ctor_set(x_80, 1, x_76);
lean_ctor_set(x_80, 2, x_76);
lean_ctor_set(x_80, 3, x_77);
lean_ctor_set(x_80, 4, x_78);
lean_ctor_set(x_80, 5, x_79);
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_72);
x_82 = lean_mk_string_unchecked("Try this: ", 10, 10);
x_83 = l_Lean_Meta_Tactic_TryThis_addSuggestion(x_71, x_80, x_81, x_82, x_76, x_32, x_33, x_34, x_35, x_70);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_81);
lean_dec(x_71);
return x_83;
}
else
{
uint8_t x_84; 
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_1);
x_84 = !lean_is_exclusive(x_68);
if (x_84 == 0)
{
return x_68;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_68, 0);
x_86 = lean_ctor_get(x_68, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_68);
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
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_27);
lean_dec(x_19);
lean_dec(x_1);
x_88 = !lean_is_exclusive(x_65);
if (x_88 == 0)
{
return x_65;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_65, 0);
x_90 = lean_ctor_get(x_65, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_65);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
else
{
uint8_t x_92; 
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_19);
lean_dec(x_1);
x_92 = !lean_is_exclusive(x_37);
if (x_92 == 0)
{
return x_37;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_37, 0);
x_94 = lean_ctor_get(x_37, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_37);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
block_117:
{
lean_object* x_109; lean_object* x_110; uint8_t x_111; 
x_109 = lean_unsigned_to_nat(4u);
x_110 = l_Lean_Syntax_getArg(x_1, x_109);
x_111 = l_Lean_Syntax_isNone(x_110);
if (x_111 == 0)
{
uint8_t x_112; 
lean_inc(x_110);
x_112 = l_Lean_Syntax_matchesNull(x_110, x_97);
if (x_112 == 0)
{
lean_object* x_113; 
lean_dec(x_110);
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_105);
lean_dec(x_104);
lean_dec(x_103);
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_19);
lean_dec(x_1);
x_113 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_108);
return x_113;
}
else
{
lean_object* x_114; lean_object* x_115; 
x_114 = l_Lean_Syntax_getArg(x_110, x_18);
lean_dec(x_110);
x_115 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_115, 0, x_114);
x_25 = x_99;
x_26 = x_98;
x_27 = x_115;
x_28 = x_100;
x_29 = x_101;
x_30 = x_102;
x_31 = x_103;
x_32 = x_104;
x_33 = x_105;
x_34 = x_106;
x_35 = x_107;
x_36 = x_108;
goto block_96;
}
}
else
{
lean_object* x_116; 
lean_dec(x_110);
x_116 = lean_box(0);
x_25 = x_99;
x_26 = x_98;
x_27 = x_116;
x_28 = x_100;
x_29 = x_101;
x_30 = x_102;
x_31 = x_103;
x_32 = x_104;
x_33 = x_105;
x_34 = x_106;
x_35 = x_107;
x_36 = x_108;
goto block_96;
}
}
block_137:
{
lean_object* x_128; lean_object* x_129; uint8_t x_130; 
x_128 = lean_unsigned_to_nat(3u);
x_129 = l_Lean_Syntax_getArg(x_1, x_128);
x_130 = l_Lean_Syntax_isNone(x_129);
if (x_130 == 0)
{
uint8_t x_131; 
lean_inc(x_129);
x_131 = l_Lean_Syntax_matchesNull(x_129, x_128);
if (x_131 == 0)
{
lean_object* x_132; 
lean_dec(x_129);
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_124);
lean_dec(x_123);
lean_dec(x_122);
lean_dec(x_121);
lean_dec(x_120);
lean_dec(x_119);
lean_dec(x_118);
lean_dec(x_19);
lean_dec(x_1);
x_132 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_127);
return x_132;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = l_Lean_Syntax_getArg(x_129, x_18);
lean_dec(x_129);
x_134 = l_Lean_Syntax_getArgs(x_133);
lean_dec(x_133);
x_135 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_135, 0, x_134);
x_98 = x_118;
x_99 = x_135;
x_100 = x_119;
x_101 = x_120;
x_102 = x_121;
x_103 = x_122;
x_104 = x_123;
x_105 = x_124;
x_106 = x_125;
x_107 = x_126;
x_108 = x_127;
goto block_117;
}
}
else
{
lean_object* x_136; 
lean_dec(x_129);
x_136 = lean_box(0);
x_98 = x_118;
x_99 = x_136;
x_100 = x_119;
x_101 = x_120;
x_102 = x_121;
x_103 = x_122;
x_104 = x_123;
x_105 = x_124;
x_106 = x_125;
x_107 = x_126;
x_108 = x_127;
goto block_117;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalGrindTrace__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Tactic", 6, 6);
x_6 = lean_mk_string_unchecked("grindTrace", 10, 10);
lean_inc(x_5);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("Elab", 4, 4);
x_9 = lean_mk_string_unchecked("evalGrindTrace", 14, 14);
x_10 = l_Lean_Name_mkStr4(x_3, x_8, x_5, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalGrindTrace), 10, 0);
x_12 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_10, x_11, x_1);
return x_12;
}
}
lean_object* initialize_Init_Grind_Tactics(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_TryThis(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Command(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_MutualDef(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Config(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Grind(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_Tactics(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_TryThis(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Command(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_MutualDef(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Config(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_elabGrindPattern__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_elabResetGrindAttrs__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_elabInitGrindNorm__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Tactic_grindParamsPos = _init_l_Lean_Elab_Tactic_grindParamsPos();
lean_mark_persistent(l_Lean_Elab_Tactic_grindParamsPos);
l_Lean_Elab_Tactic_grindOnlyPos = _init_l_Lean_Elab_Tactic_grindOnlyPos();
lean_mark_persistent(l_Lean_Elab_Tactic_grindOnlyPos);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_evalGrind__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_evalGrindTrace__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
