// Lean compiler output
// Module: Lean.PrettyPrinter.Delaborator.TopDownAnalyze
// Imports: Lean.Data.RBMap Lean.Meta.SynthInstance Lean.Meta.CtorRecognizer Lean.Util.FindMVar Lean.Util.FindLevelMVar Lean.Util.CollectLevelParams Lean.Util.ReplaceLevel Lean.PrettyPrinter.Delaborator.FieldNotation Lean.PrettyPrinter.Delaborator.Options Lean.PrettyPrinter.Delaborator.SubExpr Lean.Elab.Config
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
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit_spec__0(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_topDownAnalyze___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLam_spec__1_spec__1_spec__1___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_topDownAnalyze___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_hBinOpHeuristic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_withKnowing___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryFn___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeFn_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_pp_analyze_knowsType;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_367_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_pp_analyze_trustSubst;
lean_object* l_Lean_MetavarContext_findDecl_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLam_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core_spec__2_spec__2_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_pp_analyze_omitMax;
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextFull___at___Lean_Meta_recordSynthPendingFailure_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_returnsPi___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshLevelMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getPostponed___redArg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_instMonadWithReaderOfSubExprAnalyzeM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBool_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_getPPAnalyzeCheckInstances(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_hasMVarAtCurrDepth___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_getPPAnalyzeTrustId(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_hBinOpHeuristic_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_checkOutParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isDefEqAssigning___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_pp_analyze_explicitHoles;
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLam_spec__1_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_isFOLike___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_0__Lean_PrettyPrinter_Delaborator_TopDownAnalyze_valUnknown___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_instInhabitedContext;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit_spec__2___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Level_hasParam(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_spec__2___boxed(lean_object**);
LEAN_EXPORT uint8_t l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp(lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeAppStaged___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isRawNatLit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_returnsPi(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_lit___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_isSimpleHOFun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_10869_(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectBottomUps_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_0__Lean_PrettyPrinter_Delaborator_TopDownAnalyze_typeUnknown(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Meta_trySynthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isStringLit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_hasLevelMVarAtCurrDepth___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern uint8_t l_instInhabitedBool;
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit_spec__2_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLam_spec__1_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Option_register___at___Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Options___hyg_45__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_inspectOutParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
uint8_t l_Lean_getPPFieldNotation(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectTrivialBottomUps_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_instMonadEIO___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
LEAN_EXPORT uint8_t l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_hasMVarAtCurrDepth___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isTrivialBottomUp___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit_spec__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_pp_analyze_trustSubtypeMk;
LEAN_EXPORT lean_object* l_Lean_getPPAnalyzeTrustSubtypeMk___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectHigherOrders_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectBottomUps_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_hasLevelMVarAtCurrDepth___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_isType2Type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_isNonConstFun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_inspectOutParams_inspectAux___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getPPAnalyzeTypeAscriptions___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectBottomUps_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_instMonadReaderOfSubExprAnalyzeM;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_7_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeProj(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLam_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeMData_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectHigherOrders_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeMData_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getPPAnalysisNeedsType___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectBottomUps_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingDomain___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLam_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_hasLevelMVarAtCurrDepth(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_topDownAnalyze(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_checkOutParams_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_getPPAnalysisNamedArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_containsBadMax___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeAppStaged(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core_spec__2_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectBottomUps_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvar___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_insert___at___Lean_PrettyPrinter_Delaborator_OptionsPerPos_insertAt_spec__0___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedLevel;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetVarType___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_127_(lean_object*);
lean_object* l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_annotateNamedArg___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBool___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeApp___lam__0(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetVarType___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_inspectOutParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_topDownAnalyze___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_0__Lean_PrettyPrinter_Delaborator_TopDownAnalyze_valUnknown(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_hasMVarAtCurrDepth___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectTrivialBottomUps_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_CollectLevelParams_main(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_0__Lean_PrettyPrinter_Delaborator_TopDownAnalyze_valUnknown___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAtomic(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isFunLike___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeApp___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_fieldNotationCandidate_x3f(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core_spec__2_spec__2_spec__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isFunLike(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_nameNotRoundtrippable___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectHigherOrders___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_isNonConstFun___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___Lean_PrettyPrinter_Delaborator_topDownAnalyze_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryFn___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeFn_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst_spec__0___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_checkKnowsType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_inspectOutParams_inspectAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetValue___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit_spec__2_spec__2___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLam_spec__1_spec__1_spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_getPPAnalyzeTypeAscriptions(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_instMonadWithReaderOfSubExprAnalyzeM;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_topDownAnalyze___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectHigherOrders(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_checkOutParams_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_maybeAddBlockImplicit_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_annotateNamedArg___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___Lean_PrettyPrinter_Delaborator_topDownAnalyze_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_nameNotRoundtrippable(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_canBottomUp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isSort(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_mvarName___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_canBottomUp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_hasLevelMVarAtCurrDepth___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_isFOLike___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core_spec__2_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getPPAnalysisLetVarType___boxed(lean_object*);
lean_object* l_Lean_SubExpr_Pos_toString(lean_object*);
LEAN_EXPORT uint8_t l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_nameNotRoundtrippable_containsNum(lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_getPPAnalyzeKnowsType(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeFVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet_spec__0_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeFn_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core_spec__2___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_hBinOpHeuristic_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeProj_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isTrivialBottomUp___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_shrink___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___Lean_PrettyPrinter_Delaborator_topDownAnalyze_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core_spec__2_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerInternalExceptionId(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingDomain___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLam_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectHigherOrders_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
LEAN_EXPORT lean_object* l_Lean_pp_analyze_trustKnownFOType2TypeHOFuns;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectBottomUps___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_canBottomUp_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
uint8_t l_Lean_Expr_isMVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_checkOutParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectBottomUps_spec__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectBottomUps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeArg___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_checkpointDefEq___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_checkpointDefEq_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_207_(lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isDefEqAssigning(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_isNonConstFun___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHigherOrder___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_spec__2_spec__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeAppStaged___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeSort(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___Lean_PrettyPrinter_Delaborator_topDownAnalyze_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extract(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_287_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_inspectOutParams_inspectAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_isStructureInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_47_(lean_object*);
LEAN_EXPORT uint8_t l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isSubstLike(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___Lean_PrettyPrinter_Delaborator_returnsPi_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_getPPAnalyzeOmitMax(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_maybeAddBlockImplicit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeFn_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
uint8_t lean_is_out_param(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FindMVar_main(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLam_spec__1_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isFunLike___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLam_spec__1___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___Lean_PrettyPrinter_Delaborator_returnsPi_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_getPPFieldNotationGeneralized(lean_object*);
lean_object* l_Lean_Expr_constName_x21(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_maybeAddBlockImplicit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectTrivialBottomUps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_nameNotRoundtrippable_containsNum___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_getPPAnalyzeTrustOfScientific(lean_object*);
LEAN_EXPORT lean_object* l_Lean_pp_analyze;
uint8_t l_Lean_getPPInstances(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_maybeAddBlockImplicit_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_hasMVarAtCurrDepth(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectTrivialBottomUps_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_withKnowing___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getPPAnalysisNoDot___boxed(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_____private_Lean_Meta_Basic_0__Lean_Meta_beqInfoCacheKey____x40_Lean_Meta_Basic___hyg_1324__spec__0(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBool(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeAppStaged___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_inspectOutParams_inspectAux___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst_spec__0___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getPPAnalysisHole___boxed(lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getResetPostponed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core_spec__2_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_withKnowing___redArg(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_hasMVarAtCurrDepth___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_getPPAnalyzeExplicitHoles(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SubExpr_Pos_pushNaryArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_hBinOpHeuristic_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_checkOutParams_spec__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectBottomUps___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_447_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLam_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectBottomUps_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit_spec__2_spec__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_tryUnify___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_instMonadReaderOfSubExprAnalyzeM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KVMap_setBool(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_isNonConstFun___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_checkKnowsType___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getPPAnalyzeTrustOfScientific___boxed(lean_object*);
uint8_t l_Lean_getPPInstanceTypes(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getPPAnalysisSkip___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getPPAnalyzeExplicitHoles___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryFn___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeFn_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLam(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_checkpointDefEq___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_checkpointDefEq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLam_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBool_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeArg___lam__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_247_(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectTrivialBottomUps_spec__0___boxed(lean_object**);
lean_object* l_Lean_SubExpr_Pos_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBool_spec__0___redArg___boxed(lean_object*, lean_object*);
uint8_t l_Lean_Expr_binderInfo(lean_object*);
LEAN_EXPORT uint8_t l_Lean_getPPAnalyzeTrustSubtypeMk(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_topDownAnalyze___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingDomain___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLam_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHigherOrder(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_setElabConfig(lean_object*);
lean_object* l_Lean_Meta_forallMetaBoundedTelescope(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_topDownAnalyze___lam__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_hasLevelMVarAtCurrDepth___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_canBottomUp_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectBottomUps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___Lean_PrettyPrinter_Delaborator_returnsPi_spec__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_getPPAnalysisBlockImplicit(lean_object*);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingDomain_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_mvarName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_getPPAnalysisNoDot(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getPPAnalyzeKnowsType___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_getPPAnalysisSkip(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeFailureId;
LEAN_EXPORT lean_object* l_Lean_getPPAnalyzeTrustSubst___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core_spec__2_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getPPAnalyzeTrustOfNat___boxed(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_NameHashSet_insert_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryFn___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeFn_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBool_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectBottomUps_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeMData(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PrettyPrinter_Delaborator_isIdLike(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_getPPAnalysisHole(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___Lean_PrettyPrinter_Delaborator_returnsPi_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectBottomUps_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_topDownAnalyze___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FindLevelMVar_main(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core_spec__2_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isSubstLike___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeProj_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_annotateNamedArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_returnsPi___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_containsBadMax___lam__0(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_getPPAnalyzeTrustSubst(lean_object*);
uint64_t l_Lean_Name_hash___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core_spec__2_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLam_spec__1_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_getPPAnalysisNeedsType(lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* l_Lean_SubExpr_mkRoot(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core_spec__2___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLam_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectBottomUps_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_Meta_saveState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core_spec__2_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isTrivialBottomUp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_RBNode_find___at___Lean_PrettyPrinter_Delaborator_OptionsPerPos_insertAt_spec__2___redArg(lean_object*, lean_object*);
uint8_t l_Lean_isStructure(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at___Lean_Meta_getParamNames_spec__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_getPPAnalyze(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___Lean_PrettyPrinter_Delaborator_topDownAnalyze_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeSort___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeFn_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_hasLevelMVarAtCurrDepth___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectBottomUps_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_getPPAnalyzeTrustKnownFOType2TypeHOFuns(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectBottomUps___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectBottomUps___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_instMonadReaderOfSubExprAnalyzeM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getPPAnalyzeOmitMax___boxed(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_hBinOpHeuristic_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit_spec__2_spec__2___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectBottomUps_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* l_EStateM_seqRight(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_pp_analyze_trustId;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_isIdLike___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core_spec__2_spec__2_spec__3___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_findLevelDepth_x3f(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_containsBadMax(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit_spec__2_spec__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_0__Lean_PrettyPrinter_Delaborator_TopDownAnalyze_valUnknown___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getPPAnalyzeTrustId___boxed(lean_object*);
uint8_t l_Lean_Expr_hasLevelParam(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KVMap_findCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeSort___redArg(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_annotateNamedArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_containsBadMax___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_maybeAddBlockImplicit_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_canBottomUp_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_checkKnowsType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHigherOrder___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SubExpr_Pos_pushNaryFn(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingBody_x21(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit_spec__2_spec__2___redArg___lam__0(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_pp_analyze_trustOfNat;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___lam__0(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLam_spec__1___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_topDownAnalyze___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_pp_analyze_checkInstances;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_327_(lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_isType2Type___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeFVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_tryUnify___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_withTraceNode___at___Lean_Meta_processPostponed_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_getPPAnalysisLetVarType(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getPPAnalyzeCheckInstances___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_checkKnowsType___redArg___boxed(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_pp_analyze_typeAscriptions;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_pp_analyze_trustOfScientific;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_isStructureInstance___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_hasMVarAtCurrDepth___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_tryUnify___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_withKnowing(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_getPPProofs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeArg___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_any___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_getPPAnalyzeTrustOfNat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_hBinOpHeuristic___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isTrivialBottomUp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_checkOutParams_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_407_(lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_tryUnify(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_NameHashSet_insert_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_167_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_isType2Type___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_87_(lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
uint8_t l_Lean_Expr_bindingInfo_x21(lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzePi(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_canBottomUp_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isConstructorApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_setPostponed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectHigherOrders_spec__0___boxed(lean_object**);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_isFOLike(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_maybeAddBlockImplicit_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getPPAnalysisBlockImplicit___boxed(lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectTrivialBottomUps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getPPAnalysisNamedArg___boxed(lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_throwAlreadyImported_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getPPAnalyze___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLam_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingDomain___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLam_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core_spec__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_isFOLike___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___Lean_PrettyPrinter_Delaborator_returnsPi_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeFn_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_3632_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetValue___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_getPPAnalyzeTrustKnownFOType2TypeHOFuns___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit_spec__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_getPPProofsWithType(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit_spec__2_spec__2___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_processPostponed(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_checkpointDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_7_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = lean_mk_string_unchecked("pp", 2, 2);
x_3 = lean_mk_string_unchecked("analyze", 7, 7);
lean_inc(x_3);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(0);
x_6 = lean_mk_string_unchecked("pp.analyze", 10, 10);
x_7 = lean_mk_string_unchecked("(pretty printer analyzer) try to determine annotations sufficient to ensure round-tripping", 90, 90);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_6);
lean_ctor_set(x_8, 2, x_7);
x_9 = lean_mk_string_unchecked("Lean", 4, 4);
x_10 = l_Lean_Name_mkStr3(x_9, x_2, x_3);
x_11 = l_Lean_Option_register___at___Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Options___hyg_45__spec__0(x_4, x_8, x_10, x_1);
lean_dec(x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_47_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = lean_mk_string_unchecked("pp", 2, 2);
x_3 = lean_mk_string_unchecked("analyze", 7, 7);
x_4 = lean_mk_string_unchecked("checkInstances", 14, 14);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_5 = l_Lean_Name_mkStr3(x_2, x_3, x_4);
x_6 = lean_box(0);
x_7 = lean_mk_string_unchecked("pp.analyze", 10, 10);
x_8 = lean_mk_string_unchecked("(pretty printer analyzer) confirm that instances can be re-synthesized", 70, 70);
x_9 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_7);
lean_ctor_set(x_9, 2, x_8);
x_10 = lean_mk_string_unchecked("Lean", 4, 4);
x_11 = l_Lean_Name_mkStr4(x_10, x_2, x_3, x_4);
x_12 = l_Lean_Option_register___at___Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Options___hyg_45__spec__0(x_5, x_9, x_11, x_1);
lean_dec(x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_87_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = lean_mk_string_unchecked("pp", 2, 2);
x_3 = lean_mk_string_unchecked("analyze", 7, 7);
x_4 = lean_mk_string_unchecked("typeAscriptions", 15, 15);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_5 = l_Lean_Name_mkStr3(x_2, x_3, x_4);
x_6 = lean_box(1);
x_7 = lean_mk_string_unchecked("pp.analyze", 10, 10);
x_8 = lean_mk_string_unchecked("(pretty printer analyzer) add type ascriptions when deemed necessary", 68, 68);
x_9 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_7);
lean_ctor_set(x_9, 2, x_8);
x_10 = lean_mk_string_unchecked("Lean", 4, 4);
x_11 = l_Lean_Name_mkStr4(x_10, x_2, x_3, x_4);
x_12 = l_Lean_Option_register___at___Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Options___hyg_45__spec__0(x_5, x_9, x_11, x_1);
lean_dec(x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_127_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = lean_mk_string_unchecked("pp", 2, 2);
x_3 = lean_mk_string_unchecked("analyze", 7, 7);
x_4 = lean_mk_string_unchecked("trustSubst", 10, 10);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_5 = l_Lean_Name_mkStr3(x_2, x_3, x_4);
x_6 = lean_box(0);
x_7 = lean_mk_string_unchecked("pp.analyze", 10, 10);
x_8 = lean_mk_string_unchecked("(pretty printer analyzer) always 'pretend' applications that can delab to ▸ are 'regular'", 91, 89);
x_9 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_7);
lean_ctor_set(x_9, 2, x_8);
x_10 = lean_mk_string_unchecked("Lean", 4, 4);
x_11 = l_Lean_Name_mkStr4(x_10, x_2, x_3, x_4);
x_12 = l_Lean_Option_register___at___Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Options___hyg_45__spec__0(x_5, x_9, x_11, x_1);
lean_dec(x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_167_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = lean_mk_string_unchecked("pp", 2, 2);
x_3 = lean_mk_string_unchecked("analyze", 7, 7);
x_4 = lean_mk_string_unchecked("trustOfNat", 10, 10);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_5 = l_Lean_Name_mkStr3(x_2, x_3, x_4);
x_6 = lean_box(1);
x_7 = lean_mk_string_unchecked("pp.analyze", 10, 10);
x_8 = lean_mk_string_unchecked("(pretty printer analyzer) always 'pretend' `OfNat.ofNat` applications can elab bottom-up", 88, 88);
x_9 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_7);
lean_ctor_set(x_9, 2, x_8);
x_10 = lean_mk_string_unchecked("Lean", 4, 4);
x_11 = l_Lean_Name_mkStr4(x_10, x_2, x_3, x_4);
x_12 = l_Lean_Option_register___at___Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Options___hyg_45__spec__0(x_5, x_9, x_11, x_1);
lean_dec(x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_207_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = lean_mk_string_unchecked("pp", 2, 2);
x_3 = lean_mk_string_unchecked("analyze", 7, 7);
x_4 = lean_mk_string_unchecked("trustOfScientific", 17, 17);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_5 = l_Lean_Name_mkStr3(x_2, x_3, x_4);
x_6 = lean_box(1);
x_7 = lean_mk_string_unchecked("pp.analyze", 10, 10);
x_8 = lean_mk_string_unchecked("(pretty printer analyzer) always 'pretend' `OfScientific.ofScientific` applications can elab bottom-up", 102, 102);
x_9 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_7);
lean_ctor_set(x_9, 2, x_8);
x_10 = lean_mk_string_unchecked("Lean", 4, 4);
x_11 = l_Lean_Name_mkStr4(x_10, x_2, x_3, x_4);
x_12 = l_Lean_Option_register___at___Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Options___hyg_45__spec__0(x_5, x_9, x_11, x_1);
lean_dec(x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_247_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = lean_mk_string_unchecked("pp", 2, 2);
x_3 = lean_mk_string_unchecked("analyze", 7, 7);
x_4 = lean_mk_string_unchecked("trustSubtypeMk", 14, 14);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_5 = l_Lean_Name_mkStr3(x_2, x_3, x_4);
x_6 = lean_box(1);
x_7 = lean_mk_string_unchecked("pp.analyze", 10, 10);
x_8 = lean_mk_string_unchecked("(pretty printer analyzer) assume the implicit arguments of Subtype.mk can be inferred", 85, 85);
x_9 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_7);
lean_ctor_set(x_9, 2, x_8);
x_10 = lean_mk_string_unchecked("Lean", 4, 4);
x_11 = l_Lean_Name_mkStr4(x_10, x_2, x_3, x_4);
x_12 = l_Lean_Option_register___at___Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Options___hyg_45__spec__0(x_5, x_9, x_11, x_1);
lean_dec(x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_287_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = lean_mk_string_unchecked("pp", 2, 2);
x_3 = lean_mk_string_unchecked("analyze", 7, 7);
x_4 = lean_mk_string_unchecked("trustId", 7, 7);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_5 = l_Lean_Name_mkStr3(x_2, x_3, x_4);
x_6 = lean_box(1);
x_7 = lean_mk_string_unchecked("pp.analyze", 10, 10);
x_8 = lean_mk_string_unchecked("(pretty printer analyzer) always assume an implicit `fun x => x` can be inferred", 80, 80);
x_9 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_7);
lean_ctor_set(x_9, 2, x_8);
x_10 = lean_mk_string_unchecked("Lean", 4, 4);
x_11 = l_Lean_Name_mkStr4(x_10, x_2, x_3, x_4);
x_12 = l_Lean_Option_register___at___Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Options___hyg_45__spec__0(x_5, x_9, x_11, x_1);
lean_dec(x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_327_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = lean_mk_string_unchecked("pp", 2, 2);
x_3 = lean_mk_string_unchecked("analyze", 7, 7);
x_4 = lean_mk_string_unchecked("trustKnownFOType2TypeHOFuns", 27, 27);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_5 = l_Lean_Name_mkStr3(x_2, x_3, x_4);
x_6 = lean_box(1);
x_7 = lean_mk_string_unchecked("pp.analyze", 10, 10);
x_8 = lean_mk_string_unchecked("(pretty printer analyzer) omit higher-order functions whose values seem to be knownType2Type", 92, 92);
x_9 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_7);
lean_ctor_set(x_9, 2, x_8);
x_10 = lean_mk_string_unchecked("Lean", 4, 4);
x_11 = l_Lean_Name_mkStr4(x_10, x_2, x_3, x_4);
x_12 = l_Lean_Option_register___at___Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Options___hyg_45__spec__0(x_5, x_9, x_11, x_1);
lean_dec(x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_367_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = lean_mk_string_unchecked("pp", 2, 2);
x_3 = lean_mk_string_unchecked("analyze", 7, 7);
x_4 = lean_mk_string_unchecked("omitMax", 7, 7);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_5 = l_Lean_Name_mkStr3(x_2, x_3, x_4);
x_6 = lean_box(1);
x_7 = lean_mk_string_unchecked("pp.analyze", 10, 10);
x_8 = lean_mk_string_unchecked("(pretty printer analyzer) omit universe `max` annotations (these constraints can actually hurt)", 95, 95);
x_9 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_7);
lean_ctor_set(x_9, 2, x_8);
x_10 = lean_mk_string_unchecked("Lean", 4, 4);
x_11 = l_Lean_Name_mkStr4(x_10, x_2, x_3, x_4);
x_12 = l_Lean_Option_register___at___Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Options___hyg_45__spec__0(x_5, x_9, x_11, x_1);
lean_dec(x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_407_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = lean_mk_string_unchecked("pp", 2, 2);
x_3 = lean_mk_string_unchecked("analyze", 7, 7);
x_4 = lean_mk_string_unchecked("knowsType", 9, 9);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_5 = l_Lean_Name_mkStr3(x_2, x_3, x_4);
x_6 = lean_box(1);
x_7 = lean_mk_string_unchecked("pp.analyze", 10, 10);
x_8 = lean_mk_string_unchecked("(pretty printer analyzer) assume the type of the original expression is known", 77, 77);
x_9 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_7);
lean_ctor_set(x_9, 2, x_8);
x_10 = lean_mk_string_unchecked("Lean", 4, 4);
x_11 = l_Lean_Name_mkStr4(x_10, x_2, x_3, x_4);
x_12 = l_Lean_Option_register___at___Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Options___hyg_45__spec__0(x_5, x_9, x_11, x_1);
lean_dec(x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_447_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = lean_mk_string_unchecked("pp", 2, 2);
x_3 = lean_mk_string_unchecked("analyze", 7, 7);
x_4 = lean_mk_string_unchecked("explicitHoles", 13, 13);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_5 = l_Lean_Name_mkStr3(x_2, x_3, x_4);
x_6 = lean_box(0);
x_7 = lean_mk_string_unchecked("pp.analyze", 10, 10);
x_8 = lean_mk_string_unchecked("(pretty printer analyzer) use `_` for explicit arguments that can be inferred", 77, 77);
x_9 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_7);
lean_ctor_set(x_9, 2, x_8);
x_10 = lean_mk_string_unchecked("Lean", 4, 4);
x_11 = l_Lean_Name_mkStr4(x_10, x_2, x_3, x_4);
x_12 = l_Lean_Option_register___at___Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Options___hyg_45__spec__0(x_5, x_9, x_11, x_1);
lean_dec(x_9);
return x_12;
}
}
LEAN_EXPORT uint8_t l_Lean_getPPAnalyze(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_pp_analyze;
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = l_Lean_KVMap_findCore(x_1, x_3);
lean_dec(x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = lean_unbox(x_4);
lean_dec(x_4);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
if (lean_obj_tag(x_7) == 1)
{
uint8_t x_8; 
lean_dec(x_4);
x_8 = lean_ctor_get_uint8(x_7, 0);
lean_dec(x_7);
return x_8;
}
else
{
uint8_t x_9; 
lean_dec(x_7);
x_9 = lean_unbox(x_4);
lean_dec(x_4);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getPPAnalyze___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_getPPAnalyze(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_getPPAnalyzeCheckInstances(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_pp_analyze_checkInstances;
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = l_Lean_KVMap_findCore(x_1, x_3);
lean_dec(x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = lean_unbox(x_4);
lean_dec(x_4);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
if (lean_obj_tag(x_7) == 1)
{
uint8_t x_8; 
lean_dec(x_4);
x_8 = lean_ctor_get_uint8(x_7, 0);
lean_dec(x_7);
return x_8;
}
else
{
uint8_t x_9; 
lean_dec(x_7);
x_9 = lean_unbox(x_4);
lean_dec(x_4);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getPPAnalyzeCheckInstances___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_getPPAnalyzeCheckInstances(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_getPPAnalyzeTypeAscriptions(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_pp_analyze_typeAscriptions;
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = l_Lean_KVMap_findCore(x_1, x_3);
lean_dec(x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = lean_unbox(x_4);
lean_dec(x_4);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
if (lean_obj_tag(x_7) == 1)
{
uint8_t x_8; 
lean_dec(x_4);
x_8 = lean_ctor_get_uint8(x_7, 0);
lean_dec(x_7);
return x_8;
}
else
{
uint8_t x_9; 
lean_dec(x_7);
x_9 = lean_unbox(x_4);
lean_dec(x_4);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getPPAnalyzeTypeAscriptions___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_getPPAnalyzeTypeAscriptions(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_getPPAnalyzeTrustSubst(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_pp_analyze_trustSubst;
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = l_Lean_KVMap_findCore(x_1, x_3);
lean_dec(x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = lean_unbox(x_4);
lean_dec(x_4);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
if (lean_obj_tag(x_7) == 1)
{
uint8_t x_8; 
lean_dec(x_4);
x_8 = lean_ctor_get_uint8(x_7, 0);
lean_dec(x_7);
return x_8;
}
else
{
uint8_t x_9; 
lean_dec(x_7);
x_9 = lean_unbox(x_4);
lean_dec(x_4);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getPPAnalyzeTrustSubst___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_getPPAnalyzeTrustSubst(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_getPPAnalyzeTrustOfNat(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_pp_analyze_trustOfNat;
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = l_Lean_KVMap_findCore(x_1, x_3);
lean_dec(x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = lean_unbox(x_4);
lean_dec(x_4);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
if (lean_obj_tag(x_7) == 1)
{
uint8_t x_8; 
lean_dec(x_4);
x_8 = lean_ctor_get_uint8(x_7, 0);
lean_dec(x_7);
return x_8;
}
else
{
uint8_t x_9; 
lean_dec(x_7);
x_9 = lean_unbox(x_4);
lean_dec(x_4);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getPPAnalyzeTrustOfNat___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_getPPAnalyzeTrustOfNat(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_getPPAnalyzeTrustOfScientific(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_pp_analyze_trustOfScientific;
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = l_Lean_KVMap_findCore(x_1, x_3);
lean_dec(x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = lean_unbox(x_4);
lean_dec(x_4);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
if (lean_obj_tag(x_7) == 1)
{
uint8_t x_8; 
lean_dec(x_4);
x_8 = lean_ctor_get_uint8(x_7, 0);
lean_dec(x_7);
return x_8;
}
else
{
uint8_t x_9; 
lean_dec(x_7);
x_9 = lean_unbox(x_4);
lean_dec(x_4);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getPPAnalyzeTrustOfScientific___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_getPPAnalyzeTrustOfScientific(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_getPPAnalyzeTrustId(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_pp_analyze_trustId;
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = l_Lean_KVMap_findCore(x_1, x_3);
lean_dec(x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = lean_unbox(x_4);
lean_dec(x_4);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
if (lean_obj_tag(x_7) == 1)
{
uint8_t x_8; 
lean_dec(x_4);
x_8 = lean_ctor_get_uint8(x_7, 0);
lean_dec(x_7);
return x_8;
}
else
{
uint8_t x_9; 
lean_dec(x_7);
x_9 = lean_unbox(x_4);
lean_dec(x_4);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getPPAnalyzeTrustId___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_getPPAnalyzeTrustId(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_getPPAnalyzeTrustSubtypeMk(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_pp_analyze_trustSubtypeMk;
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = l_Lean_KVMap_findCore(x_1, x_3);
lean_dec(x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = lean_unbox(x_4);
lean_dec(x_4);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
if (lean_obj_tag(x_7) == 1)
{
uint8_t x_8; 
lean_dec(x_4);
x_8 = lean_ctor_get_uint8(x_7, 0);
lean_dec(x_7);
return x_8;
}
else
{
uint8_t x_9; 
lean_dec(x_7);
x_9 = lean_unbox(x_4);
lean_dec(x_4);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getPPAnalyzeTrustSubtypeMk___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_getPPAnalyzeTrustSubtypeMk(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_getPPAnalyzeTrustKnownFOType2TypeHOFuns(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_pp_analyze_trustKnownFOType2TypeHOFuns;
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = l_Lean_KVMap_findCore(x_1, x_3);
lean_dec(x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = lean_unbox(x_4);
lean_dec(x_4);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
if (lean_obj_tag(x_7) == 1)
{
uint8_t x_8; 
lean_dec(x_4);
x_8 = lean_ctor_get_uint8(x_7, 0);
lean_dec(x_7);
return x_8;
}
else
{
uint8_t x_9; 
lean_dec(x_7);
x_9 = lean_unbox(x_4);
lean_dec(x_4);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getPPAnalyzeTrustKnownFOType2TypeHOFuns___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_getPPAnalyzeTrustKnownFOType2TypeHOFuns(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_getPPAnalyzeOmitMax(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_pp_analyze_omitMax;
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = l_Lean_KVMap_findCore(x_1, x_3);
lean_dec(x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = lean_unbox(x_4);
lean_dec(x_4);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
if (lean_obj_tag(x_7) == 1)
{
uint8_t x_8; 
lean_dec(x_4);
x_8 = lean_ctor_get_uint8(x_7, 0);
lean_dec(x_7);
return x_8;
}
else
{
uint8_t x_9; 
lean_dec(x_7);
x_9 = lean_unbox(x_4);
lean_dec(x_4);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getPPAnalyzeOmitMax___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_getPPAnalyzeOmitMax(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_getPPAnalyzeKnowsType(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_pp_analyze_knowsType;
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = l_Lean_KVMap_findCore(x_1, x_3);
lean_dec(x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = lean_unbox(x_4);
lean_dec(x_4);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
if (lean_obj_tag(x_7) == 1)
{
uint8_t x_8; 
lean_dec(x_4);
x_8 = lean_ctor_get_uint8(x_7, 0);
lean_dec(x_7);
return x_8;
}
else
{
uint8_t x_9; 
lean_dec(x_7);
x_9 = lean_unbox(x_4);
lean_dec(x_4);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getPPAnalyzeKnowsType___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_getPPAnalyzeKnowsType(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_getPPAnalyzeExplicitHoles(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_pp_analyze_explicitHoles;
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = l_Lean_KVMap_findCore(x_1, x_3);
lean_dec(x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = lean_unbox(x_4);
lean_dec(x_4);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
if (lean_obj_tag(x_7) == 1)
{
uint8_t x_8; 
lean_dec(x_4);
x_8 = lean_ctor_get_uint8(x_7, 0);
lean_dec(x_7);
return x_8;
}
else
{
uint8_t x_9; 
lean_dec(x_7);
x_9 = lean_unbox(x_4);
lean_dec(x_4);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getPPAnalyzeExplicitHoles___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_getPPAnalyzeExplicitHoles(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_getPPAnalysisSkip(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_mk_string_unchecked("pp", 2, 2);
x_3 = lean_mk_string_unchecked("analysis", 8, 8);
x_4 = lean_mk_string_unchecked("skip", 4, 4);
x_5 = l_Lean_Name_mkStr3(x_2, x_3, x_4);
x_6 = lean_box(0);
x_7 = l_Lean_KVMap_findCore(x_1, x_5);
lean_dec(x_5);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = lean_unbox(x_6);
return x_8;
}
else
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
if (lean_obj_tag(x_9) == 1)
{
uint8_t x_10; 
x_10 = lean_ctor_get_uint8(x_9, 0);
lean_dec(x_9);
return x_10;
}
else
{
uint8_t x_11; 
lean_dec(x_9);
x_11 = lean_unbox(x_6);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getPPAnalysisSkip___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_getPPAnalysisSkip(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_getPPAnalysisHole(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_mk_string_unchecked("pp", 2, 2);
x_3 = lean_mk_string_unchecked("analysis", 8, 8);
x_4 = lean_mk_string_unchecked("hole", 4, 4);
x_5 = l_Lean_Name_mkStr3(x_2, x_3, x_4);
x_6 = lean_box(0);
x_7 = l_Lean_KVMap_findCore(x_1, x_5);
lean_dec(x_5);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = lean_unbox(x_6);
return x_8;
}
else
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
if (lean_obj_tag(x_9) == 1)
{
uint8_t x_10; 
x_10 = lean_ctor_get_uint8(x_9, 0);
lean_dec(x_9);
return x_10;
}
else
{
uint8_t x_11; 
lean_dec(x_9);
x_11 = lean_unbox(x_6);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getPPAnalysisHole___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_getPPAnalysisHole(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_getPPAnalysisNamedArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_mk_string_unchecked("pp", 2, 2);
x_3 = lean_mk_string_unchecked("analysis", 8, 8);
x_4 = lean_mk_string_unchecked("namedArg", 8, 8);
x_5 = l_Lean_Name_mkStr3(x_2, x_3, x_4);
x_6 = lean_box(0);
x_7 = l_Lean_KVMap_findCore(x_1, x_5);
lean_dec(x_5);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = lean_unbox(x_6);
return x_8;
}
else
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
if (lean_obj_tag(x_9) == 1)
{
uint8_t x_10; 
x_10 = lean_ctor_get_uint8(x_9, 0);
lean_dec(x_9);
return x_10;
}
else
{
uint8_t x_11; 
lean_dec(x_9);
x_11 = lean_unbox(x_6);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getPPAnalysisNamedArg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_getPPAnalysisNamedArg(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_getPPAnalysisLetVarType(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_mk_string_unchecked("pp", 2, 2);
x_3 = lean_mk_string_unchecked("analysis", 8, 8);
x_4 = lean_mk_string_unchecked("letVarType", 10, 10);
x_5 = l_Lean_Name_mkStr3(x_2, x_3, x_4);
x_6 = lean_box(0);
x_7 = l_Lean_KVMap_findCore(x_1, x_5);
lean_dec(x_5);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = lean_unbox(x_6);
return x_8;
}
else
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
if (lean_obj_tag(x_9) == 1)
{
uint8_t x_10; 
x_10 = lean_ctor_get_uint8(x_9, 0);
lean_dec(x_9);
return x_10;
}
else
{
uint8_t x_11; 
lean_dec(x_9);
x_11 = lean_unbox(x_6);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getPPAnalysisLetVarType___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_getPPAnalysisLetVarType(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_getPPAnalysisNeedsType(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_mk_string_unchecked("pp", 2, 2);
x_3 = lean_mk_string_unchecked("analysis", 8, 8);
x_4 = lean_mk_string_unchecked("needsType", 9, 9);
x_5 = l_Lean_Name_mkStr3(x_2, x_3, x_4);
x_6 = lean_box(0);
x_7 = l_Lean_KVMap_findCore(x_1, x_5);
lean_dec(x_5);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = lean_unbox(x_6);
return x_8;
}
else
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
if (lean_obj_tag(x_9) == 1)
{
uint8_t x_10; 
x_10 = lean_ctor_get_uint8(x_9, 0);
lean_dec(x_9);
return x_10;
}
else
{
uint8_t x_11; 
lean_dec(x_9);
x_11 = lean_unbox(x_6);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getPPAnalysisNeedsType___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_getPPAnalysisNeedsType(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_getPPAnalysisBlockImplicit(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_mk_string_unchecked("pp", 2, 2);
x_3 = lean_mk_string_unchecked("analysis", 8, 8);
x_4 = lean_mk_string_unchecked("blockImplicit", 13, 13);
x_5 = l_Lean_Name_mkStr3(x_2, x_3, x_4);
x_6 = lean_box(0);
x_7 = l_Lean_KVMap_findCore(x_1, x_5);
lean_dec(x_5);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = lean_unbox(x_6);
return x_8;
}
else
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
if (lean_obj_tag(x_9) == 1)
{
uint8_t x_10; 
x_10 = lean_ctor_get_uint8(x_9, 0);
lean_dec(x_9);
return x_10;
}
else
{
uint8_t x_11; 
lean_dec(x_9);
x_11 = lean_unbox(x_6);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getPPAnalysisBlockImplicit___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_getPPAnalysisBlockImplicit(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_getPPAnalysisNoDot(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_mk_string_unchecked("pp", 2, 2);
x_3 = lean_mk_string_unchecked("analysis", 8, 8);
x_4 = lean_mk_string_unchecked("noDot", 5, 5);
x_5 = l_Lean_Name_mkStr3(x_2, x_3, x_4);
x_6 = lean_box(0);
x_7 = l_Lean_KVMap_findCore(x_1, x_5);
lean_dec(x_5);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = lean_unbox(x_6);
return x_8;
}
else
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
if (lean_obj_tag(x_9) == 1)
{
uint8_t x_10; 
x_10 = lean_ctor_get_uint8(x_9, 0);
lean_dec(x_9);
return x_10;
}
else
{
uint8_t x_11; 
lean_dec(x_9);
x_11 = lean_unbox(x_6);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getPPAnalysisNoDot___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_getPPAnalysisNoDot(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___Lean_PrettyPrinter_Delaborator_returnsPi_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_apply_7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___Lean_PrettyPrinter_Delaborator_returnsPi_spec__0___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___Lean_PrettyPrinter_Delaborator_returnsPi_spec__0___redArg___lam__0), 8, 1);
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
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___Lean_PrettyPrinter_Delaborator_returnsPi_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_lambdaTelescope___at___Lean_PrettyPrinter_Delaborator_returnsPi_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_returnsPi___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Lean_Expr_isForall(x_2);
x_9 = lean_box(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_returnsPi(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_7 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_returnsPi___lam__0___boxed), 7, 0);
x_8 = lean_box(0);
x_9 = lean_unbox(x_8);
x_10 = l_Lean_Meta_lambdaTelescope___at___Lean_PrettyPrinter_Delaborator_returnsPi_spec__0___redArg(x_1, x_7, x_9, x_2, x_3, x_4, x_5, x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___Lean_PrettyPrinter_Delaborator_returnsPi_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lean_Meta_lambdaTelescope___at___Lean_PrettyPrinter_Delaborator_returnsPi_spec__0___redArg(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___Lean_PrettyPrinter_Delaborator_returnsPi_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = l_Lean_Meta_lambdaTelescope___at___Lean_PrettyPrinter_Delaborator_returnsPi_spec__0(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_returnsPi___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Delaborator_returnsPi___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_isNonConstFun___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 6)
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 2);
x_1 = x_3;
goto _start;
}
else
{
uint8_t x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Lean_Expr_hasLooseBVars(x_1);
x_6 = lean_box(x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_2);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_isNonConstFun(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Delaborator_isNonConstFun___redArg(x_1, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_isNonConstFun___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PrettyPrinter_Delaborator_isNonConstFun___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_isNonConstFun___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Delaborator_isNonConstFun(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_isSimpleHOFun(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_1);
x_7 = l_Lean_PrettyPrinter_Delaborator_returnsPi(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_PrettyPrinter_Delaborator_isNonConstFun___redArg(x_1, x_9);
lean_dec(x_1);
x_11 = lean_unbox(x_8);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
uint8_t x_14; 
lean_dec(x_8);
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_10, 0);
lean_dec(x_15);
x_16 = lean_box(1);
lean_ctor_set(x_10, 0, x_16);
return x_10;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_dec(x_10);
x_18 = lean_box(1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_10);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_10, 0);
lean_dec(x_21);
lean_ctor_set(x_10, 0, x_8);
return x_10;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_10, 1);
lean_inc(x_22);
lean_dec(x_10);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_8);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
else
{
uint8_t x_24; 
lean_dec(x_8);
x_24 = !lean_is_exclusive(x_10);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_10, 0);
lean_dec(x_25);
x_26 = lean_box(0);
lean_ctor_set(x_10, 0, x_26);
return x_10;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_10, 1);
lean_inc(x_27);
lean_dec(x_10);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
}
else
{
lean_dec(x_1);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_isType2Type___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_isType2Type(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_7 = lean_infer_type(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 7)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
switch (lean_obj_tag(x_9)) {
case 0:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_8, 2);
lean_inc(x_12);
x_13 = lean_ctor_get_uint8(x_8, sizeof(void*)*3 + 8);
lean_dec(x_8);
x_14 = lean_ctor_get(x_9, 0);
lean_inc(x_14);
lean_dec(x_9);
x_15 = l_Lean_Expr_bvar___override(x_14);
x_16 = l_Lean_Expr_forallE___override(x_11, x_15, x_12, x_13);
x_17 = l_Lean_PrettyPrinter_Delaborator_isType2Type___lam__0(x_16, x_2, x_3, x_4, x_5, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_16);
return x_17;
}
case 1:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_18 = lean_ctor_get(x_7, 1);
lean_inc(x_18);
lean_dec(x_7);
x_19 = lean_ctor_get(x_8, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_8, 2);
lean_inc(x_20);
x_21 = lean_ctor_get_uint8(x_8, sizeof(void*)*3 + 8);
lean_dec(x_8);
x_22 = lean_ctor_get(x_9, 0);
lean_inc(x_22);
lean_dec(x_9);
x_23 = l_Lean_Expr_fvar___override(x_22);
x_24 = l_Lean_Expr_forallE___override(x_19, x_23, x_20, x_21);
x_25 = l_Lean_PrettyPrinter_Delaborator_isType2Type___lam__0(x_24, x_2, x_3, x_4, x_5, x_18);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_24);
return x_25;
}
case 2:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_26 = lean_ctor_get(x_7, 1);
lean_inc(x_26);
lean_dec(x_7);
x_27 = lean_ctor_get(x_8, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_8, 2);
lean_inc(x_28);
x_29 = lean_ctor_get_uint8(x_8, sizeof(void*)*3 + 8);
lean_dec(x_8);
x_30 = lean_ctor_get(x_9, 0);
lean_inc(x_30);
lean_dec(x_9);
x_31 = l_Lean_Expr_mvar___override(x_30);
x_32 = l_Lean_Expr_forallE___override(x_27, x_31, x_28, x_29);
x_33 = l_Lean_PrettyPrinter_Delaborator_isType2Type___lam__0(x_32, x_2, x_3, x_4, x_5, x_26);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_32);
return x_33;
}
case 3:
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_8, 2);
lean_inc(x_34);
switch (lean_obj_tag(x_34)) {
case 0:
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_35 = lean_ctor_get(x_7, 1);
lean_inc(x_35);
lean_dec(x_7);
x_36 = lean_ctor_get(x_8, 0);
lean_inc(x_36);
x_37 = lean_ctor_get_uint8(x_8, sizeof(void*)*3 + 8);
lean_dec(x_8);
x_38 = lean_ctor_get(x_9, 0);
lean_inc(x_38);
lean_dec(x_9);
x_39 = lean_ctor_get(x_34, 0);
lean_inc(x_39);
lean_dec(x_34);
x_40 = l_Lean_Expr_sort___override(x_38);
x_41 = l_Lean_Expr_bvar___override(x_39);
x_42 = l_Lean_Expr_forallE___override(x_36, x_40, x_41, x_37);
x_43 = l_Lean_PrettyPrinter_Delaborator_isType2Type___lam__0(x_42, x_2, x_3, x_4, x_5, x_35);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_42);
return x_43;
}
case 1:
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_44 = lean_ctor_get(x_7, 1);
lean_inc(x_44);
lean_dec(x_7);
x_45 = lean_ctor_get(x_8, 0);
lean_inc(x_45);
x_46 = lean_ctor_get_uint8(x_8, sizeof(void*)*3 + 8);
lean_dec(x_8);
x_47 = lean_ctor_get(x_9, 0);
lean_inc(x_47);
lean_dec(x_9);
x_48 = lean_ctor_get(x_34, 0);
lean_inc(x_48);
lean_dec(x_34);
x_49 = l_Lean_Expr_sort___override(x_47);
x_50 = l_Lean_Expr_fvar___override(x_48);
x_51 = l_Lean_Expr_forallE___override(x_45, x_49, x_50, x_46);
x_52 = l_Lean_PrettyPrinter_Delaborator_isType2Type___lam__0(x_51, x_2, x_3, x_4, x_5, x_44);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_51);
return x_52;
}
case 2:
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_53 = lean_ctor_get(x_7, 1);
lean_inc(x_53);
lean_dec(x_7);
x_54 = lean_ctor_get(x_8, 0);
lean_inc(x_54);
x_55 = lean_ctor_get_uint8(x_8, sizeof(void*)*3 + 8);
lean_dec(x_8);
x_56 = lean_ctor_get(x_9, 0);
lean_inc(x_56);
lean_dec(x_9);
x_57 = lean_ctor_get(x_34, 0);
lean_inc(x_57);
lean_dec(x_34);
x_58 = l_Lean_Expr_sort___override(x_56);
x_59 = l_Lean_Expr_mvar___override(x_57);
x_60 = l_Lean_Expr_forallE___override(x_54, x_58, x_59, x_55);
x_61 = l_Lean_PrettyPrinter_Delaborator_isType2Type___lam__0(x_60, x_2, x_3, x_4, x_5, x_53);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_60);
return x_61;
}
case 3:
{
uint8_t x_62; 
lean_dec(x_34);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_62 = !lean_is_exclusive(x_7);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_7, 0);
lean_dec(x_63);
x_64 = lean_box(1);
lean_ctor_set(x_7, 0, x_64);
return x_7;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_7, 1);
lean_inc(x_65);
lean_dec(x_7);
x_66 = lean_box(1);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
}
case 4:
{
lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_68 = lean_ctor_get(x_7, 1);
lean_inc(x_68);
lean_dec(x_7);
x_69 = lean_ctor_get(x_8, 0);
lean_inc(x_69);
x_70 = lean_ctor_get_uint8(x_8, sizeof(void*)*3 + 8);
lean_dec(x_8);
x_71 = lean_ctor_get(x_9, 0);
lean_inc(x_71);
lean_dec(x_9);
x_72 = lean_ctor_get(x_34, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_34, 1);
lean_inc(x_73);
lean_dec(x_34);
x_74 = l_Lean_Expr_sort___override(x_71);
x_75 = l_Lean_Expr_const___override(x_72, x_73);
x_76 = l_Lean_Expr_forallE___override(x_69, x_74, x_75, x_70);
x_77 = l_Lean_PrettyPrinter_Delaborator_isType2Type___lam__0(x_76, x_2, x_3, x_4, x_5, x_68);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_76);
return x_77;
}
case 5:
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_78 = lean_ctor_get(x_7, 1);
lean_inc(x_78);
lean_dec(x_7);
x_79 = lean_ctor_get(x_8, 0);
lean_inc(x_79);
x_80 = lean_ctor_get_uint8(x_8, sizeof(void*)*3 + 8);
lean_dec(x_8);
x_81 = lean_ctor_get(x_9, 0);
lean_inc(x_81);
lean_dec(x_9);
x_82 = lean_ctor_get(x_34, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_34, 1);
lean_inc(x_83);
lean_dec(x_34);
x_84 = l_Lean_Expr_sort___override(x_81);
x_85 = l_Lean_Expr_app___override(x_82, x_83);
x_86 = l_Lean_Expr_forallE___override(x_79, x_84, x_85, x_80);
x_87 = l_Lean_PrettyPrinter_Delaborator_isType2Type___lam__0(x_86, x_2, x_3, x_4, x_5, x_78);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_86);
return x_87;
}
case 6:
{
lean_object* x_88; lean_object* x_89; uint8_t x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_88 = lean_ctor_get(x_7, 1);
lean_inc(x_88);
lean_dec(x_7);
x_89 = lean_ctor_get(x_8, 0);
lean_inc(x_89);
x_90 = lean_ctor_get_uint8(x_8, sizeof(void*)*3 + 8);
lean_dec(x_8);
x_91 = lean_ctor_get(x_9, 0);
lean_inc(x_91);
lean_dec(x_9);
x_92 = lean_ctor_get(x_34, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_34, 1);
lean_inc(x_93);
x_94 = lean_ctor_get(x_34, 2);
lean_inc(x_94);
x_95 = lean_ctor_get_uint8(x_34, sizeof(void*)*3 + 8);
lean_dec(x_34);
x_96 = l_Lean_Expr_sort___override(x_91);
x_97 = l_Lean_Expr_lam___override(x_92, x_93, x_94, x_95);
x_98 = l_Lean_Expr_forallE___override(x_89, x_96, x_97, x_90);
x_99 = l_Lean_PrettyPrinter_Delaborator_isType2Type___lam__0(x_98, x_2, x_3, x_4, x_5, x_88);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_98);
return x_99;
}
case 7:
{
lean_object* x_100; lean_object* x_101; uint8_t x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_100 = lean_ctor_get(x_7, 1);
lean_inc(x_100);
lean_dec(x_7);
x_101 = lean_ctor_get(x_8, 0);
lean_inc(x_101);
x_102 = lean_ctor_get_uint8(x_8, sizeof(void*)*3 + 8);
lean_dec(x_8);
x_103 = lean_ctor_get(x_9, 0);
lean_inc(x_103);
lean_dec(x_9);
x_104 = lean_ctor_get(x_34, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_34, 1);
lean_inc(x_105);
x_106 = lean_ctor_get(x_34, 2);
lean_inc(x_106);
x_107 = lean_ctor_get_uint8(x_34, sizeof(void*)*3 + 8);
lean_dec(x_34);
x_108 = l_Lean_Expr_sort___override(x_103);
x_109 = l_Lean_Expr_forallE___override(x_104, x_105, x_106, x_107);
x_110 = l_Lean_Expr_forallE___override(x_101, x_108, x_109, x_102);
x_111 = l_Lean_PrettyPrinter_Delaborator_isType2Type___lam__0(x_110, x_2, x_3, x_4, x_5, x_100);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_110);
return x_111;
}
case 8:
{
lean_object* x_112; lean_object* x_113; uint8_t x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_112 = lean_ctor_get(x_7, 1);
lean_inc(x_112);
lean_dec(x_7);
x_113 = lean_ctor_get(x_8, 0);
lean_inc(x_113);
x_114 = lean_ctor_get_uint8(x_8, sizeof(void*)*3 + 8);
lean_dec(x_8);
x_115 = lean_ctor_get(x_9, 0);
lean_inc(x_115);
lean_dec(x_9);
x_116 = lean_ctor_get(x_34, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_34, 1);
lean_inc(x_117);
x_118 = lean_ctor_get(x_34, 2);
lean_inc(x_118);
x_119 = lean_ctor_get(x_34, 3);
lean_inc(x_119);
x_120 = lean_ctor_get_uint8(x_34, sizeof(void*)*4 + 8);
lean_dec(x_34);
x_121 = l_Lean_Expr_sort___override(x_115);
x_122 = l_Lean_Expr_letE___override(x_116, x_117, x_118, x_119, x_120);
x_123 = l_Lean_Expr_forallE___override(x_113, x_121, x_122, x_114);
x_124 = l_Lean_PrettyPrinter_Delaborator_isType2Type___lam__0(x_123, x_2, x_3, x_4, x_5, x_112);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_123);
return x_124;
}
case 9:
{
lean_object* x_125; lean_object* x_126; uint8_t x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_125 = lean_ctor_get(x_7, 1);
lean_inc(x_125);
lean_dec(x_7);
x_126 = lean_ctor_get(x_8, 0);
lean_inc(x_126);
x_127 = lean_ctor_get_uint8(x_8, sizeof(void*)*3 + 8);
lean_dec(x_8);
x_128 = lean_ctor_get(x_9, 0);
lean_inc(x_128);
lean_dec(x_9);
x_129 = lean_ctor_get(x_34, 0);
lean_inc(x_129);
lean_dec(x_34);
x_130 = l_Lean_Expr_sort___override(x_128);
x_131 = l_Lean_Expr_lit___override(x_129);
x_132 = l_Lean_Expr_forallE___override(x_126, x_130, x_131, x_127);
x_133 = l_Lean_PrettyPrinter_Delaborator_isType2Type___lam__0(x_132, x_2, x_3, x_4, x_5, x_125);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_132);
return x_133;
}
case 10:
{
lean_object* x_134; lean_object* x_135; uint8_t x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_134 = lean_ctor_get(x_7, 1);
lean_inc(x_134);
lean_dec(x_7);
x_135 = lean_ctor_get(x_8, 0);
lean_inc(x_135);
x_136 = lean_ctor_get_uint8(x_8, sizeof(void*)*3 + 8);
lean_dec(x_8);
x_137 = lean_ctor_get(x_9, 0);
lean_inc(x_137);
lean_dec(x_9);
x_138 = lean_ctor_get(x_34, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_34, 1);
lean_inc(x_139);
lean_dec(x_34);
x_140 = l_Lean_Expr_sort___override(x_137);
x_141 = l_Lean_Expr_mdata___override(x_138, x_139);
x_142 = l_Lean_Expr_forallE___override(x_135, x_140, x_141, x_136);
x_143 = l_Lean_PrettyPrinter_Delaborator_isType2Type___lam__0(x_142, x_2, x_3, x_4, x_5, x_134);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_142);
return x_143;
}
default: 
{
lean_object* x_144; lean_object* x_145; uint8_t x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_144 = lean_ctor_get(x_7, 1);
lean_inc(x_144);
lean_dec(x_7);
x_145 = lean_ctor_get(x_8, 0);
lean_inc(x_145);
x_146 = lean_ctor_get_uint8(x_8, sizeof(void*)*3 + 8);
lean_dec(x_8);
x_147 = lean_ctor_get(x_9, 0);
lean_inc(x_147);
lean_dec(x_9);
x_148 = lean_ctor_get(x_34, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_34, 1);
lean_inc(x_149);
x_150 = lean_ctor_get(x_34, 2);
lean_inc(x_150);
lean_dec(x_34);
x_151 = l_Lean_Expr_sort___override(x_147);
x_152 = l_Lean_Expr_proj___override(x_148, x_149, x_150);
x_153 = l_Lean_Expr_forallE___override(x_145, x_151, x_152, x_146);
x_154 = l_Lean_PrettyPrinter_Delaborator_isType2Type___lam__0(x_153, x_2, x_3, x_4, x_5, x_144);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_153);
return x_154;
}
}
}
case 4:
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; uint8_t x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_155 = lean_ctor_get(x_7, 1);
lean_inc(x_155);
lean_dec(x_7);
x_156 = lean_ctor_get(x_8, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_8, 2);
lean_inc(x_157);
x_158 = lean_ctor_get_uint8(x_8, sizeof(void*)*3 + 8);
lean_dec(x_8);
x_159 = lean_ctor_get(x_9, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_9, 1);
lean_inc(x_160);
lean_dec(x_9);
x_161 = l_Lean_Expr_const___override(x_159, x_160);
x_162 = l_Lean_Expr_forallE___override(x_156, x_161, x_157, x_158);
x_163 = l_Lean_PrettyPrinter_Delaborator_isType2Type___lam__0(x_162, x_2, x_3, x_4, x_5, x_155);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_162);
return x_163;
}
case 5:
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; uint8_t x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_164 = lean_ctor_get(x_7, 1);
lean_inc(x_164);
lean_dec(x_7);
x_165 = lean_ctor_get(x_8, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_8, 2);
lean_inc(x_166);
x_167 = lean_ctor_get_uint8(x_8, sizeof(void*)*3 + 8);
lean_dec(x_8);
x_168 = lean_ctor_get(x_9, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_9, 1);
lean_inc(x_169);
lean_dec(x_9);
x_170 = l_Lean_Expr_app___override(x_168, x_169);
x_171 = l_Lean_Expr_forallE___override(x_165, x_170, x_166, x_167);
x_172 = l_Lean_PrettyPrinter_Delaborator_isType2Type___lam__0(x_171, x_2, x_3, x_4, x_5, x_164);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_171);
return x_172;
}
case 6:
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; uint8_t x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; uint8_t x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_173 = lean_ctor_get(x_7, 1);
lean_inc(x_173);
lean_dec(x_7);
x_174 = lean_ctor_get(x_8, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_8, 2);
lean_inc(x_175);
x_176 = lean_ctor_get_uint8(x_8, sizeof(void*)*3 + 8);
lean_dec(x_8);
x_177 = lean_ctor_get(x_9, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_9, 1);
lean_inc(x_178);
x_179 = lean_ctor_get(x_9, 2);
lean_inc(x_179);
x_180 = lean_ctor_get_uint8(x_9, sizeof(void*)*3 + 8);
lean_dec(x_9);
x_181 = l_Lean_Expr_lam___override(x_177, x_178, x_179, x_180);
x_182 = l_Lean_Expr_forallE___override(x_174, x_181, x_175, x_176);
x_183 = l_Lean_PrettyPrinter_Delaborator_isType2Type___lam__0(x_182, x_2, x_3, x_4, x_5, x_173);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_182);
return x_183;
}
case 7:
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; uint8_t x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_184 = lean_ctor_get(x_7, 1);
lean_inc(x_184);
lean_dec(x_7);
x_185 = lean_ctor_get(x_8, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_8, 2);
lean_inc(x_186);
x_187 = lean_ctor_get_uint8(x_8, sizeof(void*)*3 + 8);
lean_dec(x_8);
x_188 = lean_ctor_get(x_9, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_9, 1);
lean_inc(x_189);
x_190 = lean_ctor_get(x_9, 2);
lean_inc(x_190);
x_191 = lean_ctor_get_uint8(x_9, sizeof(void*)*3 + 8);
lean_dec(x_9);
x_192 = l_Lean_Expr_forallE___override(x_188, x_189, x_190, x_191);
x_193 = l_Lean_Expr_forallE___override(x_185, x_192, x_186, x_187);
x_194 = l_Lean_PrettyPrinter_Delaborator_isType2Type___lam__0(x_193, x_2, x_3, x_4, x_5, x_184);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_193);
return x_194;
}
case 8:
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; uint8_t x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; uint8_t x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_195 = lean_ctor_get(x_7, 1);
lean_inc(x_195);
lean_dec(x_7);
x_196 = lean_ctor_get(x_8, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_8, 2);
lean_inc(x_197);
x_198 = lean_ctor_get_uint8(x_8, sizeof(void*)*3 + 8);
lean_dec(x_8);
x_199 = lean_ctor_get(x_9, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_9, 1);
lean_inc(x_200);
x_201 = lean_ctor_get(x_9, 2);
lean_inc(x_201);
x_202 = lean_ctor_get(x_9, 3);
lean_inc(x_202);
x_203 = lean_ctor_get_uint8(x_9, sizeof(void*)*4 + 8);
lean_dec(x_9);
x_204 = l_Lean_Expr_letE___override(x_199, x_200, x_201, x_202, x_203);
x_205 = l_Lean_Expr_forallE___override(x_196, x_204, x_197, x_198);
x_206 = l_Lean_PrettyPrinter_Delaborator_isType2Type___lam__0(x_205, x_2, x_3, x_4, x_5, x_195);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_205);
return x_206;
}
case 9:
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; uint8_t x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_207 = lean_ctor_get(x_7, 1);
lean_inc(x_207);
lean_dec(x_7);
x_208 = lean_ctor_get(x_8, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_8, 2);
lean_inc(x_209);
x_210 = lean_ctor_get_uint8(x_8, sizeof(void*)*3 + 8);
lean_dec(x_8);
x_211 = lean_ctor_get(x_9, 0);
lean_inc(x_211);
lean_dec(x_9);
x_212 = l_Lean_Expr_lit___override(x_211);
x_213 = l_Lean_Expr_forallE___override(x_208, x_212, x_209, x_210);
x_214 = l_Lean_PrettyPrinter_Delaborator_isType2Type___lam__0(x_213, x_2, x_3, x_4, x_5, x_207);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_213);
return x_214;
}
case 10:
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; uint8_t x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_215 = lean_ctor_get(x_7, 1);
lean_inc(x_215);
lean_dec(x_7);
x_216 = lean_ctor_get(x_8, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_8, 2);
lean_inc(x_217);
x_218 = lean_ctor_get_uint8(x_8, sizeof(void*)*3 + 8);
lean_dec(x_8);
x_219 = lean_ctor_get(x_9, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_9, 1);
lean_inc(x_220);
lean_dec(x_9);
x_221 = l_Lean_Expr_mdata___override(x_219, x_220);
x_222 = l_Lean_Expr_forallE___override(x_216, x_221, x_217, x_218);
x_223 = l_Lean_PrettyPrinter_Delaborator_isType2Type___lam__0(x_222, x_2, x_3, x_4, x_5, x_215);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_222);
return x_223;
}
default: 
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; uint8_t x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_224 = lean_ctor_get(x_7, 1);
lean_inc(x_224);
lean_dec(x_7);
x_225 = lean_ctor_get(x_8, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_8, 2);
lean_inc(x_226);
x_227 = lean_ctor_get_uint8(x_8, sizeof(void*)*3 + 8);
lean_dec(x_8);
x_228 = lean_ctor_get(x_9, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_9, 1);
lean_inc(x_229);
x_230 = lean_ctor_get(x_9, 2);
lean_inc(x_230);
lean_dec(x_9);
x_231 = l_Lean_Expr_proj___override(x_228, x_229, x_230);
x_232 = l_Lean_Expr_forallE___override(x_225, x_231, x_226, x_227);
x_233 = l_Lean_PrettyPrinter_Delaborator_isType2Type___lam__0(x_232, x_2, x_3, x_4, x_5, x_224);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_232);
return x_233;
}
}
}
else
{
lean_object* x_234; lean_object* x_235; 
x_234 = lean_ctor_get(x_7, 1);
lean_inc(x_234);
lean_dec(x_7);
x_235 = l_Lean_PrettyPrinter_Delaborator_isType2Type___lam__0(x_8, x_2, x_3, x_4, x_5, x_234);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_8);
return x_235;
}
}
else
{
uint8_t x_236; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_236 = !lean_is_exclusive(x_7);
if (x_236 == 0)
{
return x_7;
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_237 = lean_ctor_get(x_7, 0);
x_238 = lean_ctor_get(x_7, 1);
lean_inc(x_238);
lean_inc(x_237);
lean_dec(x_7);
x_239 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_239, 0, x_237);
lean_ctor_set(x_239, 1, x_238);
return x_239;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_isType2Type___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Delaborator_isType2Type___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_isFOLike___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_Expr_getAppFn(x_1);
x_4 = l_Lean_Expr_isFVar(x_3);
if (x_4 == 0)
{
uint8_t x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Lean_Expr_isConst(x_3);
lean_dec(x_3);
x_6 = lean_box(x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_2);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
x_8 = lean_box(x_4);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_2);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_isFOLike(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Delaborator_isFOLike___redArg(x_1, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_isFOLike___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PrettyPrinter_Delaborator_isFOLike___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_isFOLike___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Delaborator_isFOLike(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lean_PrettyPrinter_Delaborator_isIdLike(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 6)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 2);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_box(1);
x_4 = lean_unbox(x_3);
return x_4;
}
else
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_box(0);
x_6 = lean_unbox(x_5);
return x_6;
}
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_box(0);
x_8 = lean_unbox(x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_isIdLike___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_PrettyPrinter_Delaborator_isIdLike(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_isStructureInstance(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
x_7 = l_Lean_Meta_isConstructorApp_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
lean_dec(x_5);
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_7, 0);
lean_dec(x_10);
x_11 = lean_box(0);
lean_ctor_set(x_7, 0, x_11);
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_7, 1);
lean_inc(x_15);
lean_dec(x_7);
x_16 = lean_ctor_get(x_8, 0);
lean_inc(x_16);
lean_dec(x_8);
x_17 = lean_st_ref_get(x_5, x_15);
lean_dec(x_5);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_dec(x_16);
x_22 = l_Lean_isStructure(x_20, x_21);
x_23 = lean_box(x_22);
lean_ctor_set(x_17, 0, x_23);
return x_17;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; 
x_24 = lean_ctor_get(x_17, 0);
x_25 = lean_ctor_get(x_17, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_17);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_ctor_get(x_16, 1);
lean_inc(x_27);
lean_dec(x_16);
x_28 = l_Lean_isStructure(x_26, x_27);
x_29 = lean_box(x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_25);
return x_30;
}
}
}
else
{
uint8_t x_31; 
lean_dec(x_5);
x_31 = !lean_is_exclusive(x_7);
if (x_31 == 0)
{
return x_7;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_7, 0);
x_33 = lean_ctor_get(x_7, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_7);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_isStructureInstance___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Delaborator_isStructureInstance(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_hasMVarAtCurrDepth___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc(x_1);
x_3 = l_Lean_MetavarContext_findDecl_x3f(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; uint8_t x_5; 
lean_dec(x_1);
x_4 = lean_box(0);
x_5 = lean_unbox(x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_ctor_get(x_6, 3);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_nat_dec_eq(x_7, x_8);
lean_dec(x_8);
lean_dec(x_7);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_hasMVarAtCurrDepth___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_hasMVarAtCurrDepth___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_8, 0, x_7);
x_9 = lean_box(0);
x_10 = l_Lean_FindMVar_main(x_8, x_1, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_box(0);
lean_ctor_set(x_4, 0, x_11);
return x_4;
}
else
{
lean_object* x_12; 
lean_dec(x_10);
x_12 = lean_box(1);
lean_ctor_set(x_4, 0, x_12);
return x_4;
}
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_4);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_hasMVarAtCurrDepth___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = lean_box(0);
x_18 = l_Lean_FindMVar_main(x_16, x_1, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_14);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_18);
x_21 = lean_box(1);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_14);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_hasMVarAtCurrDepth(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_hasMVarAtCurrDepth___redArg(x_1, x_3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_hasMVarAtCurrDepth___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_hasMVarAtCurrDepth___redArg___lam__0(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_hasMVarAtCurrDepth___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_hasMVarAtCurrDepth___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_hasMVarAtCurrDepth___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_hasMVarAtCurrDepth(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_hasLevelMVarAtCurrDepth___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
lean_inc(x_1);
x_3 = l_Lean_MetavarContext_findLevelDepth_x3f(x_1, x_2);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_____private_Lean_Meta_Basic_0__Lean_Meta_beqInfoCacheKey____x40_Lean_Meta_Basic___hyg_1324__spec__0(x_3, x_5);
lean_dec(x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_hasLevelMVarAtCurrDepth___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_hasLevelMVarAtCurrDepth___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_8, 0, x_7);
x_9 = lean_box(0);
x_10 = l_Lean_FindLevelMVar_main(x_8, x_1, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_box(0);
lean_ctor_set(x_4, 0, x_11);
return x_4;
}
else
{
lean_object* x_12; 
lean_dec(x_10);
x_12 = lean_box(1);
lean_ctor_set(x_4, 0, x_12);
return x_4;
}
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_4);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_hasLevelMVarAtCurrDepth___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = lean_box(0);
x_18 = l_Lean_FindLevelMVar_main(x_16, x_1, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_14);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_18);
x_21 = lean_box(1);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_14);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_hasLevelMVarAtCurrDepth(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_hasLevelMVarAtCurrDepth___redArg(x_1, x_3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_hasLevelMVarAtCurrDepth___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_hasLevelMVarAtCurrDepth___redArg___lam__0(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_hasLevelMVarAtCurrDepth___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_hasLevelMVarAtCurrDepth___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_hasLevelMVarAtCurrDepth___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_hasLevelMVarAtCurrDepth(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_0__Lean_PrettyPrinter_Delaborator_TopDownAnalyze_valUnknown___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_1, x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_hasMVarAtCurrDepth___redArg(x_5, x_2, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_0__Lean_PrettyPrinter_Delaborator_TopDownAnalyze_valUnknown(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_0__Lean_PrettyPrinter_Delaborator_TopDownAnalyze_valUnknown___redArg(x_1, x_3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_0__Lean_PrettyPrinter_Delaborator_TopDownAnalyze_valUnknown___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_0__Lean_PrettyPrinter_Delaborator_TopDownAnalyze_valUnknown___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_0__Lean_PrettyPrinter_Delaborator_TopDownAnalyze_valUnknown___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_0__Lean_PrettyPrinter_Delaborator_TopDownAnalyze_valUnknown(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_0__Lean_PrettyPrinter_Delaborator_TopDownAnalyze_typeUnknown(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_3);
x_7 = lean_infer_type(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l___private_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_0__Lean_PrettyPrinter_Delaborator_TopDownAnalyze_valUnknown___redArg(x_8, x_3, x_9);
lean_dec(x_3);
return x_10;
}
else
{
uint8_t x_11; 
lean_dec(x_3);
x_11 = !lean_is_exclusive(x_7);
if (x_11 == 0)
{
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_7, 0);
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_7);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = l_Lean_Expr_getAppFn(x_1);
x_7 = lean_array_uget(x_2, x_3);
x_8 = l_Lean_Expr_constName_x21(x_6);
lean_dec(x_6);
x_9 = lean_name_eq(x_7, x_8);
lean_dec(x_8);
lean_dec(x_7);
if (x_9 == 0)
{
lean_object* x_10; size_t x_11; size_t x_12; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_usize_of_nat(x_10);
x_12 = lean_usize_add(x_3, x_11);
x_3 = x_12;
goto _start;
}
else
{
return x_9;
}
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_box(0);
x_15 = lean_unbox(x_14);
return x_15;
}
}
}
LEAN_EXPORT uint8_t l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l_Lean_Expr_getAppNumArgs(x_1);
x_3 = lean_unsigned_to_nat(6u);
x_4 = lean_nat_dec_eq(x_2, x_3);
lean_dec(x_2);
if (x_4 == 0)
{
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_box(0);
x_6 = l_Lean_Expr_getAppFn(x_1);
x_7 = l_Lean_Expr_isConst(x_6);
lean_dec(x_6);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = lean_unbox(x_5);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_9 = lean_mk_string_unchecked("HOr", 3, 3);
x_10 = lean_mk_string_unchecked("hOr", 3, 3);
x_11 = l_Lean_Name_mkStr2(x_9, x_10);
x_12 = lean_mk_string_unchecked("HXor", 4, 4);
x_13 = lean_mk_string_unchecked("hXor", 4, 4);
x_14 = l_Lean_Name_mkStr2(x_12, x_13);
x_15 = lean_mk_string_unchecked("HAnd", 4, 4);
x_16 = lean_mk_string_unchecked("hAnd", 4, 4);
x_17 = l_Lean_Name_mkStr2(x_15, x_16);
x_18 = lean_mk_string_unchecked("HAppend", 7, 7);
x_19 = lean_mk_string_unchecked("hAppend", 7, 7);
x_20 = l_Lean_Name_mkStr2(x_18, x_19);
x_21 = lean_mk_string_unchecked("HOrElse", 7, 7);
x_22 = lean_mk_string_unchecked("hOrElse", 7, 7);
x_23 = l_Lean_Name_mkStr2(x_21, x_22);
x_24 = lean_mk_string_unchecked("HAndThen", 8, 8);
x_25 = lean_mk_string_unchecked("hAndThen", 8, 8);
x_26 = l_Lean_Name_mkStr2(x_24, x_25);
x_27 = lean_mk_string_unchecked("HAdd", 4, 4);
x_28 = lean_mk_string_unchecked("hAdd", 4, 4);
x_29 = l_Lean_Name_mkStr2(x_27, x_28);
x_30 = lean_mk_string_unchecked("HSub", 4, 4);
x_31 = lean_mk_string_unchecked("hSub", 4, 4);
x_32 = l_Lean_Name_mkStr2(x_30, x_31);
x_33 = lean_mk_string_unchecked("HMul", 4, 4);
x_34 = lean_mk_string_unchecked("hMul", 4, 4);
x_35 = l_Lean_Name_mkStr2(x_33, x_34);
x_36 = lean_mk_string_unchecked("HDiv", 4, 4);
x_37 = lean_mk_string_unchecked("hDiv", 4, 4);
x_38 = l_Lean_Name_mkStr2(x_36, x_37);
x_39 = lean_mk_string_unchecked("HMod", 4, 4);
x_40 = lean_mk_string_unchecked("hMod", 4, 4);
x_41 = l_Lean_Name_mkStr2(x_39, x_40);
x_42 = lean_mk_string_unchecked("HShiftLeft", 10, 10);
x_43 = lean_mk_string_unchecked("hShiftLeft", 10, 10);
x_44 = l_Lean_Name_mkStr2(x_42, x_43);
x_45 = lean_mk_string_unchecked("HShiftRight", 11, 11);
x_46 = l_Lean_Name_mkStr1(x_45);
x_47 = lean_unsigned_to_nat(13u);
x_48 = lean_mk_empty_array_with_capacity(x_47);
x_49 = lean_array_push(x_48, x_11);
x_50 = lean_array_push(x_49, x_14);
x_51 = lean_array_push(x_50, x_17);
x_52 = lean_array_push(x_51, x_20);
x_53 = lean_array_push(x_52, x_23);
x_54 = lean_array_push(x_53, x_26);
x_55 = lean_array_push(x_54, x_29);
x_56 = lean_array_push(x_55, x_32);
x_57 = lean_array_push(x_56, x_35);
x_58 = lean_array_push(x_57, x_38);
x_59 = lean_array_push(x_58, x_41);
x_60 = lean_array_push(x_59, x_44);
x_61 = lean_array_push(x_60, x_46);
x_62 = lean_unsigned_to_nat(0u);
x_63 = lean_array_get_size(x_61);
x_64 = lean_nat_dec_lt(x_62, x_63);
if (x_64 == 0)
{
uint8_t x_65; 
lean_dec(x_63);
lean_dec(x_61);
x_65 = lean_unbox(x_5);
return x_65;
}
else
{
if (x_64 == 0)
{
uint8_t x_66; 
lean_dec(x_63);
lean_dec(x_61);
x_66 = lean_unbox(x_5);
return x_66;
}
else
{
size_t x_67; size_t x_68; uint8_t x_69; 
x_67 = lean_usize_of_nat(x_62);
x_68 = lean_usize_of_nat(x_63);
lean_dec(x_63);
x_69 = l_Array_anyMUnsafe_any___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp_spec__0(x_1, x_61, x_67, x_68);
lean_dec(x_61);
return x_69;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp_spec__0(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_3, x_2);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_21; 
x_12 = l_Lean_Meta_mkFreshLevelMVar(x_5, x_6, x_7, x_8, x_9);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_21 = !lean_is_exclusive(x_4);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint64_t x_26; lean_object* x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; lean_object* x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; size_t x_35; size_t x_36; lean_object* x_37; size_t x_38; size_t x_39; size_t x_40; lean_object* x_41; uint8_t x_42; 
x_22 = lean_ctor_get(x_4, 0);
x_23 = lean_ctor_get(x_4, 1);
x_24 = lean_array_uget(x_1, x_3);
x_25 = lean_array_get_size(x_23);
x_26 = l_Lean_Name_hash___override(x_24);
x_27 = lean_unsigned_to_nat(32u);
x_28 = lean_uint64_of_nat(x_27);
x_29 = lean_uint64_shift_right(x_26, x_28);
x_30 = lean_uint64_xor(x_26, x_29);
x_31 = lean_unsigned_to_nat(16u);
x_32 = lean_uint64_of_nat(x_31);
x_33 = lean_uint64_shift_right(x_30, x_32);
x_34 = lean_uint64_xor(x_30, x_33);
x_35 = lean_uint64_to_usize(x_34);
x_36 = lean_usize_of_nat(x_25);
lean_dec(x_25);
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_usize_of_nat(x_37);
x_39 = lean_usize_sub(x_36, x_38);
x_40 = lean_usize_land(x_35, x_39);
x_41 = lean_array_uget(x_23, x_40);
x_42 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_NameHashSet_insert_spec__0___redArg(x_24, x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_43 = lean_nat_add(x_22, x_37);
lean_dec(x_22);
x_44 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_44, 0, x_24);
lean_ctor_set(x_44, 1, x_13);
lean_ctor_set(x_44, 2, x_41);
x_45 = lean_array_uset(x_23, x_40, x_44);
x_46 = lean_unsigned_to_nat(2u);
x_47 = lean_nat_shiftl(x_43, x_46);
x_48 = lean_unsigned_to_nat(3u);
x_49 = lean_nat_div(x_47, x_48);
lean_dec(x_47);
x_50 = lean_array_get_size(x_45);
x_51 = lean_nat_dec_le(x_49, x_50);
lean_dec(x_50);
lean_dec(x_49);
if (x_51 == 0)
{
lean_object* x_52; 
x_52 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_NameHashSet_insert_spec__1___redArg(x_45);
lean_ctor_set(x_4, 1, x_52);
lean_ctor_set(x_4, 0, x_43);
x_15 = x_4;
goto block_20;
}
else
{
lean_ctor_set(x_4, 1, x_45);
lean_ctor_set(x_4, 0, x_43);
x_15 = x_4;
goto block_20;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_box(0);
x_54 = lean_array_uset(x_23, x_40, x_53);
x_55 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0_spec__1___redArg(x_24, x_13, x_41);
x_56 = lean_array_uset(x_54, x_40, x_55);
lean_ctor_set(x_4, 1, x_56);
x_15 = x_4;
goto block_20;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint64_t x_61; lean_object* x_62; uint64_t x_63; uint64_t x_64; uint64_t x_65; lean_object* x_66; uint64_t x_67; uint64_t x_68; uint64_t x_69; size_t x_70; size_t x_71; lean_object* x_72; size_t x_73; size_t x_74; size_t x_75; lean_object* x_76; uint8_t x_77; 
x_57 = lean_ctor_get(x_4, 0);
x_58 = lean_ctor_get(x_4, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_4);
x_59 = lean_array_uget(x_1, x_3);
x_60 = lean_array_get_size(x_58);
x_61 = l_Lean_Name_hash___override(x_59);
x_62 = lean_unsigned_to_nat(32u);
x_63 = lean_uint64_of_nat(x_62);
x_64 = lean_uint64_shift_right(x_61, x_63);
x_65 = lean_uint64_xor(x_61, x_64);
x_66 = lean_unsigned_to_nat(16u);
x_67 = lean_uint64_of_nat(x_66);
x_68 = lean_uint64_shift_right(x_65, x_67);
x_69 = lean_uint64_xor(x_65, x_68);
x_70 = lean_uint64_to_usize(x_69);
x_71 = lean_usize_of_nat(x_60);
lean_dec(x_60);
x_72 = lean_unsigned_to_nat(1u);
x_73 = lean_usize_of_nat(x_72);
x_74 = lean_usize_sub(x_71, x_73);
x_75 = lean_usize_land(x_70, x_74);
x_76 = lean_array_uget(x_58, x_75);
x_77 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_NameHashSet_insert_spec__0___redArg(x_59, x_76);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_78 = lean_nat_add(x_57, x_72);
lean_dec(x_57);
x_79 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_79, 0, x_59);
lean_ctor_set(x_79, 1, x_13);
lean_ctor_set(x_79, 2, x_76);
x_80 = lean_array_uset(x_58, x_75, x_79);
x_81 = lean_unsigned_to_nat(2u);
x_82 = lean_nat_shiftl(x_78, x_81);
x_83 = lean_unsigned_to_nat(3u);
x_84 = lean_nat_div(x_82, x_83);
lean_dec(x_82);
x_85 = lean_array_get_size(x_80);
x_86 = lean_nat_dec_le(x_84, x_85);
lean_dec(x_85);
lean_dec(x_84);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; 
x_87 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_NameHashSet_insert_spec__1___redArg(x_80);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_78);
lean_ctor_set(x_88, 1, x_87);
x_15 = x_88;
goto block_20;
}
else
{
lean_object* x_89; 
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_78);
lean_ctor_set(x_89, 1, x_80);
x_15 = x_89;
goto block_20;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_90 = lean_box(0);
x_91 = lean_array_uset(x_58, x_75, x_90);
x_92 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0_spec__1___redArg(x_59, x_13, x_76);
x_93 = lean_array_uset(x_91, x_75, x_92);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_57);
lean_ctor_set(x_94, 1, x_93);
x_15 = x_94;
goto block_20;
}
}
block_20:
{
lean_object* x_16; size_t x_17; size_t x_18; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_usize_of_nat(x_16);
x_18 = lean_usize_add(x_3, x_17);
x_3 = x_18;
x_4 = x_15;
x_9 = x_14;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___lam__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_30; 
x_30 = l_Lean_Level_hasParam(x_4);
if (x_30 == 0)
{
if (x_3 == 0)
{
goto block_29;
}
else
{
lean_object* x_31; 
lean_inc(x_4);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_4);
x_5 = x_31;
goto block_27;
}
}
else
{
goto block_29;
}
block_27:
{
if (lean_obj_tag(x_4) == 4)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; lean_object* x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; lean_object* x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; size_t x_18; size_t x_19; lean_object* x_20; size_t x_21; size_t x_22; size_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_5);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_array_get_size(x_7);
x_9 = l_Lean_Name_hash___override(x_6);
x_10 = lean_unsigned_to_nat(32u);
x_11 = lean_uint64_of_nat(x_10);
x_12 = lean_uint64_shift_right(x_9, x_11);
x_13 = lean_uint64_xor(x_9, x_12);
x_14 = lean_unsigned_to_nat(16u);
x_15 = lean_uint64_of_nat(x_14);
x_16 = lean_uint64_shift_right(x_13, x_15);
x_17 = lean_uint64_xor(x_13, x_16);
x_18 = lean_uint64_to_usize(x_17);
x_19 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_usize_of_nat(x_20);
x_22 = lean_usize_sub(x_19, x_21);
x_23 = lean_usize_land(x_18, x_22);
x_24 = lean_array_uget(x_7, x_23);
x_25 = l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_throwAlreadyImported_spec__0___redArg(x_2, x_6, x_24);
lean_dec(x_24);
lean_dec(x_6);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
else
{
lean_dec(x_4);
lean_dec(x_2);
return x_5;
}
}
block_29:
{
lean_object* x_28; 
x_28 = lean_box(0);
x_5 = x_28;
goto block_27;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = l_Lean_Expr_hasLevelParam(x_1);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; size_t x_29; size_t x_30; lean_object* x_31; uint8_t x_32; 
x_9 = lean_unsigned_to_nat(8u);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_unsigned_to_nat(2u);
x_12 = lean_nat_shiftl(x_9, x_11);
x_13 = lean_unsigned_to_nat(3u);
x_14 = lean_nat_div(x_12, x_13);
lean_dec(x_12);
x_15 = l_Nat_nextPowerOfTwo(x_14);
lean_dec(x_14);
x_16 = lean_box(0);
lean_inc(x_15);
x_17 = lean_mk_array(x_15, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_10);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_box(0);
lean_inc(x_15);
x_20 = lean_mk_array(x_15, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_10);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_mk_empty_array_with_capacity(x_10);
x_23 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_23, 0, x_18);
lean_ctor_set(x_23, 1, x_21);
lean_ctor_set(x_23, 2, x_22);
lean_inc(x_1);
x_24 = l_Lean_CollectLevelParams_main(x_1, x_23);
x_25 = lean_ctor_get(x_24, 2);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_box(0);
x_27 = lean_mk_array(x_15, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_10);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_array_size(x_25);
x_30 = lean_usize_of_nat(x_10);
x_31 = l_Array_forIn_x27Unsafe_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars_spec__0(x_25, x_29, x_30, x_28, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_25);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = l_Lean_instInhabitedLevel;
x_35 = lean_box(x_7);
x_36 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___lam__0___boxed), 4, 3);
lean_closure_set(x_36, 0, x_33);
lean_closure_set(x_36, 1, x_34);
lean_closure_set(x_36, 2, x_35);
x_37 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(x_36, x_1);
lean_ctor_set(x_31, 0, x_37);
return x_31;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_38 = lean_ctor_get(x_31, 0);
x_39 = lean_ctor_get(x_31, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_31);
x_40 = l_Lean_instInhabitedLevel;
x_41 = lean_box(x_7);
x_42 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___lam__0___boxed), 4, 3);
lean_closure_set(x_42, 0, x_38);
lean_closure_set(x_42, 1, x_40);
lean_closure_set(x_42, 2, x_41);
x_43 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(x_42, x_1);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_39);
return x_44;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_forIn_x27Unsafe_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars_spec__0(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_3);
lean_dec(x_3);
x_6 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___lam__0(x_1, x_2, x_5, x_4);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isDefEqAssigning(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; lean_object* x_27; uint8_t x_28; uint64_t x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_ctor_get_uint8(x_8, 0);
x_10 = lean_ctor_get_uint8(x_8, 1);
x_11 = lean_ctor_get_uint8(x_8, 2);
x_12 = lean_ctor_get_uint8(x_8, 3);
x_13 = lean_ctor_get_uint8(x_8, 4);
x_14 = lean_ctor_get_uint8(x_8, 5);
x_15 = lean_ctor_get_uint8(x_8, 6);
x_16 = lean_box(1);
x_17 = lean_ctor_get_uint8(x_8, 8);
x_18 = lean_ctor_get_uint8(x_8, 9);
x_19 = lean_ctor_get_uint8(x_8, 10);
x_20 = lean_ctor_get_uint8(x_8, 11);
x_21 = lean_ctor_get_uint8(x_8, 12);
x_22 = lean_ctor_get_uint8(x_8, 13);
x_23 = lean_ctor_get_uint8(x_8, 14);
x_24 = lean_ctor_get_uint8(x_8, 15);
x_25 = lean_ctor_get_uint8(x_8, 16);
x_26 = lean_ctor_get_uint8(x_8, 17);
x_27 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_27, 0, x_9);
lean_ctor_set_uint8(x_27, 1, x_10);
lean_ctor_set_uint8(x_27, 2, x_11);
lean_ctor_set_uint8(x_27, 3, x_12);
lean_ctor_set_uint8(x_27, 4, x_13);
lean_ctor_set_uint8(x_27, 5, x_14);
lean_ctor_set_uint8(x_27, 6, x_15);
x_28 = lean_unbox(x_16);
lean_ctor_set_uint8(x_27, 7, x_28);
lean_ctor_set_uint8(x_27, 8, x_17);
lean_ctor_set_uint8(x_27, 9, x_18);
lean_ctor_set_uint8(x_27, 10, x_19);
lean_ctor_set_uint8(x_27, 11, x_20);
lean_ctor_set_uint8(x_27, 12, x_21);
lean_ctor_set_uint8(x_27, 13, x_22);
lean_ctor_set_uint8(x_27, 14, x_23);
lean_ctor_set_uint8(x_27, 15, x_24);
lean_ctor_set_uint8(x_27, 16, x_25);
lean_ctor_set_uint8(x_27, 17, x_26);
x_29 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_27);
x_30 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 8);
x_31 = lean_ctor_get(x_3, 1);
x_32 = lean_ctor_get(x_3, 2);
x_33 = lean_ctor_get(x_3, 3);
x_34 = lean_ctor_get(x_3, 4);
x_35 = lean_ctor_get(x_3, 5);
x_36 = lean_ctor_get(x_3, 6);
x_37 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 9);
x_38 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 10);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
x_39 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_39, 0, x_27);
lean_ctor_set(x_39, 1, x_31);
lean_ctor_set(x_39, 2, x_32);
lean_ctor_set(x_39, 3, x_33);
lean_ctor_set(x_39, 4, x_34);
lean_ctor_set(x_39, 5, x_35);
lean_ctor_set(x_39, 6, x_36);
lean_ctor_set_uint64(x_39, sizeof(void*)*7, x_29);
lean_ctor_set_uint8(x_39, sizeof(void*)*7 + 8, x_30);
lean_ctor_set_uint8(x_39, sizeof(void*)*7 + 9, x_37);
lean_ctor_set_uint8(x_39, sizeof(void*)*7 + 10, x_38);
x_40 = l_Lean_Meta_isExprDefEq(x_1, x_2, x_39, x_4, x_5, x_6, x_7);
lean_dec(x_39);
return x_40;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isDefEqAssigning___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isDefEqAssigning(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkpointDefEq___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_checkpointDefEq_spec__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_23; lean_object* x_24; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_9 = l_Lean_Meta_saveState___redArg(x_5, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_12 = x_9;
} else {
 lean_dec_ref(x_9);
 x_12 = lean_box(0);
}
x_28 = lean_st_ref_take(x_5, x_11);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = !lean_is_exclusive(x_29);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_29, 1);
lean_dec(x_33);
x_34 = !lean_is_exclusive(x_30);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_35 = lean_ctor_get(x_30, 4);
lean_dec(x_35);
x_36 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_30, 4, x_37);
x_38 = lean_st_ref_set(x_5, x_29, x_31);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
x_40 = l_Lean_Meta_getResetPostponed(x_4, x_5, x_6, x_7, x_39);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_43 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isDefEqAssigning(x_1, x_2, x_4, x_5, x_6, x_7, x_42);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_unbox(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; 
lean_dec(x_41);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_4);
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_dec(x_43);
x_47 = l_Lean_Meta_SavedState_restore___redArg(x_10, x_5, x_7, x_46);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_10);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_47, 0);
lean_dec(x_49);
lean_ctor_set(x_47, 0, x_44);
return x_47;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
lean_dec(x_47);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_44);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
else
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; 
lean_dec(x_44);
x_52 = lean_ctor_get(x_43, 1);
lean_inc(x_52);
lean_dec(x_43);
x_53 = lean_box(0);
x_54 = lean_unbox(x_53);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_55 = l_Lean_Meta_processPostponed(x_3, x_54, x_4, x_5, x_6, x_7, x_52);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; uint8_t x_57; 
lean_dec(x_12);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_unbox(x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; 
lean_dec(x_56);
lean_dec(x_41);
lean_dec(x_6);
lean_dec(x_4);
x_58 = lean_ctor_get(x_55, 1);
lean_inc(x_58);
lean_dec(x_55);
x_59 = l_Lean_Meta_SavedState_restore___redArg(x_10, x_5, x_7, x_58);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_10);
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_59, 0);
lean_dec(x_61);
lean_ctor_set(x_59, 0, x_53);
return x_59;
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_59, 1);
lean_inc(x_62);
lean_dec(x_59);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_53);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
lean_dec(x_10);
x_64 = lean_ctor_get(x_55, 1);
lean_inc(x_64);
lean_dec(x_55);
x_65 = l_Lean_Meta_getPostponed___redArg(x_5, x_64);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = l_Lean_PersistentArray_append___redArg(x_41, x_66);
lean_dec(x_66);
x_69 = l_Lean_Meta_setPostponed(x_68, x_4, x_5, x_6, x_7, x_67);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_70 = !lean_is_exclusive(x_69);
if (x_70 == 0)
{
lean_object* x_71; 
x_71 = lean_ctor_get(x_69, 0);
lean_dec(x_71);
lean_ctor_set(x_69, 0, x_56);
return x_69;
}
else
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_69, 1);
lean_inc(x_72);
lean_dec(x_69);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_56);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
else
{
lean_object* x_74; lean_object* x_75; 
lean_dec(x_41);
lean_dec(x_6);
lean_dec(x_4);
x_74 = lean_ctor_get(x_55, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_55, 1);
lean_inc(x_75);
lean_dec(x_55);
x_23 = x_74;
x_24 = x_75;
goto block_27;
}
}
}
else
{
lean_object* x_76; lean_object* x_77; 
lean_dec(x_41);
lean_dec(x_6);
lean_dec(x_4);
x_76 = lean_ctor_get(x_43, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_43, 1);
lean_inc(x_77);
lean_dec(x_43);
x_23 = x_76;
x_24 = x_77;
goto block_27;
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_78 = lean_ctor_get(x_30, 0);
x_79 = lean_ctor_get(x_30, 1);
x_80 = lean_ctor_get(x_30, 2);
x_81 = lean_ctor_get(x_30, 3);
x_82 = lean_ctor_get(x_30, 5);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_30);
x_83 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_84 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_84, 0, x_83);
x_85 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_85, 0, x_78);
lean_ctor_set(x_85, 1, x_79);
lean_ctor_set(x_85, 2, x_80);
lean_ctor_set(x_85, 3, x_81);
lean_ctor_set(x_85, 4, x_84);
lean_ctor_set(x_85, 5, x_82);
lean_ctor_set(x_29, 1, x_85);
x_86 = lean_st_ref_set(x_5, x_29, x_31);
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
lean_dec(x_86);
x_88 = l_Lean_Meta_getResetPostponed(x_4, x_5, x_6, x_7, x_87);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_91 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isDefEqAssigning(x_1, x_2, x_4, x_5, x_6, x_7, x_90);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; uint8_t x_93; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_unbox(x_92);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_89);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_4);
x_94 = lean_ctor_get(x_91, 1);
lean_inc(x_94);
lean_dec(x_91);
x_95 = l_Lean_Meta_SavedState_restore___redArg(x_10, x_5, x_7, x_94);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_10);
x_96 = lean_ctor_get(x_95, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_97 = x_95;
} else {
 lean_dec_ref(x_95);
 x_97 = lean_box(0);
}
if (lean_is_scalar(x_97)) {
 x_98 = lean_alloc_ctor(0, 2, 0);
} else {
 x_98 = x_97;
}
lean_ctor_set(x_98, 0, x_92);
lean_ctor_set(x_98, 1, x_96);
return x_98;
}
else
{
lean_object* x_99; lean_object* x_100; uint8_t x_101; lean_object* x_102; 
lean_dec(x_92);
x_99 = lean_ctor_get(x_91, 1);
lean_inc(x_99);
lean_dec(x_91);
x_100 = lean_box(0);
x_101 = lean_unbox(x_100);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_102 = l_Lean_Meta_processPostponed(x_3, x_101, x_4, x_5, x_6, x_7, x_99);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; uint8_t x_104; 
lean_dec(x_12);
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_unbox(x_103);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_103);
lean_dec(x_89);
lean_dec(x_6);
lean_dec(x_4);
x_105 = lean_ctor_get(x_102, 1);
lean_inc(x_105);
lean_dec(x_102);
x_106 = l_Lean_Meta_SavedState_restore___redArg(x_10, x_5, x_7, x_105);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_10);
x_107 = lean_ctor_get(x_106, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_108 = x_106;
} else {
 lean_dec_ref(x_106);
 x_108 = lean_box(0);
}
if (lean_is_scalar(x_108)) {
 x_109 = lean_alloc_ctor(0, 2, 0);
} else {
 x_109 = x_108;
}
lean_ctor_set(x_109, 0, x_100);
lean_ctor_set(x_109, 1, x_107);
return x_109;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_dec(x_10);
x_110 = lean_ctor_get(x_102, 1);
lean_inc(x_110);
lean_dec(x_102);
x_111 = l_Lean_Meta_getPostponed___redArg(x_5, x_110);
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec(x_111);
x_114 = l_Lean_PersistentArray_append___redArg(x_89, x_112);
lean_dec(x_112);
x_115 = l_Lean_Meta_setPostponed(x_114, x_4, x_5, x_6, x_7, x_113);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_116 = lean_ctor_get(x_115, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_117 = x_115;
} else {
 lean_dec_ref(x_115);
 x_117 = lean_box(0);
}
if (lean_is_scalar(x_117)) {
 x_118 = lean_alloc_ctor(0, 2, 0);
} else {
 x_118 = x_117;
}
lean_ctor_set(x_118, 0, x_103);
lean_ctor_set(x_118, 1, x_116);
return x_118;
}
}
else
{
lean_object* x_119; lean_object* x_120; 
lean_dec(x_89);
lean_dec(x_6);
lean_dec(x_4);
x_119 = lean_ctor_get(x_102, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_102, 1);
lean_inc(x_120);
lean_dec(x_102);
x_23 = x_119;
x_24 = x_120;
goto block_27;
}
}
}
else
{
lean_object* x_121; lean_object* x_122; 
lean_dec(x_89);
lean_dec(x_6);
lean_dec(x_4);
x_121 = lean_ctor_get(x_91, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_91, 1);
lean_inc(x_122);
lean_dec(x_91);
x_23 = x_121;
x_24 = x_122;
goto block_27;
}
}
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_123 = lean_ctor_get(x_29, 0);
x_124 = lean_ctor_get(x_29, 2);
x_125 = lean_ctor_get(x_29, 3);
x_126 = lean_ctor_get(x_29, 4);
lean_inc(x_126);
lean_inc(x_125);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_29);
x_127 = lean_ctor_get(x_30, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_30, 1);
lean_inc(x_128);
x_129 = lean_ctor_get(x_30, 2);
lean_inc(x_129);
x_130 = lean_ctor_get(x_30, 3);
lean_inc(x_130);
x_131 = lean_ctor_get(x_30, 5);
lean_inc(x_131);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 lean_ctor_release(x_30, 2);
 lean_ctor_release(x_30, 3);
 lean_ctor_release(x_30, 4);
 lean_ctor_release(x_30, 5);
 x_132 = x_30;
} else {
 lean_dec_ref(x_30);
 x_132 = lean_box(0);
}
x_133 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_134 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_134, 0, x_133);
if (lean_is_scalar(x_132)) {
 x_135 = lean_alloc_ctor(0, 6, 0);
} else {
 x_135 = x_132;
}
lean_ctor_set(x_135, 0, x_127);
lean_ctor_set(x_135, 1, x_128);
lean_ctor_set(x_135, 2, x_129);
lean_ctor_set(x_135, 3, x_130);
lean_ctor_set(x_135, 4, x_134);
lean_ctor_set(x_135, 5, x_131);
x_136 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_136, 0, x_123);
lean_ctor_set(x_136, 1, x_135);
lean_ctor_set(x_136, 2, x_124);
lean_ctor_set(x_136, 3, x_125);
lean_ctor_set(x_136, 4, x_126);
x_137 = lean_st_ref_set(x_5, x_136, x_31);
x_138 = lean_ctor_get(x_137, 1);
lean_inc(x_138);
lean_dec(x_137);
x_139 = l_Lean_Meta_getResetPostponed(x_4, x_5, x_6, x_7, x_138);
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_139, 1);
lean_inc(x_141);
lean_dec(x_139);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_142 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isDefEqAssigning(x_1, x_2, x_4, x_5, x_6, x_7, x_141);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; uint8_t x_144; 
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_unbox(x_143);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
lean_dec(x_140);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_4);
x_145 = lean_ctor_get(x_142, 1);
lean_inc(x_145);
lean_dec(x_142);
x_146 = l_Lean_Meta_SavedState_restore___redArg(x_10, x_5, x_7, x_145);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_10);
x_147 = lean_ctor_get(x_146, 1);
lean_inc(x_147);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 x_148 = x_146;
} else {
 lean_dec_ref(x_146);
 x_148 = lean_box(0);
}
if (lean_is_scalar(x_148)) {
 x_149 = lean_alloc_ctor(0, 2, 0);
} else {
 x_149 = x_148;
}
lean_ctor_set(x_149, 0, x_143);
lean_ctor_set(x_149, 1, x_147);
return x_149;
}
else
{
lean_object* x_150; lean_object* x_151; uint8_t x_152; lean_object* x_153; 
lean_dec(x_143);
x_150 = lean_ctor_get(x_142, 1);
lean_inc(x_150);
lean_dec(x_142);
x_151 = lean_box(0);
x_152 = lean_unbox(x_151);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_153 = l_Lean_Meta_processPostponed(x_3, x_152, x_4, x_5, x_6, x_7, x_150);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; uint8_t x_155; 
lean_dec(x_12);
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_unbox(x_154);
if (x_155 == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_154);
lean_dec(x_140);
lean_dec(x_6);
lean_dec(x_4);
x_156 = lean_ctor_get(x_153, 1);
lean_inc(x_156);
lean_dec(x_153);
x_157 = l_Lean_Meta_SavedState_restore___redArg(x_10, x_5, x_7, x_156);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_10);
x_158 = lean_ctor_get(x_157, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_157)) {
 lean_ctor_release(x_157, 0);
 lean_ctor_release(x_157, 1);
 x_159 = x_157;
} else {
 lean_dec_ref(x_157);
 x_159 = lean_box(0);
}
if (lean_is_scalar(x_159)) {
 x_160 = lean_alloc_ctor(0, 2, 0);
} else {
 x_160 = x_159;
}
lean_ctor_set(x_160, 0, x_151);
lean_ctor_set(x_160, 1, x_158);
return x_160;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
lean_dec(x_10);
x_161 = lean_ctor_get(x_153, 1);
lean_inc(x_161);
lean_dec(x_153);
x_162 = l_Lean_Meta_getPostponed___redArg(x_5, x_161);
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_162, 1);
lean_inc(x_164);
lean_dec(x_162);
x_165 = l_Lean_PersistentArray_append___redArg(x_140, x_163);
lean_dec(x_163);
x_166 = l_Lean_Meta_setPostponed(x_165, x_4, x_5, x_6, x_7, x_164);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_167 = lean_ctor_get(x_166, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 lean_ctor_release(x_166, 1);
 x_168 = x_166;
} else {
 lean_dec_ref(x_166);
 x_168 = lean_box(0);
}
if (lean_is_scalar(x_168)) {
 x_169 = lean_alloc_ctor(0, 2, 0);
} else {
 x_169 = x_168;
}
lean_ctor_set(x_169, 0, x_154);
lean_ctor_set(x_169, 1, x_167);
return x_169;
}
}
else
{
lean_object* x_170; lean_object* x_171; 
lean_dec(x_140);
lean_dec(x_6);
lean_dec(x_4);
x_170 = lean_ctor_get(x_153, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_153, 1);
lean_inc(x_171);
lean_dec(x_153);
x_23 = x_170;
x_24 = x_171;
goto block_27;
}
}
}
else
{
lean_object* x_172; lean_object* x_173; 
lean_dec(x_140);
lean_dec(x_6);
lean_dec(x_4);
x_172 = lean_ctor_get(x_142, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_142, 1);
lean_inc(x_173);
lean_dec(x_142);
x_23 = x_172;
x_24 = x_173;
goto block_27;
}
}
block_22:
{
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
lean_dec(x_12);
x_16 = l_Lean_Meta_SavedState_restore___redArg(x_10, x_5, x_7, x_14);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_10);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 0, x_13);
return x_16;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_13);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
lean_object* x_21; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_5);
if (lean_is_scalar(x_12)) {
 x_21 = lean_alloc_ctor(1, 2, 0);
} else {
 x_21 = x_12;
 lean_ctor_set_tag(x_21, 1);
}
lean_ctor_set(x_21, 0, x_13);
lean_ctor_set(x_21, 1, x_14);
return x_21;
}
}
block_27:
{
uint8_t x_25; 
x_25 = l_Lean_Exception_isInterrupt(x_23);
if (x_25 == 0)
{
uint8_t x_26; 
x_26 = l_Lean_Exception_isRuntime(x_23);
x_13 = x_23;
x_14 = x_24;
x_15 = x_26;
goto block_22;
}
else
{
x_13 = x_23;
x_14 = x_24;
x_15 = x_25;
goto block_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_checkpointDefEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_box(0);
x_9 = lean_unbox(x_8);
x_10 = l_Lean_Meta_checkpointDefEq___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_checkpointDefEq_spec__0(x_1, x_2, x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkpointDefEq___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_checkpointDefEq_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lean_Meta_checkpointDefEq___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_checkpointDefEq_spec__0(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHigherOrder___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_get_size(x_1);
x_10 = lean_nat_dec_lt(x_8, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_7);
return x_12;
}
else
{
uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_13 = l_Lean_Expr_isSort(x_2);
x_14 = lean_box(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_7);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHigherOrder(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_7 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHigherOrder___lam__0___boxed), 7, 0);
x_8 = lean_box(0);
x_9 = lean_unbox(x_8);
x_10 = l_Lean_Meta_forallTelescopeReducing___at___Lean_Meta_getParamNames_spec__1(lean_box(0), x_1, x_7, x_9, x_2, x_3, x_4, x_5, x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHigherOrder___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHigherOrder___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isFunLike___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_get_size(x_1);
x_10 = lean_nat_dec_lt(x_8, x_9);
lean_dec(x_9);
x_11 = lean_box(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_7);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isFunLike(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_7 = lean_infer_type(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isFunLike___lam__0___boxed), 7, 0);
x_11 = lean_box(0);
x_12 = lean_unbox(x_11);
x_13 = l_Lean_Meta_forallTelescopeReducing___at___Lean_Meta_getParamNames_spec__1(lean_box(0), x_8, x_10, x_12, x_2, x_3, x_4, x_5, x_9);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_14 = !lean_is_exclusive(x_7);
if (x_14 == 0)
{
return x_7;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_7, 0);
x_16 = lean_ctor_get(x_7, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_7);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isFunLike___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isFunLike___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT uint8_t l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isSubstLike(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_2 = lean_mk_string_unchecked("Eq", 2, 2);
x_3 = lean_mk_string_unchecked("ndrec", 5, 5);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_unsigned_to_nat(6u);
x_6 = l_Lean_Expr_isAppOfArity(x_1, x_4, x_5);
lean_dec(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_mk_string_unchecked("rec", 3, 3);
x_8 = l_Lean_Name_mkStr2(x_2, x_7);
x_9 = l_Lean_Expr_isAppOfArity(x_1, x_8, x_5);
lean_dec(x_8);
return x_9;
}
else
{
lean_dec(x_2);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isSubstLike___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isSubstLike(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_nameNotRoundtrippable_containsNum(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
case 1:
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 0);
x_1 = x_4;
goto _start;
}
default: 
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_box(1);
x_7 = lean_unbox(x_6);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_nameNotRoundtrippable_containsNum___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_nameNotRoundtrippable_containsNum(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_nameNotRoundtrippable(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_5; 
x_5 = l_Lean_Name_hasMacroScopes(x_1);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = l_Lean_isPrivateName(x_1);
x_2 = x_6;
goto block_4;
}
else
{
x_2 = x_5;
goto block_4;
}
block_4:
{
if (x_2 == 0)
{
uint8_t x_3; 
x_3 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_nameNotRoundtrippable_containsNum(x_1);
return x_3;
}
else
{
return x_2;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_nameNotRoundtrippable___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_nameNotRoundtrippable(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_mvarName(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Expr_mvarId_x21(x_1);
x_8 = l_Lean_MVarId_getDecl(x_7, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_8);
if (x_16 == 0)
{
return x_8;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_8, 0);
x_18 = lean_ctor_get(x_8, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_8);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_mvarName___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_mvarName(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_containsBadMax___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_7; 
x_7 = l_Lean_Level_hasParam(x_1);
if (x_7 == 0)
{
x_3 = x_7;
goto block_6;
}
else
{
uint8_t x_8; 
x_8 = l_Lean_Level_hasParam(x_2);
x_3 = x_8;
goto block_6;
}
block_6:
{
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_containsBadMax(x_1);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_containsBadMax(x_2);
return x_5;
}
else
{
return x_4;
}
}
else
{
return x_3;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_containsBadMax(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
x_1 = x_2;
goto _start;
}
case 2:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_containsBadMax___lam__0(x_4, x_5);
return x_6;
}
case 3:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
x_9 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_containsBadMax___lam__0(x_7, x_8);
return x_9;
}
default: 
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_box(0);
x_11 = lean_unbox(x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_containsBadMax___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_containsBadMax___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_containsBadMax___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_containsBadMax(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_instInhabitedContext() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; 
x_1 = lean_box(0);
x_2 = lean_mk_string_unchecked("_inhabitedExprDummy", 19, 19);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_box(0);
x_5 = l_Lean_Expr_const___override(x_3, x_4);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_unbox(x_1);
lean_ctor_set_uint8(x_8, sizeof(void*)*1, x_9);
x_10 = lean_unbox(x_1);
lean_ctor_set_uint8(x_8, sizeof(void*)*1 + 1, x_10);
x_11 = lean_unbox(x_1);
lean_ctor_set_uint8(x_8, sizeof(void*)*1 + 2, x_11);
x_12 = lean_unbox(x_1);
lean_ctor_set_uint8(x_8, sizeof(void*)*1 + 3, x_12);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_instMonadReaderOfSubExprAnalyzeM___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_instMonadReaderOfSubExprAnalyzeM() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_instMonadReaderOfSubExprAnalyzeM___lam__0___boxed), 7, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_instMonadReaderOfSubExprAnalyzeM___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_instMonadReaderOfSubExprAnalyzeM___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_instMonadWithReaderOfSubExprAnalyzeM___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
x_12 = lean_ctor_get_uint8(x_4, sizeof(void*)*1 + 1);
x_13 = lean_ctor_get_uint8(x_4, sizeof(void*)*1 + 2);
x_14 = lean_ctor_get_uint8(x_4, sizeof(void*)*1 + 3);
x_15 = lean_ctor_get(x_4, 0);
lean_inc(x_15);
lean_dec(x_4);
x_16 = lean_apply_1(x_2, x_15);
x_17 = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set_uint8(x_17, sizeof(void*)*1, x_11);
lean_ctor_set_uint8(x_17, sizeof(void*)*1 + 1, x_12);
lean_ctor_set_uint8(x_17, sizeof(void*)*1 + 2, x_13);
lean_ctor_set_uint8(x_17, sizeof(void*)*1 + 3, x_14);
x_18 = lean_apply_7(x_3, x_17, x_5, x_6, x_7, x_8, x_9, x_10);
return x_18;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_instMonadWithReaderOfSubExprAnalyzeM() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_instMonadWithReaderOfSubExprAnalyzeM___lam__0), 10, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_tryUnify___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_tryUnify(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_42; lean_object* x_43; lean_object* x_47; lean_object* x_49; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_2);
lean_inc(x_1);
x_49 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isDefEqAssigning(x_1, x_2, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; uint8_t x_51; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_unbox(x_50);
lean_dec(x_50);
if (x_51 == 0)
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_49);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_53 = lean_ctor_get(x_49, 1);
x_54 = lean_ctor_get(x_49, 0);
lean_dec(x_54);
x_55 = lean_st_ref_take(x_4, x_53);
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_57 = lean_ctor_get(x_55, 0);
x_58 = lean_ctor_get(x_55, 1);
x_59 = lean_ctor_get(x_57, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
lean_dec(x_57);
lean_ctor_set(x_55, 1, x_2);
lean_ctor_set(x_55, 0, x_1);
x_61 = lean_array_push(x_60, x_55);
lean_ctor_set(x_49, 1, x_61);
lean_ctor_set(x_49, 0, x_59);
x_62 = lean_st_ref_set(x_4, x_49, x_58);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
lean_dec(x_62);
x_64 = lean_box(0);
x_65 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_tryUnify___lam__0(x_64, x_3, x_4, x_5, x_6, x_7, x_8, x_63);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_47 = x_65;
goto block_48;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_66 = lean_ctor_get(x_55, 0);
x_67 = lean_ctor_get(x_55, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_55);
x_68 = lean_ctor_get(x_66, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_66, 1);
lean_inc(x_69);
lean_dec(x_66);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_1);
lean_ctor_set(x_70, 1, x_2);
x_71 = lean_array_push(x_69, x_70);
lean_ctor_set(x_49, 1, x_71);
lean_ctor_set(x_49, 0, x_68);
x_72 = lean_st_ref_set(x_4, x_49, x_67);
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec(x_72);
x_74 = lean_box(0);
x_75 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_tryUnify___lam__0(x_74, x_3, x_4, x_5, x_6, x_7, x_8, x_73);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_47 = x_75;
goto block_48;
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_76 = lean_ctor_get(x_49, 1);
lean_inc(x_76);
lean_dec(x_49);
x_77 = lean_st_ref_take(x_4, x_76);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_80 = x_77;
} else {
 lean_dec_ref(x_77);
 x_80 = lean_box(0);
}
x_81 = lean_ctor_get(x_78, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_78, 1);
lean_inc(x_82);
lean_dec(x_78);
if (lean_is_scalar(x_80)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_80;
}
lean_ctor_set(x_83, 0, x_1);
lean_ctor_set(x_83, 1, x_2);
x_84 = lean_array_push(x_82, x_83);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_81);
lean_ctor_set(x_85, 1, x_84);
x_86 = lean_st_ref_set(x_4, x_85, x_79);
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
lean_dec(x_86);
x_88 = lean_box(0);
x_89 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_tryUnify___lam__0(x_88, x_3, x_4, x_5, x_6, x_7, x_8, x_87);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_47 = x_89;
goto block_48;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_2);
lean_dec(x_1);
x_90 = lean_ctor_get(x_49, 1);
lean_inc(x_90);
lean_dec(x_49);
x_91 = lean_box(0);
x_92 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_tryUnify___lam__0(x_91, x_3, x_4, x_5, x_6, x_7, x_8, x_90);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_47 = x_92;
goto block_48;
}
}
else
{
lean_object* x_93; lean_object* x_94; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_93 = lean_ctor_get(x_49, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_49, 1);
lean_inc(x_94);
lean_dec(x_49);
x_42 = x_93;
x_43 = x_94;
goto block_46;
}
block_41:
{
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
lean_dec(x_11);
x_13 = lean_st_ref_take(x_4, x_10);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
lean_ctor_set(x_13, 1, x_2);
lean_ctor_set(x_13, 0, x_1);
x_19 = lean_array_push(x_18, x_13);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_st_ref_set(x_4, x_20, x_16);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
x_24 = lean_box(0);
lean_ctor_set(x_21, 0, x_24);
return x_21;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_dec(x_21);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_28 = lean_ctor_get(x_13, 0);
x_29 = lean_ctor_get(x_13, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_13);
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_1);
lean_ctor_set(x_32, 1, x_2);
x_33 = lean_array_push(x_31, x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_30);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_st_ref_set(x_4, x_34, x_29);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_37 = x_35;
} else {
 lean_dec_ref(x_35);
 x_37 = lean_box(0);
}
x_38 = lean_box(0);
if (lean_is_scalar(x_37)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_37;
}
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_36);
return x_39;
}
}
else
{
lean_object* x_40; 
lean_dec(x_2);
lean_dec(x_1);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_11);
lean_ctor_set(x_40, 1, x_10);
return x_40;
}
}
block_46:
{
uint8_t x_44; 
x_44 = l_Lean_Exception_isInterrupt(x_42);
if (x_44 == 0)
{
uint8_t x_45; 
x_45 = l_Lean_Exception_isRuntime(x_42);
x_10 = x_43;
x_11 = x_42;
x_12 = x_45;
goto block_41;
}
else
{
x_10 = x_43;
x_11 = x_42;
x_12 = x_44;
goto block_41;
}
}
block_48:
{
return x_47;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_tryUnify___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_tryUnify___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_tryUnify___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_tryUnify(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_inspectOutParams_inspectAux___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_inspectOutParams_inspectAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_13 = lean_whnf(x_1, x_8, x_9, x_10, x_11, x_12);
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
lean_inc(x_8);
x_16 = lean_whnf(x_2, x_8, x_9, x_10, x_11, x_15);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
x_20 = lean_array_get_size(x_4);
x_21 = lean_nat_dec_lt(x_3, x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
x_22 = lean_box(0);
lean_ctor_set(x_16, 0, x_22);
return x_16;
}
else
{
lean_free_object(x_16);
if (lean_obj_tag(x_14) == 7)
{
if (lean_obj_tag(x_18) == 7)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_42; 
x_23 = lean_ctor_get(x_14, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_14, 2);
lean_inc(x_24);
lean_dec(x_14);
x_25 = lean_ctor_get(x_18, 2);
lean_inc(x_25);
lean_dec(x_18);
x_26 = l_Lean_instInhabitedExpr;
x_42 = lean_is_out_param(x_23);
if (x_42 == 0)
{
x_27 = x_6;
x_28 = x_7;
x_29 = x_8;
x_30 = x_9;
x_31 = x_10;
x_32 = x_11;
x_33 = x_19;
goto block_41;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_array_get(x_26, x_4, x_3);
x_44 = lean_array_get(x_26, x_5, x_3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_45 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_tryUnify(x_43, x_44, x_6, x_7, x_8, x_9, x_10, x_11, x_19);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_27 = x_6;
x_28 = x_7;
x_29 = x_8;
x_30 = x_9;
x_31 = x_10;
x_32 = x_11;
x_33 = x_46;
goto block_41;
}
else
{
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
return x_45;
}
}
block_41:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_array_get(x_26, x_4, x_3);
x_35 = lean_expr_instantiate1(x_24, x_34);
lean_dec(x_34);
lean_dec(x_24);
x_36 = lean_array_get(x_26, x_5, x_3);
x_37 = lean_expr_instantiate1(x_25, x_36);
lean_dec(x_36);
lean_dec(x_25);
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_nat_add(x_3, x_38);
lean_dec(x_3);
x_1 = x_35;
x_2 = x_37;
x_3 = x_39;
x_6 = x_27;
x_7 = x_28;
x_8 = x_29;
x_9 = x_30;
x_10 = x_31;
x_11 = x_32;
x_12 = x_33;
goto _start;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_3);
x_47 = lean_ctor_get(x_14, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_14, 1);
lean_inc(x_48);
x_49 = lean_ctor_get(x_14, 2);
lean_inc(x_49);
x_50 = lean_ctor_get_uint8(x_14, sizeof(void*)*3 + 8);
lean_dec(x_14);
x_51 = l_Lean_Expr_forallE___override(x_47, x_48, x_49, x_50);
x_52 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_inspectOutParams_inspectAux___lam__0(x_51, x_18, x_6, x_7, x_8, x_9, x_10, x_11, x_19);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_18);
lean_dec(x_51);
return x_52;
}
}
else
{
lean_object* x_53; 
lean_dec(x_3);
x_53 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_inspectOutParams_inspectAux___lam__0(x_14, x_18, x_6, x_7, x_8, x_9, x_10, x_11, x_19);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_18);
lean_dec(x_14);
return x_53;
}
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_54 = lean_ctor_get(x_16, 0);
x_55 = lean_ctor_get(x_16, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_16);
x_56 = lean_array_get_size(x_4);
x_57 = lean_nat_dec_lt(x_3, x_56);
lean_dec(x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_54);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
x_58 = lean_box(0);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_55);
return x_59;
}
else
{
if (lean_obj_tag(x_14) == 7)
{
if (lean_obj_tag(x_54) == 7)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_79; 
x_60 = lean_ctor_get(x_14, 1);
lean_inc(x_60);
x_61 = lean_ctor_get(x_14, 2);
lean_inc(x_61);
lean_dec(x_14);
x_62 = lean_ctor_get(x_54, 2);
lean_inc(x_62);
lean_dec(x_54);
x_63 = l_Lean_instInhabitedExpr;
x_79 = lean_is_out_param(x_60);
if (x_79 == 0)
{
x_64 = x_6;
x_65 = x_7;
x_66 = x_8;
x_67 = x_9;
x_68 = x_10;
x_69 = x_11;
x_70 = x_55;
goto block_78;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_array_get(x_63, x_4, x_3);
x_81 = lean_array_get(x_63, x_5, x_3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_82 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_tryUnify(x_80, x_81, x_6, x_7, x_8, x_9, x_10, x_11, x_55);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; 
x_83 = lean_ctor_get(x_82, 1);
lean_inc(x_83);
lean_dec(x_82);
x_64 = x_6;
x_65 = x_7;
x_66 = x_8;
x_67 = x_9;
x_68 = x_10;
x_69 = x_11;
x_70 = x_83;
goto block_78;
}
else
{
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
return x_82;
}
}
block_78:
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_71 = lean_array_get(x_63, x_4, x_3);
x_72 = lean_expr_instantiate1(x_61, x_71);
lean_dec(x_71);
lean_dec(x_61);
x_73 = lean_array_get(x_63, x_5, x_3);
x_74 = lean_expr_instantiate1(x_62, x_73);
lean_dec(x_73);
lean_dec(x_62);
x_75 = lean_unsigned_to_nat(1u);
x_76 = lean_nat_add(x_3, x_75);
lean_dec(x_3);
x_1 = x_72;
x_2 = x_74;
x_3 = x_76;
x_6 = x_64;
x_7 = x_65;
x_8 = x_66;
x_9 = x_67;
x_10 = x_68;
x_11 = x_69;
x_12 = x_70;
goto _start;
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_3);
x_84 = lean_ctor_get(x_14, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_14, 1);
lean_inc(x_85);
x_86 = lean_ctor_get(x_14, 2);
lean_inc(x_86);
x_87 = lean_ctor_get_uint8(x_14, sizeof(void*)*3 + 8);
lean_dec(x_14);
x_88 = l_Lean_Expr_forallE___override(x_84, x_85, x_86, x_87);
x_89 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_inspectOutParams_inspectAux___lam__0(x_88, x_54, x_6, x_7, x_8, x_9, x_10, x_11, x_55);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_54);
lean_dec(x_88);
return x_89;
}
}
else
{
lean_object* x_90; 
lean_dec(x_3);
x_90 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_inspectOutParams_inspectAux___lam__0(x_14, x_54, x_6, x_7, x_8, x_9, x_10, x_11, x_55);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_54);
lean_dec(x_14);
return x_90;
}
}
}
}
else
{
uint8_t x_91; 
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
x_91 = !lean_is_exclusive(x_16);
if (x_91 == 0)
{
return x_16;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_16, 0);
x_93 = lean_ctor_get(x_16, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_16);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
else
{
uint8_t x_95; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_95 = !lean_is_exclusive(x_13);
if (x_95 == 0)
{
return x_13;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_13, 0);
x_97 = lean_ctor_get(x_13, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_13);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_inspectOutParams_inspectAux___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_inspectOutParams_inspectAux___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_inspectOutParams_inspectAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_inspectOutParams_inspectAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_inspectOutParams(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_10 = lean_infer_type(x_1, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_13 = lean_infer_type(x_2, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Expr_getAppFn(x_11);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_17 = lean_infer_type(x_16, x_5, x_6, x_7, x_8, x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Expr_getAppFn(x_14);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_21 = lean_infer_type(x_20, x_5, x_6, x_7, x_8, x_19);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_unsigned_to_nat(0u);
x_25 = lean_box(0);
x_26 = l_Lean_Expr_sort___override(x_25);
x_27 = l_Lean_Expr_getAppNumArgs(x_11);
lean_inc(x_26);
lean_inc(x_27);
x_28 = lean_mk_array(x_27, x_26);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_sub(x_27, x_29);
lean_dec(x_27);
x_31 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_11, x_28, x_30);
x_32 = l_Lean_Expr_getAppNumArgs(x_14);
lean_inc(x_32);
x_33 = lean_mk_array(x_32, x_26);
x_34 = lean_nat_sub(x_32, x_29);
lean_dec(x_32);
x_35 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_14, x_33, x_34);
x_36 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_inspectOutParams_inspectAux(x_18, x_22, x_24, x_31, x_35, x_3, x_4, x_5, x_6, x_7, x_8, x_23);
lean_dec(x_35);
lean_dec(x_31);
return x_36;
}
else
{
uint8_t x_37; 
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_37 = !lean_is_exclusive(x_21);
if (x_37 == 0)
{
return x_21;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_21, 0);
x_39 = lean_ctor_get(x_21, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_21);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_41 = !lean_is_exclusive(x_17);
if (x_41 == 0)
{
return x_17;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_17, 0);
x_43 = lean_ctor_get(x_17, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_17);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_45 = !lean_is_exclusive(x_13);
if (x_45 == 0)
{
return x_13;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_13, 0);
x_47 = lean_ctor_get(x_13, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_13);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_49 = !lean_is_exclusive(x_10);
if (x_49 == 0)
{
return x_10;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_10, 0);
x_51 = lean_ctor_get(x_10, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_10);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_inspectOutParams___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_inspectOutParams(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isTrivialBottomUp___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; uint8_t x_19; uint8_t x_41; 
x_4 = lean_ctor_get(x_2, 2);
x_41 = l_Lean_Expr_isFVar(x_1);
if (x_41 == 0)
{
uint8_t x_42; 
x_42 = l_Lean_Expr_isConst(x_1);
x_19 = x_42;
goto block_40;
}
else
{
x_19 = x_41;
goto block_40;
}
block_18:
{
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = l_Lean_getPPAnalyzeTrustOfScientific(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_mk_string_unchecked("OfScientific", 12, 12);
x_10 = lean_mk_string_unchecked("ofScientific", 12, 12);
x_11 = l_Lean_Name_mkStr2(x_9, x_10);
x_12 = lean_unsigned_to_nat(5u);
x_13 = l_Lean_Expr_isAppOfArity(x_1, x_11, x_12);
lean_dec(x_11);
x_14 = lean_box(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_3);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_box(x_5);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_3);
return x_17;
}
}
block_40:
{
if (x_19 == 0)
{
uint8_t x_20; 
x_20 = l_Lean_Expr_isMVar(x_1);
if (x_20 == 0)
{
uint8_t x_21; 
x_21 = l_Lean_Expr_isRawNatLit(x_1);
if (x_21 == 0)
{
uint8_t x_22; 
x_22 = l_Lean_Expr_isStringLit(x_1);
if (x_22 == 0)
{
uint8_t x_23; 
x_23 = l_Lean_Expr_isSort(x_1);
if (x_23 == 0)
{
uint8_t x_24; 
x_24 = l_Lean_getPPAnalyzeTrustOfNat(x_4);
if (x_24 == 0)
{
x_5 = x_24;
goto block_18;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_25 = lean_mk_string_unchecked("OfNat", 5, 5);
x_26 = lean_mk_string_unchecked("ofNat", 5, 5);
x_27 = l_Lean_Name_mkStr2(x_25, x_26);
x_28 = lean_unsigned_to_nat(3u);
x_29 = l_Lean_Expr_isAppOfArity(x_1, x_27, x_28);
lean_dec(x_27);
x_5 = x_29;
goto block_18;
}
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_box(x_23);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_3);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_box(x_22);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_3);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_box(x_21);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_3);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_box(x_20);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_3);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_box(x_19);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_3);
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isTrivialBottomUp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isTrivialBottomUp___redArg(x_1, x_6, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isTrivialBottomUp___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isTrivialBottomUp___redArg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isTrivialBottomUp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isTrivialBottomUp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_canBottomUp_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_21 = l_Lean_Expr_getAppNumArgs(x_2);
x_22 = lean_box(0);
x_23 = l_Lean_Expr_sort___override(x_22);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_ctor_get(x_5, 1);
x_26 = lean_nat_dec_lt(x_7, x_25);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_2);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_6);
lean_ctor_set(x_27, 1, x_14);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; uint8_t x_37; uint8_t x_38; 
lean_dec(x_6);
lean_inc(x_21);
x_28 = lean_mk_array(x_21, x_23);
x_29 = lean_nat_sub(x_21, x_24);
lean_dec(x_21);
x_30 = lean_box(0);
x_31 = lean_box(0);
x_32 = l_Lean_instInhabitedExpr;
lean_inc(x_2);
x_33 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_2, x_28, x_29);
x_34 = lean_array_get(x_30, x_1, x_7);
x_35 = lean_unbox(x_34);
lean_dec(x_34);
x_36 = lean_box(3);
x_37 = lean_unbox(x_36);
x_38 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(x_35, x_37);
if (x_38 == 0)
{
uint8_t x_39; uint8_t x_40; 
x_39 = lean_unbox(x_30);
x_40 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(x_35, x_39);
if (x_40 == 0)
{
lean_dec(x_33);
x_15 = x_31;
x_16 = x_14;
goto block_20;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_41 = lean_array_get(x_32, x_33, x_7);
lean_dec(x_33);
x_42 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isTrivialBottomUp___redArg(x_41, x_12, x_14);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_unbox(x_43);
lean_dec(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_59; 
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_dec(x_42);
x_46 = lean_array_fget(x_3, x_7);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_46);
x_59 = l___private_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_0__Lean_PrettyPrinter_Delaborator_TopDownAnalyze_typeUnknown(x_46, x_10, x_11, x_12, x_13, x_45);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; uint8_t x_61; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_unbox(x_60);
lean_dec(x_60);
if (x_61 == 0)
{
x_47 = x_59;
goto block_58;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_59, 1);
lean_inc(x_62);
lean_dec(x_59);
lean_inc(x_46);
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_46);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_41);
x_64 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_canBottomUp(x_41, x_63, x_4, x_8, x_9, x_10, x_11, x_12, x_13, x_62);
x_47 = x_64;
goto block_58;
}
}
else
{
x_47 = x_59;
goto block_58;
}
block_58:
{
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_unbox(x_48);
lean_dec(x_48);
if (x_49 == 0)
{
lean_object* x_50; 
lean_dec(x_46);
lean_dec(x_41);
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
lean_dec(x_47);
x_15 = x_31;
x_16 = x_50;
goto block_20;
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_47, 1);
lean_inc(x_51);
lean_dec(x_47);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_52 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_tryUnify(x_41, x_46, x_8, x_9, x_10, x_11, x_12, x_13, x_51);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_dec(x_52);
x_15 = x_31;
x_16 = x_53;
goto block_20;
}
else
{
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_2);
return x_52;
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_46);
lean_dec(x_41);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_2);
x_54 = !lean_is_exclusive(x_47);
if (x_54 == 0)
{
return x_47;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_47, 0);
x_56 = lean_ctor_get(x_47, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_47);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_42, 1);
lean_inc(x_65);
lean_dec(x_42);
x_66 = lean_array_fget(x_3, x_7);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_67 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_tryUnify(x_41, x_66, x_8, x_9, x_10, x_11, x_12, x_13, x_65);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
lean_dec(x_67);
x_15 = x_31;
x_16 = x_68;
goto block_20;
}
else
{
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_2);
return x_67;
}
}
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_array_get(x_32, x_33, x_7);
lean_dec(x_33);
x_70 = lean_array_fget(x_3, x_7);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_71 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_inspectOutParams(x_69, x_70, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
lean_dec(x_71);
x_15 = x_31;
x_16 = x_72;
goto block_20;
}
else
{
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_2);
return x_71;
}
}
}
block_20:
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_5, 2);
x_18 = lean_nat_add(x_7, x_17);
lean_dec(x_7);
x_6 = x_15;
x_7 = x_18;
x_14 = x_16;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_canBottomUp_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_canBottomUp_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_canBottomUp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_55; uint8_t x_56; 
x_55 = lean_unsigned_to_nat(0u);
x_56 = lean_nat_dec_eq(x_3, x_55);
if (x_56 == 1)
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_57 = lean_box(0);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_10);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_59 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isTrivialBottomUp___redArg(x_1, x_8, x_10);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_unbox(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; uint8_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_91; lean_object* x_92; uint8_t x_93; uint8_t x_142; 
x_62 = lean_ctor_get(x_59, 1);
lean_inc(x_62);
x_63 = lean_unsigned_to_nat(1u);
x_64 = l_Lean_instInhabitedExpr;
x_91 = lean_nat_sub(x_3, x_63);
x_92 = l_Lean_Expr_getAppFn(x_1);
x_142 = l_Lean_Expr_isConst(x_92);
if (x_142 == 0)
{
uint8_t x_143; 
x_143 = l_Lean_Expr_isFVar(x_92);
if (x_143 == 0)
{
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_62);
lean_dec(x_60);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_59;
}
else
{
uint8_t x_144; 
lean_dec(x_59);
x_144 = lean_unbox(x_60);
lean_dec(x_60);
x_93 = x_144;
goto block_141;
}
}
else
{
uint8_t x_145; 
lean_dec(x_59);
x_145 = lean_unbox(x_60);
lean_dec(x_60);
x_93 = x_145;
goto block_141;
}
block_80:
{
if (x_70 == 0)
{
lean_dec(x_68);
lean_dec(x_66);
x_31 = x_65;
x_32 = x_69;
x_33 = x_4;
x_34 = x_5;
x_35 = x_6;
x_36 = x_7;
x_37 = x_8;
x_38 = x_9;
x_39 = x_71;
goto block_54;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_array_get(x_64, x_68, x_66);
lean_dec(x_66);
x_73 = lean_array_get(x_64, x_68, x_67);
lean_dec(x_68);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_74 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_tryUnify(x_72, x_73, x_4, x_5, x_6, x_7, x_8, x_9, x_71);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; 
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
lean_dec(x_74);
x_31 = x_65;
x_32 = x_69;
x_33 = x_4;
x_34 = x_5;
x_35 = x_6;
x_36 = x_7;
x_37 = x_8;
x_38 = x_9;
x_39 = x_75;
goto block_54;
}
else
{
uint8_t x_76; 
lean_dec(x_69);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_76 = !lean_is_exclusive(x_74);
if (x_76 == 0)
{
return x_74;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_74, 0);
x_78 = lean_ctor_get(x_74, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_74);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
}
block_90:
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
x_89 = lean_unbox(x_87);
lean_dec(x_87);
x_65 = x_81;
x_66 = x_82;
x_67 = x_83;
x_68 = x_84;
x_69 = x_85;
x_70 = x_89;
x_71 = x_88;
goto block_80;
}
block_141:
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_95 = lean_infer_type(x_92, x_6, x_7, x_8, x_9, x_62);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; lean_object* x_109; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
x_98 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars(x_96, x_6, x_7, x_8, x_9, x_97);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
x_101 = l_Lean_Expr_sort___override(x_94);
x_102 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_102);
x_103 = lean_mk_array(x_102, x_101);
x_104 = lean_nat_sub(x_102, x_63);
lean_dec(x_102);
lean_inc(x_1);
x_105 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_103, x_104);
x_106 = lean_array_get_size(x_105);
lean_dec(x_105);
x_107 = lean_box(0);
x_108 = lean_unbox(x_107);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_109 = l_Lean_Meta_forallMetaBoundedTelescope(x_99, x_106, x_108, x_6, x_7, x_8, x_9, x_100);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_110, 1);
lean_inc(x_111);
x_112 = lean_ctor_get(x_109, 1);
lean_inc(x_112);
lean_dec(x_109);
x_113 = lean_ctor_get(x_110, 0);
lean_inc(x_113);
lean_dec(x_110);
x_114 = lean_ctor_get(x_111, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_111, 1);
lean_inc(x_115);
lean_dec(x_111);
x_116 = lean_array_get_size(x_113);
x_117 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_117, 0, x_55);
lean_ctor_set(x_117, 1, x_116);
lean_ctor_set(x_117, 2, x_63);
x_118 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_119 = l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_canBottomUp_spec__0___redArg(x_114, x_1, x_113, x_91, x_117, x_118, x_55, x_4, x_5, x_6, x_7, x_8, x_9, x_112);
lean_dec(x_117);
lean_dec(x_91);
lean_dec(x_114);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; uint8_t x_121; 
x_120 = lean_ctor_get(x_119, 1);
lean_inc(x_120);
lean_dec(x_119);
x_121 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp(x_1);
lean_dec(x_1);
if (x_121 == 0)
{
x_65 = x_93;
x_66 = x_55;
x_67 = x_63;
x_68 = x_113;
x_69 = x_115;
x_70 = x_121;
x_71 = x_120;
goto block_80;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; 
x_122 = lean_array_get(x_64, x_113, x_55);
x_123 = l___private_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_0__Lean_PrettyPrinter_Delaborator_TopDownAnalyze_valUnknown___redArg(x_122, x_7, x_120);
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_unbox(x_124);
lean_dec(x_124);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_123, 1);
lean_inc(x_126);
lean_dec(x_123);
x_127 = lean_array_get(x_64, x_113, x_63);
x_128 = l___private_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_0__Lean_PrettyPrinter_Delaborator_TopDownAnalyze_valUnknown___redArg(x_127, x_7, x_126);
x_81 = x_93;
x_82 = x_55;
x_83 = x_63;
x_84 = x_113;
x_85 = x_115;
x_86 = x_128;
goto block_90;
}
else
{
x_81 = x_93;
x_82 = x_55;
x_83 = x_63;
x_84 = x_113;
x_85 = x_115;
x_86 = x_123;
goto block_90;
}
}
}
else
{
uint8_t x_129; 
lean_dec(x_115);
lean_dec(x_113);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_129 = !lean_is_exclusive(x_119);
if (x_129 == 0)
{
return x_119;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_119, 0);
x_131 = lean_ctor_get(x_119, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_119);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
return x_132;
}
}
}
else
{
uint8_t x_133; 
lean_dec(x_91);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_133 = !lean_is_exclusive(x_109);
if (x_133 == 0)
{
return x_109;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_ctor_get(x_109, 0);
x_135 = lean_ctor_get(x_109, 1);
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_109);
x_136 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
return x_136;
}
}
}
else
{
uint8_t x_137; 
lean_dec(x_91);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_137 = !lean_is_exclusive(x_95);
if (x_137 == 0)
{
return x_95;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_95, 0);
x_139 = lean_ctor_get(x_95, 1);
lean_inc(x_139);
lean_inc(x_138);
lean_dec(x_95);
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
return x_140;
}
}
}
}
else
{
lean_dec(x_60);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_59;
}
}
block_30:
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = l___private_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_0__Lean_PrettyPrinter_Delaborator_TopDownAnalyze_valUnknown___redArg(x_12, x_13, x_14);
lean_dec(x_13);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_15, 0);
lean_dec(x_19);
x_20 = lean_box(1);
lean_ctor_set(x_15, 0, x_20);
return x_15;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_dec(x_15);
x_22 = lean_box(1);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_15);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_15, 0);
lean_dec(x_25);
x_26 = lean_box(x_11);
lean_ctor_set(x_15, 0, x_26);
return x_15;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_15, 1);
lean_inc(x_27);
lean_dec(x_15);
x_28 = lean_box(x_11);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
}
block_54:
{
if (lean_obj_tag(x_2) == 0)
{
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_35);
x_11 = x_31;
x_12 = x_32;
x_13 = x_36;
x_14 = x_39;
goto block_30;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_2, 0);
lean_inc(x_40);
lean_dec(x_2);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
x_41 = lean_infer_type(x_40, x_35, x_36, x_37, x_38, x_39);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
lean_inc(x_36);
lean_inc(x_32);
x_44 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_tryUnify(x_32, x_42, x_33, x_34, x_35, x_36, x_37, x_38, x_43);
lean_dec(x_35);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_11 = x_31;
x_12 = x_32;
x_13 = x_36;
x_14 = x_45;
goto block_30;
}
else
{
uint8_t x_46; 
lean_dec(x_36);
lean_dec(x_32);
x_46 = !lean_is_exclusive(x_44);
if (x_46 == 0)
{
return x_44;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_44, 0);
x_48 = lean_ctor_get(x_44, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_44);
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
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_32);
x_50 = !lean_is_exclusive(x_41);
if (x_50 == 0)
{
return x_41;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_41, 0);
x_52 = lean_ctor_get(x_41, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_41);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_canBottomUp_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_canBottomUp_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_canBottomUp_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_canBottomUp_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_canBottomUp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_canBottomUp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_withKnowing___redArg(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get_uint8(x_4, sizeof(void*)*1 + 2);
x_12 = lean_ctor_get_uint8(x_4, sizeof(void*)*1 + 3);
x_13 = lean_ctor_get(x_4, 0);
lean_inc(x_13);
x_14 = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set_uint8(x_14, sizeof(void*)*1, x_1);
lean_ctor_set_uint8(x_14, sizeof(void*)*1 + 1, x_2);
lean_ctor_set_uint8(x_14, sizeof(void*)*1 + 2, x_11);
lean_ctor_set_uint8(x_14, sizeof(void*)*1 + 3, x_12);
x_15 = lean_apply_7(x_3, x_14, x_5, x_6, x_7, x_8, x_9, x_10);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_withKnowing(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_withKnowing___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_withKnowing___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_withKnowing___redArg(x_11, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_withKnowing___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = lean_unbox(x_3);
lean_dec(x_3);
x_14 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_withKnowing(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_3632_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_mk_string_unchecked("analyzeFailure", 14, 14);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = l_Lean_registerInternalExceptionId(x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_checkKnowsType___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeFailureId;
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_2);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_2);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_checkKnowsType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_checkKnowsType___redArg(x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_checkKnowsType___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_checkKnowsType___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_checkKnowsType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_checkKnowsType(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 12);
x_5 = lean_ctor_get(x_2, 2);
x_6 = l_Lean_checkTraceOption(x_4, x_5, x_1);
x_7 = lean_box(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_isTracingEnabledFor___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt_spec__0___redArg(x_1, x_6, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = l_Lean_addMessageContextFull___at___Lean_Meta_recordSynthPendingFailure_spec__3(x_2, x_3, x_4, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_st_ref_take(x_6, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint64_t x_20; lean_object* x_21; lean_object* x_22; double x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = lean_ctor_get(x_5, 5);
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_13, 2);
lean_inc(x_18);
x_19 = lean_ctor_get(x_13, 3);
lean_inc(x_19);
x_20 = lean_ctor_get_uint64(x_19, sizeof(void*)*1);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_float_of_nat(x_22);
x_24 = lean_box(0);
x_25 = lean_mk_string_unchecked("", 0, 0);
x_26 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set_float(x_26, sizeof(void*)*2, x_23);
lean_ctor_set_float(x_26, sizeof(void*)*2 + 8, x_23);
x_27 = lean_unbox(x_24);
lean_ctor_set_uint8(x_26, sizeof(void*)*2 + 16, x_27);
x_28 = lean_mk_empty_array_with_capacity(x_22);
x_29 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_9);
lean_ctor_set(x_29, 2, x_28);
lean_inc(x_15);
lean_ctor_set(x_11, 1, x_29);
lean_ctor_set(x_11, 0, x_15);
x_30 = l_Lean_PersistentArray_push___redArg(x_21, x_11);
x_31 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set_uint64(x_31, sizeof(void*)*1, x_20);
x_32 = lean_ctor_get(x_13, 4);
lean_inc(x_32);
x_33 = lean_ctor_get(x_13, 5);
lean_inc(x_33);
x_34 = lean_ctor_get(x_13, 6);
lean_inc(x_34);
x_35 = lean_ctor_get(x_13, 7);
lean_inc(x_35);
lean_dec(x_13);
x_36 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_36, 0, x_16);
lean_ctor_set(x_36, 1, x_17);
lean_ctor_set(x_36, 2, x_18);
lean_ctor_set(x_36, 3, x_31);
lean_ctor_set(x_36, 4, x_32);
lean_ctor_set(x_36, 5, x_33);
lean_ctor_set(x_36, 6, x_34);
lean_ctor_set(x_36, 7, x_35);
x_37 = lean_st_ref_set(x_6, x_36, x_14);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_37, 0);
lean_dec(x_39);
x_40 = lean_box(0);
lean_ctor_set(x_37, 0, x_40);
return x_37;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_37, 1);
lean_inc(x_41);
lean_dec(x_37);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint64_t x_51; lean_object* x_52; lean_object* x_53; double x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_44 = lean_ctor_get(x_11, 0);
x_45 = lean_ctor_get(x_11, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_11);
x_46 = lean_ctor_get(x_5, 5);
x_47 = lean_ctor_get(x_44, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_44, 1);
lean_inc(x_48);
x_49 = lean_ctor_get(x_44, 2);
lean_inc(x_49);
x_50 = lean_ctor_get(x_44, 3);
lean_inc(x_50);
x_51 = lean_ctor_get_uint64(x_50, sizeof(void*)*1);
x_52 = lean_ctor_get(x_50, 0);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_unsigned_to_nat(0u);
x_54 = lean_float_of_nat(x_53);
x_55 = lean_box(0);
x_56 = lean_mk_string_unchecked("", 0, 0);
x_57 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_57, 0, x_1);
lean_ctor_set(x_57, 1, x_56);
lean_ctor_set_float(x_57, sizeof(void*)*2, x_54);
lean_ctor_set_float(x_57, sizeof(void*)*2 + 8, x_54);
x_58 = lean_unbox(x_55);
lean_ctor_set_uint8(x_57, sizeof(void*)*2 + 16, x_58);
x_59 = lean_mk_empty_array_with_capacity(x_53);
x_60 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_9);
lean_ctor_set(x_60, 2, x_59);
lean_inc(x_46);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_46);
lean_ctor_set(x_61, 1, x_60);
x_62 = l_Lean_PersistentArray_push___redArg(x_52, x_61);
x_63 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set_uint64(x_63, sizeof(void*)*1, x_51);
x_64 = lean_ctor_get(x_44, 4);
lean_inc(x_64);
x_65 = lean_ctor_get(x_44, 5);
lean_inc(x_65);
x_66 = lean_ctor_get(x_44, 6);
lean_inc(x_66);
x_67 = lean_ctor_get(x_44, 7);
lean_inc(x_67);
lean_dec(x_44);
x_68 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_68, 0, x_47);
lean_ctor_set(x_68, 1, x_48);
lean_ctor_set(x_68, 2, x_49);
lean_ctor_set(x_68, 3, x_63);
lean_ctor_set(x_68, 4, x_64);
lean_ctor_set(x_68, 5, x_65);
lean_ctor_set(x_68, 6, x_66);
lean_ctor_set(x_68, 7, x_67);
x_69 = lean_st_ref_set(x_6, x_68, x_45);
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
x_72 = lean_box(0);
if (lean_is_scalar(x_71)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_71;
}
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_70);
return x_73;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_addTrace___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt_spec__1___redArg(x_1, x_2, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_90; lean_object* x_91; 
x_39 = lean_st_ref_get(x_4, x_9);
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
x_90 = lean_ctor_get(x_40, 0);
lean_inc(x_90);
lean_dec(x_40);
lean_inc(x_2);
x_91 = l_Lean_RBNode_find___at___Lean_PrettyPrinter_Delaborator_OptionsPerPos_insertAt_spec__2___redArg(x_90, x_2);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; 
x_92 = lean_box(0);
x_43 = x_92;
goto block_89;
}
else
{
lean_object* x_93; 
x_93 = lean_ctor_get(x_91, 0);
lean_inc(x_93);
lean_dec(x_91);
x_43 = x_93;
goto block_89;
}
block_38:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_st_ref_take(x_11, x_12);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = l_Lean_RBNode_insert___at___Lean_PrettyPrinter_Delaborator_OptionsPerPos_insertAt_spec__0___redArg(x_17, x_2, x_10);
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_dec(x_15);
lean_ctor_set(x_13, 1, x_19);
lean_ctor_set(x_13, 0, x_18);
x_20 = lean_st_ref_set(x_11, x_13, x_16);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
x_23 = lean_box(0);
lean_ctor_set(x_20, 0, x_23);
return x_20;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec(x_20);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_27 = lean_ctor_get(x_13, 0);
x_28 = lean_ctor_get(x_13, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_13);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
x_30 = l_Lean_RBNode_insert___at___Lean_PrettyPrinter_Delaborator_OptionsPerPos_insertAt_spec__0___redArg(x_29, x_2, x_10);
x_31 = lean_ctor_get(x_27, 1);
lean_inc(x_31);
lean_dec(x_27);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_st_ref_set(x_11, x_32, x_28);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_35 = x_33;
} else {
 lean_dec_ref(x_33);
 x_35 = lean_box(0);
}
x_36 = lean_box(0);
if (lean_is_scalar(x_35)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_35;
}
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_34);
return x_37;
}
}
block_89:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_44 = lean_mk_string_unchecked("pp", 2, 2);
x_45 = lean_mk_string_unchecked("analyze", 7, 7);
x_46 = lean_mk_string_unchecked("annotate", 8, 8);
x_47 = l_Lean_Name_mkStr3(x_44, x_45, x_46);
lean_inc(x_47);
x_48 = l_Lean_isTracingEnabledFor___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt_spec__0___redArg(x_47, x_7, x_41);
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; uint8_t x_55; 
x_50 = lean_ctor_get(x_48, 0);
x_51 = lean_ctor_get(x_48, 1);
x_52 = lean_box(1);
x_53 = lean_unbox(x_52);
lean_inc(x_1);
x_54 = l_Lean_KVMap_setBool(x_43, x_1, x_53);
x_55 = lean_unbox(x_50);
lean_dec(x_50);
if (x_55 == 0)
{
lean_free_object(x_48);
lean_dec(x_47);
lean_dec(x_42);
lean_dec(x_1);
x_10 = x_54;
x_11 = x_4;
x_12 = x_51;
goto block_38;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_56 = lean_mk_string_unchecked("", 0, 0);
x_57 = l_Lean_stringToMessageData(x_56);
lean_dec(x_56);
x_58 = l_Lean_SubExpr_Pos_toString(x_2);
x_59 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_59, 0, x_58);
x_60 = l_Lean_MessageData_ofFormat(x_59);
lean_inc(x_57);
lean_ctor_set_tag(x_48, 7);
lean_ctor_set(x_48, 1, x_60);
lean_ctor_set(x_48, 0, x_57);
x_61 = lean_mk_string_unchecked(" ", 1, 1);
x_62 = l_Lean_stringToMessageData(x_61);
lean_dec(x_61);
if (lean_is_scalar(x_42)) {
 x_63 = lean_alloc_ctor(7, 2, 0);
} else {
 x_63 = x_42;
 lean_ctor_set_tag(x_63, 7);
}
lean_ctor_set(x_63, 0, x_48);
lean_ctor_set(x_63, 1, x_62);
x_64 = l_Lean_MessageData_ofName(x_1);
x_65 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_57);
x_67 = l_Lean_addTrace___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt_spec__1___redArg(x_47, x_66, x_5, x_6, x_7, x_8, x_51);
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
lean_dec(x_67);
x_10 = x_54;
x_11 = x_4;
x_12 = x_68;
goto block_38;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; lean_object* x_73; uint8_t x_74; 
x_69 = lean_ctor_get(x_48, 0);
x_70 = lean_ctor_get(x_48, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_48);
x_71 = lean_box(1);
x_72 = lean_unbox(x_71);
lean_inc(x_1);
x_73 = l_Lean_KVMap_setBool(x_43, x_1, x_72);
x_74 = lean_unbox(x_69);
lean_dec(x_69);
if (x_74 == 0)
{
lean_dec(x_47);
lean_dec(x_42);
lean_dec(x_1);
x_10 = x_73;
x_11 = x_4;
x_12 = x_70;
goto block_38;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_75 = lean_mk_string_unchecked("", 0, 0);
x_76 = l_Lean_stringToMessageData(x_75);
lean_dec(x_75);
x_77 = l_Lean_SubExpr_Pos_toString(x_2);
x_78 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_78, 0, x_77);
x_79 = l_Lean_MessageData_ofFormat(x_78);
lean_inc(x_76);
x_80 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_80, 0, x_76);
lean_ctor_set(x_80, 1, x_79);
x_81 = lean_mk_string_unchecked(" ", 1, 1);
x_82 = l_Lean_stringToMessageData(x_81);
lean_dec(x_81);
if (lean_is_scalar(x_42)) {
 x_83 = lean_alloc_ctor(7, 2, 0);
} else {
 x_83 = x_42;
 lean_ctor_set_tag(x_83, 7);
}
lean_ctor_set(x_83, 0, x_80);
lean_ctor_set(x_83, 1, x_82);
x_84 = l_Lean_MessageData_ofName(x_1);
x_85 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
x_86 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_76);
x_87 = l_Lean_addTrace___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt_spec__1___redArg(x_47, x_86, x_5, x_6, x_7, x_8, x_70);
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
lean_dec(x_87);
x_10 = x_73;
x_11 = x_4;
x_12 = x_88;
goto block_38;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isTracingEnabledFor___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_isTracingEnabledFor___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_addTrace___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_addTrace___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBool_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBool_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBool_spec__0___redArg(x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBool(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBool_spec__0___redArg(x_2, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt(x_1, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBool_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBool_spec__0___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBool_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBool_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBool___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBool(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectBottomUps_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_5, 1);
x_24 = lean_nat_dec_lt(x_7, x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_4);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_6);
lean_ctor_set(x_25, 1, x_8);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_15);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; 
lean_dec(x_6);
x_27 = lean_box(0);
x_28 = lean_box(0);
x_29 = lean_array_get(x_28, x_1, x_7);
x_30 = lean_unbox(x_29);
lean_dec(x_29);
x_31 = lean_unbox(x_28);
x_32 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(x_30, x_31);
if (x_32 == 0)
{
x_16 = x_27;
x_17 = x_8;
x_18 = x_15;
goto block_22;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = l_Lean_instInhabitedExpr;
x_34 = lean_array_get(x_33, x_2, x_7);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_34);
x_35 = l___private_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_0__Lean_PrettyPrinter_Delaborator_TopDownAnalyze_typeUnknown(x_34, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_unbox(x_36);
lean_dec(x_36);
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_34);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_16 = x_27;
x_17 = x_8;
x_18 = x_38;
goto block_22;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_35, 1);
lean_inc(x_39);
lean_dec(x_35);
x_40 = lean_array_fget(x_3, x_7);
lean_inc(x_4);
lean_inc(x_7);
x_41 = lean_apply_1(x_4, x_7);
x_42 = lean_unsigned_to_nat(10u);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_43 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_canBottomUp(x_40, x_41, x_42, x_9, x_10, x_11, x_12, x_13, x_14, x_39);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_unbox(x_44);
if (x_45 == 0)
{
lean_object* x_46; 
lean_dec(x_44);
lean_dec(x_34);
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_dec(x_43);
x_16 = x_27;
x_17 = x_8;
x_18 = x_46;
goto block_22;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_43, 1);
lean_inc(x_47);
lean_dec(x_43);
x_48 = lean_array_get(x_33, x_3, x_7);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_49 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_tryUnify(x_48, x_34, x_9, x_10, x_11, x_12, x_13, x_14, x_47);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec(x_49);
x_51 = lean_ctor_get(x_8, 0);
lean_inc(x_51);
x_52 = lean_array_set(x_51, x_7, x_44);
x_53 = lean_ctor_get(x_8, 1);
lean_inc(x_53);
x_54 = lean_ctor_get(x_8, 2);
lean_inc(x_54);
x_55 = lean_ctor_get(x_8, 3);
lean_inc(x_55);
x_56 = lean_ctor_get(x_8, 4);
lean_inc(x_56);
lean_dec(x_8);
x_57 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_57, 0, x_52);
lean_ctor_set(x_57, 1, x_53);
lean_ctor_set(x_57, 2, x_54);
lean_ctor_set(x_57, 3, x_55);
lean_ctor_set(x_57, 4, x_56);
x_16 = x_27;
x_17 = x_57;
x_18 = x_50;
goto block_22;
}
else
{
uint8_t x_58; 
lean_dec(x_44);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_58 = !lean_is_exclusive(x_49);
if (x_58 == 0)
{
return x_49;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_49, 0);
x_60 = lean_ctor_get(x_49, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_49);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_34);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_62 = !lean_is_exclusive(x_43);
if (x_62 == 0)
{
return x_43;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_43, 0);
x_64 = lean_ctor_get(x_43, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_43);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
}
else
{
uint8_t x_66; 
lean_dec(x_34);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_66 = !lean_is_exclusive(x_35);
if (x_66 == 0)
{
return x_35;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_35, 0);
x_68 = lean_ctor_get(x_35, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_35);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
}
block_22:
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_5, 2);
x_20 = lean_nat_add(x_7, x_19);
lean_dec(x_7);
x_6 = x_16;
x_7 = x_20;
x_8 = x_17;
x_15 = x_18;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectBottomUps_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
lean_object* x_19; 
x_19 = l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectBottomUps_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
return x_19;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectBottomUps_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_5);
lean_ctor_set(x_15, 1, x_7);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_5);
x_17 = lean_ctor_get(x_4, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_4, 1);
lean_inc(x_18);
lean_dec(x_4);
x_19 = lean_box(0);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_array_get_size(x_1);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_21);
lean_ctor_set(x_23, 2, x_22);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_24 = l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectBottomUps_spec__0___redArg(x_2, x_3, x_1, x_17, x_23, x_19, x_20, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_4 = x_18;
x_5 = x_19;
x_7 = x_27;
x_14 = x_26;
goto _start;
}
else
{
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectBottomUps_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectBottomUps_spec__1_spec__1___redArg(x_1, x_2, x_3, x_5, x_6, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_17;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectBottomUps_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_6);
lean_ctor_set(x_16, 1, x_8);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_6);
x_18 = lean_ctor_get(x_5, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_5, 1);
lean_inc(x_19);
lean_dec(x_5);
x_20 = lean_box(0);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_array_get_size(x_3);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_22);
lean_ctor_set(x_24, 2, x_23);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_25 = l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectBottomUps_spec__0___redArg(x_1, x_2, x_3, x_18, x_24, x_20, x_21, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectBottomUps_spec__1_spec__1___redArg(x_3, x_1, x_2, x_19, x_20, x_7, x_28, x_9, x_10, x_11, x_12, x_13, x_14, x_27);
return x_29;
}
else
{
lean_dec(x_19);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectBottomUps_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_List_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectBottomUps_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectBottomUps___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectBottomUps___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_array_get(x_1, x_2, x_3);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectBottomUps(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 3);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 4);
lean_inc(x_12);
x_13 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectBottomUps___lam__0___boxed), 1, 0);
x_14 = l_Lean_instInhabitedExpr;
lean_inc(x_11);
x_15 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectBottomUps___lam__1___boxed), 3, 2);
lean_closure_set(x_15, 0, x_14);
lean_closure_set(x_15, 1, x_11);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_13);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_box(0);
lean_inc(x_18);
x_20 = l_List_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectBottomUps_spec__1___redArg(x_12, x_11, x_10, x_18, x_18, x_19, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
lean_dec(x_18);
lean_dec(x_10);
lean_dec(x_11);
lean_dec(x_12);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
lean_ctor_set(x_22, 0, x_19);
return x_20;
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
lean_ctor_set(x_20, 0, x_26);
return x_20;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_27 = lean_ctor_get(x_20, 0);
x_28 = lean_ctor_get(x_20, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_20);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_30 = x_27;
} else {
 lean_dec_ref(x_27);
 x_30 = lean_box(0);
}
if (lean_is_scalar(x_30)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_30;
}
lean_ctor_set(x_31, 0, x_19);
lean_ctor_set(x_31, 1, x_29);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_28);
return x_32;
}
}
else
{
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectBottomUps_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectBottomUps_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectBottomUps_spec__0___boxed(lean_object** _args) {
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
lean_object* x_19; 
x_19 = l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectBottomUps_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_19;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectBottomUps_spec__1_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectBottomUps_spec__1_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectBottomUps_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectBottomUps_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectBottomUps_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_List_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectBottomUps_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectBottomUps_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_List_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectBottomUps_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectBottomUps___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectBottomUps___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectBottomUps___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectBottomUps___lam__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectBottomUps___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectBottomUps(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_checkOutParams_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_4, 1);
x_23 = lean_nat_dec_lt(x_6, x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_5);
lean_ctor_set(x_24, 1, x_7);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_14);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; uint8_t x_31; uint8_t x_32; 
lean_dec(x_5);
x_26 = lean_box(0);
x_27 = lean_box(0);
x_28 = lean_array_get(x_26, x_1, x_6);
x_29 = lean_unbox(x_28);
lean_dec(x_28);
x_30 = lean_box(3);
x_31 = lean_unbox(x_30);
x_32 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(x_29, x_31);
if (x_32 == 0)
{
x_15 = x_27;
x_16 = x_7;
x_17 = x_14;
goto block_21;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_array_fget(x_2, x_6);
x_34 = l_Lean_instInhabitedExpr;
x_35 = lean_array_get(x_34, x_3, x_6);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_36 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_inspectOutParams(x_33, x_35, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_15 = x_27;
x_16 = x_7;
x_17 = x_37;
goto block_21;
}
else
{
uint8_t x_38; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
x_38 = !lean_is_exclusive(x_36);
if (x_38 == 0)
{
return x_36;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_36, 0);
x_40 = lean_ctor_get(x_36, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_36);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
block_21:
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_4, 2);
x_19 = lean_nat_add(x_6, x_18);
lean_dec(x_6);
x_5 = x_15;
x_6 = x_19;
x_7 = x_16;
x_14 = x_17;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_checkOutParams_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; 
x_18 = l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_checkOutParams_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_checkOutParams(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_10 = lean_ctor_get(x_1, 2);
x_11 = lean_ctor_get(x_1, 3);
x_12 = lean_ctor_get(x_1, 4);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_array_get_size(x_10);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_14);
lean_ctor_set(x_16, 2, x_15);
x_17 = lean_box(0);
x_18 = l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_checkOutParams_spec__0___redArg(x_12, x_10, x_11, x_16, x_17, x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_16);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
lean_ctor_set(x_20, 0, x_17);
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_17);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set(x_18, 0, x_24);
return x_18;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_18, 0);
x_26 = lean_ctor_get(x_18, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_18);
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
if (lean_is_scalar(x_28)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_28;
}
lean_ctor_set(x_29, 0, x_17);
lean_ctor_set(x_29, 1, x_27);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_26);
return x_30;
}
}
else
{
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_checkOutParams_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_checkOutParams_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_checkOutParams_spec__0___boxed(lean_object** _args) {
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
lean_object* x_18; 
x_18 = l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_checkOutParams_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_checkOutParams___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_checkOutParams(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectHigherOrders_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_42; uint8_t x_43; uint8_t x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_50; uint8_t x_51; 
x_22 = lean_box(0);
x_50 = lean_ctor_get(x_4, 1);
x_51 = lean_nat_dec_lt(x_6, x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_5);
lean_ctor_set(x_52, 1, x_7);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_14);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; uint8_t x_57; uint8_t x_81; lean_object* x_106; lean_object* x_107; uint8_t x_108; lean_object* x_109; uint8_t x_110; uint8_t x_111; 
lean_dec(x_5);
x_54 = l_Lean_instInhabitedExpr;
x_106 = lean_box(0);
x_107 = lean_array_get(x_106, x_3, x_6);
x_108 = lean_unbox(x_107);
lean_dec(x_107);
x_109 = lean_box(1);
x_110 = lean_unbox(x_109);
x_111 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(x_108, x_110);
if (x_111 == 0)
{
lean_object* x_112; uint8_t x_113; uint8_t x_114; 
x_112 = lean_box(2);
x_113 = lean_unbox(x_112);
x_114 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(x_108, x_113);
x_81 = x_114;
goto block_105;
}
else
{
x_81 = x_111;
goto block_105;
}
block_80:
{
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_58 = lean_array_get(x_54, x_2, x_6);
lean_inc(x_58);
x_59 = l___private_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_0__Lean_PrettyPrinter_Delaborator_TopDownAnalyze_valUnknown___redArg(x_58, x_11, x_55);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = lean_array_get(x_54, x_1, x_6);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_62);
x_63 = l_Lean_PrettyPrinter_Delaborator_isType2Type(x_62, x_10, x_11, x_12, x_13, x_61);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = l_Lean_PrettyPrinter_Delaborator_isFOLike___redArg(x_62, x_65);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = lean_ctor_get(x_12, 2);
lean_inc(x_69);
x_70 = l_Lean_getPPAnalyzeTrustKnownFOType2TypeHOFuns(x_69);
lean_dec(x_69);
if (x_70 == 0)
{
uint8_t x_71; uint8_t x_72; 
lean_dec(x_60);
x_71 = lean_unbox(x_64);
lean_dec(x_64);
x_72 = lean_unbox(x_67);
lean_dec(x_67);
x_42 = x_58;
x_43 = x_71;
x_44 = x_72;
x_45 = x_56;
x_46 = x_62;
x_47 = x_68;
x_48 = x_70;
goto block_49;
}
else
{
uint8_t x_73; 
x_73 = lean_unbox(x_60);
lean_dec(x_60);
if (x_73 == 0)
{
uint8_t x_74; uint8_t x_75; 
x_74 = lean_unbox(x_64);
lean_dec(x_64);
x_75 = lean_unbox(x_67);
lean_dec(x_67);
x_42 = x_58;
x_43 = x_74;
x_44 = x_75;
x_45 = x_56;
x_46 = x_62;
x_47 = x_68;
x_48 = x_70;
goto block_49;
}
else
{
lean_dec(x_67);
lean_dec(x_64);
x_23 = x_58;
x_24 = x_56;
x_25 = x_68;
x_26 = x_62;
goto block_41;
}
}
}
else
{
uint8_t x_76; 
lean_dec(x_62);
lean_dec(x_60);
lean_dec(x_58);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
x_76 = !lean_is_exclusive(x_63);
if (x_76 == 0)
{
return x_63;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_63, 0);
x_78 = lean_ctor_get(x_63, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_63);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
else
{
x_15 = x_22;
x_16 = x_7;
x_17 = x_55;
goto block_21;
}
}
block_105:
{
if (x_81 == 0)
{
x_15 = x_22;
x_16 = x_7;
x_17 = x_14;
goto block_21;
}
else
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_array_fget(x_1, x_6);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_83 = lean_infer_type(x_82, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_86 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHigherOrder(x_84, x_10, x_11, x_12, x_13, x_85);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; uint8_t x_88; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_unbox(x_87);
if (x_88 == 0)
{
lean_object* x_89; 
lean_dec(x_87);
x_89 = lean_ctor_get(x_86, 1);
lean_inc(x_89);
lean_dec(x_86);
x_15 = x_22;
x_16 = x_7;
x_17 = x_89;
goto block_21;
}
else
{
lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_90 = lean_ctor_get(x_86, 1);
lean_inc(x_90);
lean_dec(x_86);
x_91 = lean_ctor_get(x_12, 2);
lean_inc(x_91);
x_92 = l_Lean_getPPAnalyzeTrustId(x_91);
lean_dec(x_91);
if (x_92 == 0)
{
uint8_t x_93; 
x_93 = lean_unbox(x_87);
lean_dec(x_87);
x_55 = x_90;
x_56 = x_93;
x_57 = x_92;
goto block_80;
}
else
{
lean_object* x_94; uint8_t x_95; uint8_t x_96; 
x_94 = lean_array_get(x_54, x_1, x_6);
x_95 = l_Lean_PrettyPrinter_Delaborator_isIdLike(x_94);
lean_dec(x_94);
x_96 = lean_unbox(x_87);
lean_dec(x_87);
x_55 = x_90;
x_56 = x_96;
x_57 = x_95;
goto block_80;
}
}
}
else
{
uint8_t x_97; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
x_97 = !lean_is_exclusive(x_86);
if (x_97 == 0)
{
return x_86;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_86, 0);
x_99 = lean_ctor_get(x_86, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_86);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
else
{
uint8_t x_101; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
x_101 = !lean_is_exclusive(x_83);
if (x_101 == 0)
{
return x_83;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_83, 0);
x_103 = lean_ctor_get(x_83, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_83);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
}
}
}
}
block_21:
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_4, 2);
x_19 = lean_nat_add(x_6, x_18);
lean_dec(x_6);
x_5 = x_15;
x_6 = x_19;
x_7 = x_16;
x_14 = x_17;
goto _start;
}
block_41:
{
lean_object* x_27; 
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_27 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_tryUnify(x_26, x_23, x_8, x_9, x_10, x_11, x_12, x_13, x_25);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_ctor_get(x_7, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_7, 1);
lean_inc(x_30);
x_31 = lean_box(x_24);
x_32 = lean_array_set(x_30, x_6, x_31);
x_33 = lean_ctor_get(x_7, 2);
lean_inc(x_33);
x_34 = lean_ctor_get(x_7, 3);
lean_inc(x_34);
x_35 = lean_ctor_get(x_7, 4);
lean_inc(x_35);
lean_dec(x_7);
x_36 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_36, 0, x_29);
lean_ctor_set(x_36, 1, x_32);
lean_ctor_set(x_36, 2, x_33);
lean_ctor_set(x_36, 3, x_34);
lean_ctor_set(x_36, 4, x_35);
x_15 = x_22;
x_16 = x_36;
x_17 = x_28;
goto block_21;
}
else
{
uint8_t x_37; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
x_37 = !lean_is_exclusive(x_27);
if (x_37 == 0)
{
return x_27;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_27, 0);
x_39 = lean_ctor_get(x_27, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_27);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
block_49:
{
if (x_48 == 0)
{
x_23 = x_42;
x_24 = x_45;
x_25 = x_47;
x_26 = x_46;
goto block_41;
}
else
{
if (x_43 == 0)
{
x_23 = x_42;
x_24 = x_45;
x_25 = x_47;
x_26 = x_46;
goto block_41;
}
else
{
if (x_44 == 0)
{
x_23 = x_42;
x_24 = x_45;
x_25 = x_47;
x_26 = x_46;
goto block_41;
}
else
{
lean_dec(x_46);
lean_dec(x_42);
x_15 = x_22;
x_16 = x_7;
x_17 = x_47;
goto block_21;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectHigherOrders_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; 
x_18 = l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectHigherOrders_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectHigherOrders(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_10 = lean_ctor_get(x_1, 2);
x_11 = lean_ctor_get(x_1, 3);
x_12 = lean_ctor_get(x_1, 4);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_array_get_size(x_10);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_14);
lean_ctor_set(x_16, 2, x_15);
x_17 = lean_box(0);
x_18 = l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectHigherOrders_spec__0___redArg(x_10, x_11, x_12, x_16, x_17, x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_16);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
lean_ctor_set(x_20, 0, x_17);
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_17);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set(x_18, 0, x_24);
return x_18;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_18, 0);
x_26 = lean_ctor_get(x_18, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_18);
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
if (lean_is_scalar(x_28)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_28;
}
lean_ctor_set(x_29, 0, x_17);
lean_ctor_set(x_29, 1, x_27);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_26);
return x_30;
}
}
else
{
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectHigherOrders_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectHigherOrders_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectHigherOrders_spec__0___boxed(lean_object** _args) {
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
lean_object* x_18; 
x_18 = l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectHigherOrders_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectHigherOrders___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectHigherOrders(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_hBinOpHeuristic_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_hBinOpHeuristic_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_hBinOpHeuristic_spec__0___redArg(x_2, x_3, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_hBinOpHeuristic(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_38; lean_object* x_39; uint8_t x_44; 
x_10 = lean_ctor_get(x_1, 3);
x_11 = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_hBinOpHeuristic_spec__0___redArg(x_2, x_3, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_14 = x_11;
} else {
 lean_dec_ref(x_11);
 x_14 = lean_box(0);
}
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_17 = x_12;
} else {
 lean_dec_ref(x_12);
 x_17 = lean_box(0);
}
x_18 = l_Lean_instInhabitedExpr;
x_44 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp(x_15);
lean_dec(x_15);
if (x_44 == 0)
{
x_38 = x_44;
x_39 = x_13;
goto block_43;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_45 = lean_unsigned_to_nat(0u);
x_46 = lean_array_get(x_18, x_10, x_45);
x_47 = l___private_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_0__Lean_PrettyPrinter_Delaborator_TopDownAnalyze_valUnknown___redArg(x_46, x_6, x_13);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_unbox(x_48);
lean_dec(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
lean_dec(x_47);
x_51 = lean_unsigned_to_nat(1u);
x_52 = lean_array_get(x_18, x_10, x_51);
x_53 = l___private_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_0__Lean_PrettyPrinter_Delaborator_TopDownAnalyze_valUnknown___redArg(x_52, x_6, x_50);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_unbox(x_54);
lean_dec(x_54);
x_38 = x_56;
x_39 = x_55;
goto block_43;
}
else
{
lean_object* x_57; 
lean_dec(x_14);
x_57 = lean_ctor_get(x_47, 1);
lean_inc(x_57);
lean_dec(x_47);
x_19 = x_16;
x_20 = x_57;
goto block_37;
}
}
block_37:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_array_get(x_18, x_10, x_21);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_array_get(x_18, x_10, x_23);
x_25 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_tryUnify(x_22, x_24, x_3, x_4, x_5, x_6, x_7, x_8, x_20);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_25, 0);
if (lean_is_scalar(x_17)) {
 x_28 = lean_alloc_ctor(0, 2, 0);
} else {
 x_28 = x_17;
}
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_19);
lean_ctor_set(x_25, 0, x_28);
return x_25;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_25, 0);
x_30 = lean_ctor_get(x_25, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_25);
if (lean_is_scalar(x_17)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_17;
}
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_19);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_dec(x_19);
lean_dec(x_17);
x_33 = !lean_is_exclusive(x_25);
if (x_33 == 0)
{
return x_25;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_25, 0);
x_35 = lean_ctor_get(x_25, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_25);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
block_43:
{
if (x_38 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_16);
if (lean_is_scalar(x_14)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_14;
}
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_39);
return x_42;
}
else
{
lean_dec(x_14);
x_19 = x_16;
x_20 = x_39;
goto block_37;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_hBinOpHeuristic_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_hBinOpHeuristic_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_hBinOpHeuristic_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_hBinOpHeuristic_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_hBinOpHeuristic___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_hBinOpHeuristic(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectTrivialBottomUps_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_4, 1);
x_23 = lean_nat_dec_lt(x_6, x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_5);
lean_ctor_set(x_24, 1, x_7);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_14);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; 
lean_dec(x_5);
x_26 = lean_box(0);
x_27 = lean_box(0);
x_28 = lean_array_get(x_27, x_1, x_6);
x_29 = lean_unbox(x_28);
lean_dec(x_28);
x_30 = lean_unbox(x_27);
x_31 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(x_29, x_30);
if (x_31 == 0)
{
x_15 = x_26;
x_16 = x_7;
x_17 = x_14;
goto block_21;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_32 = l_Lean_instInhabitedExpr;
x_33 = lean_array_get(x_32, x_2, x_6);
lean_inc(x_33);
x_34 = l___private_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_0__Lean_PrettyPrinter_Delaborator_TopDownAnalyze_valUnknown___redArg(x_33, x_11, x_14);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_unbox(x_35);
lean_dec(x_35);
if (x_36 == 0)
{
lean_object* x_37; 
lean_dec(x_33);
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_dec(x_34);
x_15 = x_26;
x_16 = x_7;
x_17 = x_37;
goto block_21;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_38 = lean_ctor_get(x_34, 1);
lean_inc(x_38);
lean_dec(x_34);
x_39 = lean_array_fget(x_3, x_6);
x_40 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isTrivialBottomUp___redArg(x_39, x_12, x_38);
lean_dec(x_39);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_unbox(x_41);
if (x_42 == 0)
{
lean_object* x_43; 
lean_dec(x_41);
lean_dec(x_33);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec(x_40);
x_15 = x_26;
x_16 = x_7;
x_17 = x_43;
goto block_21;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_40, 1);
lean_inc(x_44);
lean_dec(x_40);
x_45 = lean_array_get(x_32, x_3, x_6);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_46 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_tryUnify(x_45, x_33, x_8, x_9, x_10, x_11, x_12, x_13, x_44);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
x_48 = lean_ctor_get(x_7, 0);
lean_inc(x_48);
x_49 = lean_array_set(x_48, x_6, x_41);
x_50 = lean_ctor_get(x_7, 1);
lean_inc(x_50);
x_51 = lean_ctor_get(x_7, 2);
lean_inc(x_51);
x_52 = lean_ctor_get(x_7, 3);
lean_inc(x_52);
x_53 = lean_ctor_get(x_7, 4);
lean_inc(x_53);
lean_dec(x_7);
x_54 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_54, 0, x_49);
lean_ctor_set(x_54, 1, x_50);
lean_ctor_set(x_54, 2, x_51);
lean_ctor_set(x_54, 3, x_52);
lean_ctor_set(x_54, 4, x_53);
x_15 = x_26;
x_16 = x_54;
x_17 = x_47;
goto block_21;
}
else
{
uint8_t x_55; 
lean_dec(x_41);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
x_55 = !lean_is_exclusive(x_46);
if (x_55 == 0)
{
return x_46;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_46, 0);
x_57 = lean_ctor_get(x_46, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_46);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
}
}
}
block_21:
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_4, 2);
x_19 = lean_nat_add(x_6, x_18);
lean_dec(x_6);
x_5 = x_15;
x_6 = x_19;
x_7 = x_16;
x_14 = x_17;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectTrivialBottomUps_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; 
x_18 = l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectTrivialBottomUps_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectTrivialBottomUps(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_10 = lean_ctor_get(x_1, 2);
x_11 = lean_ctor_get(x_1, 3);
x_12 = lean_ctor_get(x_1, 4);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_array_get_size(x_10);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_14);
lean_ctor_set(x_16, 2, x_15);
x_17 = lean_box(0);
x_18 = l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectTrivialBottomUps_spec__0___redArg(x_12, x_11, x_10, x_16, x_17, x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_16);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
lean_ctor_set(x_20, 0, x_17);
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_17);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set(x_18, 0, x_24);
return x_18;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_18, 0);
x_26 = lean_ctor_get(x_18, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_18);
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
if (lean_is_scalar(x_28)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_28;
}
lean_ctor_set(x_29, 0, x_17);
lean_ctor_set(x_29, 1, x_27);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_26);
return x_30;
}
}
else
{
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectTrivialBottomUps_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectTrivialBottomUps_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectTrivialBottomUps_spec__0___boxed(lean_object** _args) {
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
lean_object* x_18; 
x_18 = l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectTrivialBottomUps_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectTrivialBottomUps___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectTrivialBottomUps(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = lean_apply_9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core_spec__0___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core_spec__0___redArg___lam__0), 10, 5);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_3);
lean_closure_set(x_12, 2, x_4);
lean_closure_set(x_12, 3, x_5);
lean_closure_set(x_12, 4, x_6);
x_13 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp___redArg(x_2, x_12, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core_spec__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_withNewMCtxDepth___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core_spec__1___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_checkpointDefEq(x_1, x_2, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_4);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_12, 0);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_12);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_4);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
uint8_t x_20; 
lean_dec(x_4);
x_20 = !lean_is_exclusive(x_12);
if (x_20 == 0)
{
return x_12;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_12, 0);
x_22 = lean_ctor_get(x_12, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_12);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_5, 1);
x_25 = lean_nat_dec_lt(x_7, x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_26 = lean_box(x_6);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_9);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_16);
return x_28;
}
else
{
lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; uint8_t x_71; uint8_t x_72; 
x_29 = l_Lean_instInhabitedExpr;
x_67 = lean_box(0);
x_68 = lean_array_get(x_67, x_3, x_7);
x_69 = lean_unbox(x_68);
lean_dec(x_68);
x_70 = lean_box(1);
x_71 = lean_unbox(x_70);
x_72 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(x_69, x_71);
if (x_72 == 0)
{
x_30 = x_72;
x_31 = x_9;
x_32 = x_16;
goto block_66;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_73 = lean_array_get(x_29, x_2, x_7);
lean_inc(x_73);
x_74 = l___private_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_0__Lean_PrettyPrinter_Delaborator_TopDownAnalyze_valUnknown___redArg(x_73, x_13, x_16);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_unbox(x_75);
lean_dec(x_75);
if (x_76 == 0)
{
lean_object* x_77; 
lean_dec(x_73);
x_77 = lean_ctor_get(x_74, 1);
lean_inc(x_77);
lean_dec(x_74);
x_17 = x_6;
x_18 = x_9;
x_19 = x_77;
goto block_23;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; 
x_78 = lean_ctor_get(x_74, 1);
lean_inc(x_78);
lean_dec(x_74);
x_79 = lean_box(0);
lean_inc(x_4);
x_80 = lean_alloc_closure((void*)(l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core_spec__1___redArg___lam__0___boxed), 11, 2);
lean_closure_set(x_80, 0, x_4);
lean_closure_set(x_80, 1, x_73);
x_81 = lean_unbox(x_79);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_8);
x_82 = l_Lean_Meta_withNewMCtxDepth___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core_spec__0___redArg(x_80, x_81, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_78);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = lean_ctor_get(x_83, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_83, 1);
lean_inc(x_86);
lean_dec(x_83);
x_87 = lean_unbox(x_85);
lean_dec(x_85);
x_30 = x_87;
x_31 = x_86;
x_32 = x_84;
goto block_66;
}
else
{
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
return x_82;
}
}
}
block_66:
{
if (x_30 == 0)
{
x_17 = x_6;
x_18 = x_31;
x_19 = x_32;
goto block_23;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
lean_dec(x_8);
lean_dec(x_4);
x_33 = lean_mk_string_unchecked("pp", 2, 2);
x_34 = lean_mk_string_unchecked("funBinderTypes", 14, 14);
x_35 = l_Lean_Name_mkStr2(x_33, x_34);
x_36 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBool(x_35, x_10, x_11, x_12, x_13, x_14, x_15, x_32);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_36, 1);
x_39 = lean_ctor_get(x_36, 0);
lean_dec(x_39);
x_40 = lean_array_get(x_29, x_1, x_7);
x_41 = lean_array_get(x_29, x_2, x_7);
lean_dec(x_7);
x_42 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_tryUnify(x_40, x_41, x_10, x_11, x_12, x_13, x_14, x_15, x_38);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
if (lean_obj_tag(x_42) == 0)
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_42, 0);
lean_dec(x_44);
x_45 = lean_box(x_30);
lean_ctor_set(x_36, 1, x_31);
lean_ctor_set(x_36, 0, x_45);
lean_ctor_set(x_42, 0, x_36);
return x_42;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_42, 1);
lean_inc(x_46);
lean_dec(x_42);
x_47 = lean_box(x_30);
lean_ctor_set(x_36, 1, x_31);
lean_ctor_set(x_36, 0, x_47);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_36);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
else
{
uint8_t x_49; 
lean_free_object(x_36);
lean_dec(x_31);
x_49 = !lean_is_exclusive(x_42);
if (x_49 == 0)
{
return x_42;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_42, 0);
x_51 = lean_ctor_get(x_42, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_42);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_36, 1);
lean_inc(x_53);
lean_dec(x_36);
x_54 = lean_array_get(x_29, x_1, x_7);
x_55 = lean_array_get(x_29, x_2, x_7);
lean_dec(x_7);
x_56 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_tryUnify(x_54, x_55, x_10, x_11, x_12, x_13, x_14, x_15, x_53);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_58 = x_56;
} else {
 lean_dec_ref(x_56);
 x_58 = lean_box(0);
}
x_59 = lean_box(x_30);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_31);
if (lean_is_scalar(x_58)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_58;
}
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_57);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_31);
x_62 = lean_ctor_get(x_56, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_56, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_64 = x_56;
} else {
 lean_dec_ref(x_56);
 x_64 = lean_box(0);
}
if (lean_is_scalar(x_64)) {
 x_65 = lean_alloc_ctor(1, 2, 0);
} else {
 x_65 = x_64;
}
lean_ctor_set(x_65, 0, x_62);
lean_ctor_set(x_65, 1, x_63);
return x_65;
}
}
}
}
}
block_23:
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_5, 2);
x_21 = lean_nat_add(x_7, x_20);
lean_dec(x_7);
x_6 = x_17;
x_7 = x_21;
x_9 = x_18;
x_16 = x_19;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
lean_object* x_19; 
x_19 = l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core_spec__2_spec__2_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_13 = lean_ctor_get_uint8(x_6, sizeof(void*)*1);
x_14 = lean_ctor_get_uint8(x_6, sizeof(void*)*1 + 1);
x_15 = lean_ctor_get_uint8(x_6, sizeof(void*)*1 + 2);
x_16 = lean_ctor_get_uint8(x_6, sizeof(void*)*1 + 3);
x_17 = lean_ctor_get(x_6, 0);
x_18 = lean_ctor_get(x_17, 1);
x_19 = l_Lean_SubExpr_Pos_push(x_18, x_2);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set_uint8(x_21, sizeof(void*)*1, x_13);
lean_ctor_set_uint8(x_21, sizeof(void*)*1 + 1, x_14);
lean_ctor_set_uint8(x_21, sizeof(void*)*1 + 2, x_15);
lean_ctor_set_uint8(x_21, sizeof(void*)*1 + 3, x_16);
x_22 = lean_apply_9(x_3, x_4, x_5, x_21, x_7, x_8, x_9, x_10, x_11, x_12);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core_spec__2_spec__2_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core_spec__2_spec__2_spec__2___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core_spec__2_spec__2_spec__3___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = lean_apply_10(x_1, x_6, x_2, x_3, x_4, x_5, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core_spec__2_spec__2_spec__3___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core_spec__2_spec__2_spec__3___redArg___lam__0), 11, 5);
lean_closure_set(x_15, 0, x_4);
lean_closure_set(x_15, 1, x_6);
lean_closure_set(x_15, 2, x_7);
lean_closure_set(x_15, 3, x_8);
lean_closure_set(x_15, 4, x_9);
x_16 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), x_1, x_2, x_3, x_15, x_5, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
return x_16;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_16);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_16);
if (x_21 == 0)
{
return x_16;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_16, 0);
x_23 = lean_ctor_get(x_16, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_16);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core_spec__2_spec__2_spec__3(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_Meta_withLocalDecl___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core_spec__2_spec__2_spec__3___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core_spec__2_spec__2___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_4);
x_14 = lean_apply_10(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
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
x_19 = l_Lean_Expr_bindingBody_x21(x_2);
x_20 = lean_expr_instantiate1(x_19, x_4);
lean_dec(x_4);
lean_dec(x_19);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_apply_1(x_3, x_17);
x_23 = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core_spec__2_spec__2_spec__2___redArg(x_20, x_21, x_22, x_5, x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_16);
lean_dec(x_7);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core_spec__2_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_13 = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_hBinOpHeuristic_spec__0___redArg(x_5, x_6, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
lean_inc(x_16);
x_18 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core_spec__2_spec__2___redArg___lam__0___boxed), 13, 3);
lean_closure_set(x_18, 0, x_2);
lean_closure_set(x_18, 1, x_16);
lean_closure_set(x_18, 2, x_3);
x_19 = l_Lean_Expr_binderInfo(x_16);
x_20 = l_Lean_Expr_bindingDomain_x21(x_16);
lean_dec(x_16);
x_21 = lean_box(0);
x_22 = lean_unbox(x_21);
x_23 = l_Lean_Meta_withLocalDecl___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core_spec__2_spec__2_spec__3___redArg(x_1, x_19, x_20, x_18, x_22, x_4, x_17, x_6, x_7, x_8, x_9, x_10, x_11, x_15);
return x_23;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core_spec__2_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core_spec__2_spec__2___redArg(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core_spec__2___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = lean_apply_9(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core_spec__2___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_3);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core_spec__2___redArg___lam__0___boxed), 11, 1);
lean_closure_set(x_12, 0, x_2);
x_13 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core_spec__2___redArg___lam__1___boxed), 10, 0);
x_14 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core_spec__2_spec__2___redArg(x_1, x_13, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core_spec__2___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_4);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_hBinOpHeuristic_spec__0___redArg(x_7, x_8, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 6)
{
if (lean_obj_tag(x_5) == 7)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
lean_dec(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_ctor_get(x_5, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_5, 2);
lean_inc(x_21);
lean_dec(x_5);
x_22 = lean_box(0);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_unsigned_to_nat(1u);
lean_inc(x_4);
x_25 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_4);
lean_ctor_set(x_25, 2, x_24);
x_26 = lean_unbox(x_22);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
x_27 = l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core_spec__1___redArg(x_1, x_2, x_3, x_20, x_25, x_26, x_23, x_6, x_19, x_8, x_9, x_10, x_11, x_12, x_13, x_18);
lean_dec(x_25);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_box(0);
x_33 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core), 14, 5);
lean_closure_set(x_33, 0, x_1);
lean_closure_set(x_33, 1, x_2);
lean_closure_set(x_33, 2, x_3);
lean_closure_set(x_33, 3, x_4);
lean_closure_set(x_33, 4, x_21);
x_34 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core_spec__2___redArg(x_32, x_33, x_6, x_31, x_8, x_9, x_10, x_11, x_12, x_13, x_29);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_46; 
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
x_38 = lean_ctor_get(x_35, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_35, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_40 = x_35;
} else {
 lean_dec_ref(x_35);
 x_40 = lean_box(0);
}
x_46 = lean_unbox(x_30);
if (x_46 == 0)
{
uint8_t x_47; 
lean_dec(x_30);
x_47 = lean_unbox(x_38);
lean_dec(x_38);
x_41 = x_47;
goto block_45;
}
else
{
uint8_t x_48; 
lean_dec(x_38);
x_48 = lean_unbox(x_30);
lean_dec(x_30);
x_41 = x_48;
goto block_45;
}
block_45:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_box(x_41);
if (lean_is_scalar(x_40)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_40;
}
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_39);
if (lean_is_scalar(x_37)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_37;
}
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_36);
return x_44;
}
}
else
{
lean_dec(x_30);
return x_34;
}
}
else
{
lean_dec(x_21);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_27;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_49 = lean_ctor_get(x_15, 1);
lean_inc(x_49);
lean_dec(x_15);
x_50 = lean_ctor_get(x_16, 1);
lean_inc(x_50);
lean_dec(x_16);
x_51 = lean_ctor_get(x_17, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_17, 1);
lean_inc(x_52);
x_53 = lean_ctor_get(x_17, 2);
lean_inc(x_53);
x_54 = lean_ctor_get_uint8(x_17, sizeof(void*)*3 + 8);
lean_dec(x_17);
x_55 = l_Lean_Expr_lam___override(x_51, x_52, x_53, x_54);
x_56 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core___lam__0(x_55, x_5, x_6, x_50, x_8, x_9, x_10, x_11, x_12, x_13, x_49);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_55);
return x_56;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_57 = lean_ctor_get(x_15, 1);
lean_inc(x_57);
lean_dec(x_15);
x_58 = lean_ctor_get(x_16, 1);
lean_inc(x_58);
lean_dec(x_16);
x_59 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core___lam__0(x_17, x_5, x_6, x_58, x_8, x_9, x_10, x_11, x_12, x_13, x_57);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_17);
return x_59;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = l_Lean_Meta_withNewMCtxDepth___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core_spec__0___redArg(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_3);
lean_dec(x_3);
x_14 = l_Lean_Meta_withNewMCtxDepth___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core_spec__0(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core_spec__1___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core_spec__1___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; lean_object* x_18; 
x_17 = lean_unbox(x_6);
lean_dec(x_6);
x_18 = l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core_spec__1___boxed(lean_object** _args) {
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
uint8_t x_19; lean_object* x_20; 
x_19 = lean_unbox(x_6);
lean_dec(x_6);
x_20 = l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core_spec__1(x_1, x_2, x_3, x_4, x_5, x_19, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core_spec__2_spec__2_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core_spec__2_spec__2_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_6);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core_spec__2_spec__2_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core_spec__2_spec__2_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_7);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core_spec__2_spec__2_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; uint8_t x_16; lean_object* x_17; 
x_15 = lean_unbox(x_2);
lean_dec(x_2);
x_16 = lean_unbox(x_5);
lean_dec(x_5);
x_17 = l_Lean_Meta_withLocalDecl___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core_spec__2_spec__2_spec__3___redArg(x_1, x_15, x_3, x_4, x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core_spec__2_spec__2_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_unbox(x_3);
lean_dec(x_3);
x_17 = lean_unbox(x_6);
lean_dec(x_6);
x_18 = l_Lean_Meta_withLocalDecl___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core_spec__2_spec__2_spec__3(x_1, x_2, x_16, x_4, x_5, x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core_spec__2_spec__2___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core_spec__2_spec__2___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core_spec__2___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core_spec__2___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core_spec__2___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core_spec__2___redArg___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_spec__0_spec__0___redArg(x_2, x_3, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_12 = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_hBinOpHeuristic_spec__0___redArg(x_4, x_5, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_box(0);
x_18 = l_Lean_Expr_sort___override(x_17);
x_19 = l_Lean_Expr_getAppNumArgs(x_15);
x_20 = lean_unsigned_to_nat(1u);
x_21 = l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_spec__0_spec__0___redArg(x_16, x_5, x_14);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_25 = lean_ctor_get(x_22, 0);
x_26 = lean_ctor_get(x_22, 1);
lean_inc(x_19);
x_27 = lean_mk_array(x_19, x_18);
x_28 = lean_nat_sub(x_19, x_20);
lean_dec(x_19);
x_29 = l_Lean_instInhabitedExpr;
x_30 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_15, x_27, x_28);
x_31 = lean_array_get_size(x_30);
x_32 = l_Lean_SubExpr_Pos_pushNaryArg(x_31, x_1, x_25);
lean_dec(x_25);
lean_dec(x_31);
x_33 = lean_ctor_get_uint8(x_5, sizeof(void*)*1);
x_34 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 1);
x_35 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 2);
x_36 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 3);
x_37 = lean_array_get(x_29, x_30, x_1);
lean_dec(x_30);
lean_ctor_set(x_22, 1, x_32);
lean_ctor_set(x_22, 0, x_37);
x_38 = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(x_38, 0, x_22);
lean_ctor_set_uint8(x_38, sizeof(void*)*1, x_33);
lean_ctor_set_uint8(x_38, sizeof(void*)*1 + 1, x_34);
lean_ctor_set_uint8(x_38, sizeof(void*)*1 + 2, x_35);
lean_ctor_set_uint8(x_38, sizeof(void*)*1 + 3, x_36);
x_39 = lean_apply_9(x_2, x_3, x_26, x_38, x_6, x_7, x_8, x_9, x_10, x_23);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_40 = lean_ctor_get(x_22, 0);
x_41 = lean_ctor_get(x_22, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_22);
lean_inc(x_19);
x_42 = lean_mk_array(x_19, x_18);
x_43 = lean_nat_sub(x_19, x_20);
lean_dec(x_19);
x_44 = l_Lean_instInhabitedExpr;
x_45 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_15, x_42, x_43);
x_46 = lean_array_get_size(x_45);
x_47 = l_Lean_SubExpr_Pos_pushNaryArg(x_46, x_1, x_40);
lean_dec(x_40);
lean_dec(x_46);
x_48 = lean_ctor_get_uint8(x_5, sizeof(void*)*1);
x_49 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 1);
x_50 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 2);
x_51 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 3);
x_52 = lean_array_get(x_44, x_45, x_1);
lean_dec(x_45);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_47);
x_54 = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set_uint8(x_54, sizeof(void*)*1, x_48);
lean_ctor_set_uint8(x_54, sizeof(void*)*1 + 1, x_49);
lean_ctor_set_uint8(x_54, sizeof(void*)*1 + 2, x_50);
lean_ctor_set_uint8(x_54, sizeof(void*)*1 + 3, x_51);
x_55 = lean_apply_9(x_2, x_3, x_41, x_54, x_6, x_7, x_8, x_9, x_10, x_23);
return x_55;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_spec__2_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_4, 1);
x_24 = lean_nat_dec_lt(x_6, x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_5);
lean_ctor_set(x_25, 1, x_8);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_15);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; 
lean_dec(x_5);
x_27 = lean_box(0);
x_28 = lean_box(0);
x_29 = lean_array_get(x_27, x_1, x_6);
x_30 = lean_unbox(x_29);
lean_dec(x_29);
x_31 = lean_unbox(x_27);
x_32 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(x_30, x_31);
if (x_32 == 0)
{
x_16 = x_28;
x_17 = x_8;
x_18 = x_15;
goto block_22;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = l_Lean_instInhabitedExpr;
x_34 = lean_array_get(x_33, x_2, x_6);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_35 = lean_infer_type(x_34, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
lean_inc(x_6);
lean_inc(x_1);
lean_inc(x_2);
lean_inc(x_3);
x_38 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core), 14, 5);
lean_closure_set(x_38, 0, x_3);
lean_closure_set(x_38, 1, x_2);
lean_closure_set(x_38, 2, x_1);
lean_closure_set(x_38, 3, x_6);
lean_closure_set(x_38, 4, x_36);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_7);
x_39 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_spec__0___redArg(x_6, x_38, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_37);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_unbox(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_41);
x_43 = lean_ctor_get(x_39, 1);
lean_inc(x_43);
lean_dec(x_39);
x_44 = lean_ctor_get(x_40, 1);
lean_inc(x_44);
lean_dec(x_40);
x_16 = x_28;
x_17 = x_44;
x_18 = x_43;
goto block_22;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_45 = lean_ctor_get(x_39, 1);
lean_inc(x_45);
lean_dec(x_39);
x_46 = lean_ctor_get(x_40, 1);
lean_inc(x_46);
lean_dec(x_40);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
x_49 = lean_ctor_get(x_46, 2);
lean_inc(x_49);
x_50 = lean_array_set(x_49, x_6, x_41);
x_51 = lean_ctor_get(x_46, 3);
lean_inc(x_51);
x_52 = lean_ctor_get(x_46, 4);
lean_inc(x_52);
lean_dec(x_46);
x_53 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_53, 0, x_47);
lean_ctor_set(x_53, 1, x_48);
lean_ctor_set(x_53, 2, x_50);
lean_ctor_set(x_53, 3, x_51);
lean_ctor_set(x_53, 4, x_52);
x_16 = x_28;
x_17 = x_53;
x_18 = x_45;
goto block_22;
}
}
else
{
uint8_t x_54; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_39);
if (x_54 == 0)
{
return x_39;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_39, 0);
x_56 = lean_ctor_get(x_39, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_39);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_35);
if (x_58 == 0)
{
return x_35;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_35, 0);
x_60 = lean_ctor_get(x_35, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_35);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
}
block_22:
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_4, 2);
x_20 = lean_nat_add(x_6, x_19);
lean_dec(x_6);
x_5 = x_16;
x_6 = x_20;
x_8 = x_17;
x_15 = x_18;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_spec__2_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; 
x_18 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_spec__2_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_4, 1);
x_24 = lean_nat_dec_lt(x_6, x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_5);
lean_ctor_set(x_25, 1, x_8);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_15);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; 
lean_dec(x_5);
x_27 = lean_box(0);
x_28 = lean_box(0);
x_29 = lean_array_get(x_27, x_1, x_6);
x_30 = lean_unbox(x_29);
lean_dec(x_29);
x_31 = lean_unbox(x_27);
x_32 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(x_30, x_31);
if (x_32 == 0)
{
x_16 = x_28;
x_17 = x_8;
x_18 = x_15;
goto block_22;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = l_Lean_instInhabitedExpr;
x_34 = lean_array_get(x_33, x_2, x_6);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_35 = lean_infer_type(x_34, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
lean_inc(x_6);
lean_inc(x_1);
lean_inc(x_2);
lean_inc(x_3);
x_38 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core), 14, 5);
lean_closure_set(x_38, 0, x_3);
lean_closure_set(x_38, 1, x_2);
lean_closure_set(x_38, 2, x_1);
lean_closure_set(x_38, 3, x_6);
lean_closure_set(x_38, 4, x_36);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_7);
x_39 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_spec__0___redArg(x_6, x_38, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_37);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_unbox(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_41);
x_43 = lean_ctor_get(x_39, 1);
lean_inc(x_43);
lean_dec(x_39);
x_44 = lean_ctor_get(x_40, 1);
lean_inc(x_44);
lean_dec(x_40);
x_16 = x_28;
x_17 = x_44;
x_18 = x_43;
goto block_22;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_45 = lean_ctor_get(x_39, 1);
lean_inc(x_45);
lean_dec(x_39);
x_46 = lean_ctor_get(x_40, 1);
lean_inc(x_46);
lean_dec(x_40);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
x_49 = lean_ctor_get(x_46, 2);
lean_inc(x_49);
x_50 = lean_array_set(x_49, x_6, x_41);
x_51 = lean_ctor_get(x_46, 3);
lean_inc(x_51);
x_52 = lean_ctor_get(x_46, 4);
lean_inc(x_52);
lean_dec(x_46);
x_53 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_53, 0, x_47);
lean_ctor_set(x_53, 1, x_48);
lean_ctor_set(x_53, 2, x_50);
lean_ctor_set(x_53, 3, x_51);
lean_ctor_set(x_53, 4, x_52);
x_16 = x_28;
x_17 = x_53;
x_18 = x_45;
goto block_22;
}
}
else
{
uint8_t x_54; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_39);
if (x_54 == 0)
{
return x_39;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_39, 0);
x_56 = lean_ctor_get(x_39, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_39);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_35);
if (x_58 == 0)
{
return x_35;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_35, 0);
x_60 = lean_ctor_get(x_35, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_35);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
}
block_22:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_4, 2);
x_20 = lean_nat_add(x_6, x_19);
lean_dec(x_6);
x_21 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_spec__2_spec__2___redArg(x_1, x_2, x_3, x_4, x_16, x_20, x_7, x_17, x_9, x_10, x_11, x_12, x_13, x_14, x_18);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; 
x_18 = l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 3);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 4);
lean_inc(x_12);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_array_get_size(x_10);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_14);
lean_ctor_set(x_16, 2, x_15);
x_17 = lean_box(0);
x_18 = l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_spec__2___redArg(x_12, x_11, x_10, x_16, x_17, x_13, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_16);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
lean_ctor_set(x_20, 0, x_17);
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_17);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set(x_18, 0, x_24);
return x_18;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_18, 0);
x_26 = lean_ctor_get(x_18, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_18);
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
if (lean_is_scalar(x_28)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_28;
}
lean_ctor_set(x_29, 0, x_17);
lean_ctor_set(x_29, 1, x_27);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_26);
return x_30;
}
}
else
{
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_spec__0_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_6);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_spec__2_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_spec__2_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_9);
lean_dec(x_4);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_spec__2_spec__2___boxed(lean_object** _args) {
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
lean_object* x_18; 
x_18 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_spec__2_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_11);
lean_dec(x_4);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_9);
lean_dec(x_4);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_spec__2___boxed(lean_object** _args) {
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
lean_object* x_18; 
x_18 = l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_11);
lean_dec(x_4);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_maybeAddBlockImplicit_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_maybeAddBlockImplicit_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_maybeAddBlockImplicit_spec__0___redArg(x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_maybeAddBlockImplicit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_maybeAddBlockImplicit_spec__0___redArg(x_1, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_12 = lean_infer_type(x_10, x_3, x_4, x_5, x_6, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_25; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_15 = x_12;
} else {
 lean_dec_ref(x_12);
 x_15 = lean_box(0);
}
x_25 = l_Lean_Expr_isForall(x_13);
if (x_25 == 0)
{
lean_dec(x_13);
x_16 = x_25;
goto block_24;
}
else
{
uint8_t x_26; lean_object* x_27; uint8_t x_28; uint8_t x_29; 
x_26 = l_Lean_Expr_bindingInfo_x21(x_13);
lean_dec(x_13);
x_27 = lean_box(1);
x_28 = lean_unbox(x_27);
x_29 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(x_26, x_28);
x_16 = x_29;
goto block_24;
}
block_24:
{
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_17 = lean_box(0);
if (lean_is_scalar(x_15)) {
 x_18 = lean_alloc_ctor(0, 2, 0);
} else {
 x_18 = x_15;
}
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_14);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_15);
x_19 = lean_mk_string_unchecked("pp", 2, 2);
x_20 = lean_mk_string_unchecked("analysis", 8, 8);
x_21 = lean_mk_string_unchecked("blockImplicit", 13, 13);
x_22 = l_Lean_Name_mkStr3(x_19, x_20, x_21);
x_23 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBool(x_22, x_1, x_2, x_3, x_4, x_5, x_6, x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_23;
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_30 = !lean_is_exclusive(x_12);
if (x_30 == 0)
{
return x_12;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_12, 0);
x_32 = lean_ctor_get(x_12, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_12);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_7);
return x_35;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_maybeAddBlockImplicit_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_maybeAddBlockImplicit_spec__0___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_maybeAddBlockImplicit_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_maybeAddBlockImplicit_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_maybeAddBlockImplicit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_maybeAddBlockImplicit(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeFVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_maybeAddBlockImplicit(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeFVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeFVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeSort___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeSort(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeSort___redArg(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeSort___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeSort(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst_spec__0___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__0___boxed), 7, 0);
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__1), 9, 0);
x_11 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__0___boxed), 5, 0);
x_12 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__1), 7, 0);
x_13 = l_instMonadEIO(lean_box(0));
x_14 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
lean_inc(x_16);
x_17 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_17, 0, x_16);
x_18 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_18, 0, x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_closure((void*)(l_instMonadEIO___lam__1), 5, 0);
x_21 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_21, 0, x_20);
x_22 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_22, 0, x_21);
x_23 = lean_alloc_closure((void*)(l_instMonadEIO___lam__2), 5, 0);
x_24 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_24, 0, x_23);
x_25 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_25, 0, x_24);
x_26 = lean_alloc_closure((void*)(l_EStateM_seqRight), 7, 2);
lean_closure_set(x_26, 0, lean_box(0));
lean_closure_set(x_26, 1, lean_box(0));
x_27 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_27, 0, x_26);
x_28 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_28, 0, x_27);
lean_inc(x_28);
lean_inc(x_25);
lean_inc(x_22);
x_29 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_29, 0, x_19);
lean_ctor_set(x_29, 1, x_11);
lean_ctor_set(x_29, 2, x_22);
lean_ctor_set(x_29, 3, x_25);
lean_ctor_set(x_29, 4, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_12);
x_31 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_30);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec(x_32);
lean_inc(x_33);
x_34 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_34, 0, x_33);
x_35 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_35, 0, x_33);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_37, 0, x_22);
x_38 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_38, 0, x_37);
x_39 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_39, 0, x_25);
x_40 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_40, 0, x_39);
x_41 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_41, 0, x_28);
x_42 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_42, 0, x_41);
x_43 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_43, 0, x_36);
lean_ctor_set(x_43, 1, x_9);
lean_ctor_set(x_43, 2, x_38);
lean_ctor_set(x_43, 3, x_40);
lean_ctor_set(x_43, 4, x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_10);
x_45 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_44);
x_46 = lean_box(0);
x_47 = l_instInhabitedOfMonad___redArg(x_45, x_46);
x_48 = lean_alloc_closure((void*)(l_panic___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst_spec__0___lam__0___boxed), 2, 1);
lean_closure_set(x_48, 0, x_47);
x_49 = lean_panic_fn(x_48, x_1);
x_50 = lean_apply_7(x_49, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_50;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_maybeAddBlockImplicit_spec__0___redArg(x_1, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
if (lean_obj_tag(x_9) == 4)
{
uint8_t x_20; 
x_20 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 1);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_9, 1);
lean_inc(x_21);
lean_dec(x_9);
x_22 = l_List_isEmpty___redArg(x_21);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_5, 2);
lean_inc(x_23);
x_24 = l_Lean_getPPAnalyzeOmitMax(x_23);
lean_dec(x_23);
if (x_24 == 0)
{
lean_dec(x_21);
x_11 = x_24;
goto block_19;
}
else
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_containsBadMax___boxed), 1, 0);
x_26 = l_List_any___redArg(x_21, x_25);
x_11 = x_26;
goto block_19;
}
}
else
{
lean_object* x_27; 
lean_dec(x_21);
x_27 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_maybeAddBlockImplicit(x_1, x_2, x_3, x_4, x_5, x_6, x_10);
lean_dec(x_2);
lean_dec(x_1);
return x_27;
}
}
else
{
lean_object* x_28; 
lean_dec(x_9);
x_28 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_maybeAddBlockImplicit(x_1, x_2, x_3, x_4, x_5, x_6, x_10);
lean_dec(x_2);
lean_dec(x_1);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_9);
x_29 = lean_mk_string_unchecked("Lean.PrettyPrinter.Delaborator.TopDownAnalyze", 45, 45);
x_30 = lean_mk_string_unchecked("Lean.PrettyPrinter.Delaborator.TopDownAnalyze.analyze.analyzeConst", 66, 66);
x_31 = lean_unsigned_to_nat(441u);
x_32 = lean_unsigned_to_nat(41u);
x_33 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_34 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_29, x_30, x_31, x_32, x_33);
lean_dec(x_33);
lean_dec(x_30);
lean_dec(x_29);
x_35 = l_panic___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst_spec__0(x_34, x_1, x_2, x_3, x_4, x_5, x_6, x_10);
return x_35;
}
block_19:
{
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_mk_string_unchecked("pp", 2, 2);
x_13 = lean_mk_string_unchecked("universes", 9, 9);
x_14 = l_Lean_Name_mkStr2(x_12, x_13);
x_15 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBool(x_14, x_1, x_2, x_3, x_4, x_5, x_6, x_10);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_maybeAddBlockImplicit(x_1, x_2, x_3, x_4, x_5, x_6, x_16);
lean_dec(x_2);
lean_dec(x_1);
return x_17;
}
else
{
lean_object* x_18; 
x_18 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_maybeAddBlockImplicit(x_1, x_2, x_3, x_4, x_5, x_6, x_10);
lean_dec(x_2);
lean_dec(x_1);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_panic___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst_spec__0___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_annotateNamedArg___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_mk_string_unchecked("pp", 2, 2);
x_11 = lean_mk_string_unchecked("analysis", 8, 8);
x_12 = lean_mk_string_unchecked("namedArg", 8, 8);
x_13 = l_Lean_Name_mkStr3(x_10, x_11, x_12);
x_14 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBool(x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
x_17 = lean_box(0);
x_18 = lean_ctor_get(x_2, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_2, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_2, 2);
lean_inc(x_20);
x_21 = lean_ctor_get(x_2, 3);
lean_inc(x_21);
x_22 = lean_ctor_get(x_2, 4);
lean_inc(x_22);
lean_dec(x_2);
x_23 = lean_array_push(x_22, x_1);
x_24 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_24, 0, x_18);
lean_ctor_set(x_24, 1, x_19);
lean_ctor_set(x_24, 2, x_20);
lean_ctor_set(x_24, 3, x_21);
lean_ctor_set(x_24, 4, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_17);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_14, 0, x_25);
return x_14;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_26 = lean_ctor_get(x_14, 1);
lean_inc(x_26);
lean_dec(x_14);
x_27 = lean_box(0);
x_28 = lean_ctor_get(x_2, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_2, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_2, 2);
lean_inc(x_30);
x_31 = lean_ctor_get(x_2, 3);
lean_inc(x_31);
x_32 = lean_ctor_get(x_2, 4);
lean_inc(x_32);
lean_dec(x_2);
x_33 = lean_array_push(x_32, x_1);
x_34 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_34, 0, x_28);
lean_ctor_set(x_34, 1, x_29);
lean_ctor_set(x_34, 2, x_30);
lean_ctor_set(x_34, 3, x_31);
lean_ctor_set(x_34, 4, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_27);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_26);
return x_36;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_annotateNamedArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_annotateNamedArg___redArg(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_annotateNamedArg___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_annotateNamedArg___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_annotateNamedArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_annotateNamedArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeFn_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_Expr_hasMVar(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = lean_st_ref_get(x_3, x_4);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_instantiateMVarsCore(x_11, x_1);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_14 = lean_ctor_get(x_12, 1);
x_15 = lean_st_ref_take(x_3, x_10);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 2);
lean_inc(x_19);
x_20 = lean_ctor_get(x_16, 3);
lean_inc(x_20);
x_21 = lean_ctor_get(x_16, 4);
lean_inc(x_21);
lean_dec(x_16);
x_22 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_22, 0, x_14);
lean_ctor_set(x_22, 1, x_18);
lean_ctor_set(x_22, 2, x_19);
lean_ctor_set(x_22, 3, x_20);
lean_ctor_set(x_22, 4, x_21);
x_23 = lean_st_ref_set(x_3, x_22, x_17);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
lean_ctor_set(x_12, 1, x_2);
lean_ctor_set(x_23, 0, x_12);
return x_23;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
lean_ctor_set(x_12, 1, x_2);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_12);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_28 = lean_ctor_get(x_12, 0);
x_29 = lean_ctor_get(x_12, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_12);
x_30 = lean_st_ref_take(x_3, x_10);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
x_34 = lean_ctor_get(x_31, 2);
lean_inc(x_34);
x_35 = lean_ctor_get(x_31, 3);
lean_inc(x_35);
x_36 = lean_ctor_get(x_31, 4);
lean_inc(x_36);
lean_dec(x_31);
x_37 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_37, 0, x_29);
lean_ctor_set(x_37, 1, x_33);
lean_ctor_set(x_37, 2, x_34);
lean_ctor_set(x_37, 3, x_35);
lean_ctor_set(x_37, 4, x_36);
x_38 = lean_st_ref_set(x_3, x_37, x_32);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_40 = x_38;
} else {
 lean_dec_ref(x_38);
 x_40 = lean_box(0);
}
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_28);
lean_ctor_set(x_41, 1, x_2);
if (lean_is_scalar(x_40)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_40;
}
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_39);
return x_42;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeFn_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_instantiateMVars___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeFn_spec__0___redArg(x_1, x_3, x_7, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryFn___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeFn_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_maybeAddBlockImplicit_spec__0___redArg(x_2, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBool_spec__0___redArg(x_2, x_11);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_16 = l_Lean_Expr_getAppNumArgs(x_10);
x_17 = l_Lean_SubExpr_Pos_pushNaryFn(x_16, x_14);
lean_dec(x_14);
lean_dec(x_16);
x_18 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
x_19 = lean_ctor_get_uint8(x_2, sizeof(void*)*1 + 1);
x_20 = lean_ctor_get_uint8(x_2, sizeof(void*)*1 + 2);
x_21 = lean_ctor_get_uint8(x_2, sizeof(void*)*1 + 3);
x_22 = l_Lean_Expr_getAppFn(x_10);
lean_dec(x_10);
lean_ctor_set(x_12, 1, x_17);
lean_ctor_set(x_12, 0, x_22);
x_23 = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(x_23, 0, x_12);
lean_ctor_set_uint8(x_23, sizeof(void*)*1, x_18);
lean_ctor_set_uint8(x_23, sizeof(void*)*1 + 1, x_19);
lean_ctor_set_uint8(x_23, sizeof(void*)*1 + 2, x_20);
lean_ctor_set_uint8(x_23, sizeof(void*)*1 + 3, x_21);
x_24 = lean_apply_7(x_1, x_23, x_3, x_4, x_5, x_6, x_7, x_15);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_25 = lean_ctor_get(x_12, 0);
x_26 = lean_ctor_get(x_12, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_12);
x_27 = l_Lean_Expr_getAppNumArgs(x_10);
x_28 = l_Lean_SubExpr_Pos_pushNaryFn(x_27, x_25);
lean_dec(x_25);
lean_dec(x_27);
x_29 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
x_30 = lean_ctor_get_uint8(x_2, sizeof(void*)*1 + 1);
x_31 = lean_ctor_get_uint8(x_2, sizeof(void*)*1 + 2);
x_32 = lean_ctor_get_uint8(x_2, sizeof(void*)*1 + 3);
x_33 = l_Lean_Expr_getAppFn(x_10);
lean_dec(x_10);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_28);
x_35 = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_29);
lean_ctor_set_uint8(x_35, sizeof(void*)*1 + 1, x_30);
lean_ctor_set_uint8(x_35, sizeof(void*)*1 + 2, x_31);
lean_ctor_set_uint8(x_35, sizeof(void*)*1 + 3, x_32);
x_36 = lean_apply_7(x_1, x_35, x_3, x_4, x_5, x_6, x_7, x_26);
return x_36;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryFn___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeFn_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryFn___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeFn_spec__1___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
x_12 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
lean_dec(x_1);
x_13 = l_Lean_Expr_isApp(x_10);
lean_dec(x_10);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_14 = l_Lean_instantiateMVars___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeFn_spec__0___redArg(x_11, x_2, x_6, x_9);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_19 = x_15;
} else {
 lean_dec_ref(x_15);
 x_19 = lean_box(0);
}
x_20 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_hasLevelMVarAtCurrDepth___redArg(x_17, x_6, x_16);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_box(1);
if (x_12 == 0)
{
uint8_t x_40; 
x_40 = lean_unbox(x_21);
lean_dec(x_21);
if (x_40 == 0)
{
uint8_t x_41; 
x_41 = lean_unbox(x_23);
x_24 = x_41;
goto block_39;
}
else
{
x_24 = x_12;
goto block_39;
}
}
else
{
uint8_t x_42; 
lean_dec(x_21);
x_42 = lean_unbox(x_23);
x_24 = x_42;
goto block_39;
}
block_39:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___boxed), 8, 1);
lean_closure_set(x_25, 0, x_23);
x_26 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryFn___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeFn_spec__1___boxed), 9, 2);
lean_closure_set(x_26, 0, lean_box(0));
lean_closure_set(x_26, 1, x_25);
x_27 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_withKnowing___redArg(x_13, x_24, x_26, x_3, x_4, x_5, x_6, x_7, x_8, x_22);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_27, 0);
if (lean_is_scalar(x_19)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_19;
}
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_18);
lean_ctor_set(x_27, 0, x_30);
return x_27;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_27, 0);
x_32 = lean_ctor_get(x_27, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_27);
if (lean_is_scalar(x_19)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_19;
}
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_18);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_dec(x_19);
lean_dec(x_18);
x_35 = !lean_is_exclusive(x_27);
if (x_35 == 0)
{
return x_27;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_27, 0);
x_37 = lean_ctor_get(x_27, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_27);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_2);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_9);
return x_45;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_11 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
x_12 = lean_ctor_get_uint8(x_4, sizeof(void*)*1 + 1);
x_13 = lean_ctor_get_uint8(x_4, sizeof(void*)*1 + 2);
x_14 = lean_ctor_get_uint8(x_4, sizeof(void*)*1 + 3);
x_15 = lean_ctor_get(x_4, 0);
x_16 = lean_ctor_get(x_15, 1);
x_17 = l_Lean_SubExpr_Pos_push(x_16, x_2);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set_uint8(x_19, sizeof(void*)*1, x_11);
lean_ctor_set_uint8(x_19, sizeof(void*)*1 + 1, x_12);
lean_ctor_set_uint8(x_19, sizeof(void*)*1 + 2, x_13);
lean_ctor_set_uint8(x_19, sizeof(void*)*1 + 3, x_14);
x_20 = lean_apply_7(x_3, x_19, x_5, x_6, x_7, x_8, x_9, x_10);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_spec__0_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_maybeAddBlockImplicit_spec__0___redArg(x_2, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_12 = lean_infer_type(x_10, x_4, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_unsigned_to_nat(3u);
x_16 = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_spec__0_spec__0___redArg(x_13, x_15, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_48; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_107; lean_object* x_108; 
x_107 = lean_mk_string_unchecked("Delaborator.topDownAnalyze", 26, 26);
x_108 = l_Lean_Core_checkSystem(x_107, x_6, x_7, x_8);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; 
x_109 = lean_ctor_get(x_108, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 x_110 = x_108;
} else {
 lean_dec_ref(x_108);
 x_110 = lean_box(0);
}
x_111 = lean_mk_string_unchecked("pp", 2, 2);
x_112 = lean_mk_string_unchecked("analyze", 7, 7);
x_113 = l_Lean_Name_mkStr2(x_111, x_112);
lean_inc(x_113);
x_114 = l_Lean_isTracingEnabledFor___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt_spec__0___redArg(x_113, x_6, x_109);
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_unbox(x_115);
lean_dec(x_115);
if (x_116 == 0)
{
lean_object* x_117; 
lean_dec(x_113);
lean_dec(x_110);
x_117 = lean_ctor_get(x_114, 1);
lean_inc(x_117);
lean_dec(x_114);
x_88 = x_2;
x_89 = x_3;
x_90 = x_4;
x_91 = x_5;
x_92 = x_6;
x_93 = x_7;
x_94 = x_117;
goto block_106;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_131; uint8_t x_142; 
x_118 = lean_ctor_get(x_114, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 x_119 = x_114;
} else {
 lean_dec_ref(x_114);
 x_119 = lean_box(0);
}
x_120 = lean_mk_string_unchecked("", 0, 0);
x_121 = l_Lean_stringToMessageData(x_120);
lean_dec(x_120);
x_142 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
if (x_142 == 0)
{
lean_object* x_143; 
x_143 = lean_mk_string_unchecked("false", 5, 5);
x_131 = x_143;
goto block_141;
}
else
{
lean_object* x_144; 
x_144 = lean_mk_string_unchecked("true", 4, 4);
x_131 = x_144;
goto block_141;
}
block_130:
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_124 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_124, 0, x_123);
x_125 = l_Lean_MessageData_ofFormat(x_124);
if (lean_is_scalar(x_119)) {
 x_126 = lean_alloc_ctor(7, 2, 0);
} else {
 x_126 = x_119;
 lean_ctor_set_tag(x_126, 7);
}
lean_ctor_set(x_126, 0, x_122);
lean_ctor_set(x_126, 1, x_125);
if (lean_is_scalar(x_110)) {
 x_127 = lean_alloc_ctor(7, 2, 0);
} else {
 x_127 = x_110;
 lean_ctor_set_tag(x_127, 7);
}
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_121);
x_128 = l_Lean_addTrace___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt_spec__1___redArg(x_113, x_127, x_4, x_5, x_6, x_7, x_118);
x_129 = lean_ctor_get(x_128, 1);
lean_inc(x_129);
lean_dec(x_128);
x_88 = x_2;
x_89 = x_3;
x_90 = x_4;
x_91 = x_5;
x_92 = x_6;
x_93 = x_7;
x_94 = x_129;
goto block_106;
}
block_141:
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; 
x_132 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_132, 0, x_131);
x_133 = l_Lean_MessageData_ofFormat(x_132);
lean_inc(x_121);
x_134 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_134, 0, x_121);
lean_ctor_set(x_134, 1, x_133);
x_135 = lean_mk_string_unchecked(".", 1, 1);
x_136 = l_Lean_stringToMessageData(x_135);
lean_dec(x_135);
x_137 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_137, 0, x_134);
lean_ctor_set(x_137, 1, x_136);
x_138 = lean_ctor_get_uint8(x_2, sizeof(void*)*1 + 1);
if (x_138 == 0)
{
lean_object* x_139; 
x_139 = lean_mk_string_unchecked("false", 5, 5);
x_122 = x_137;
x_123 = x_139;
goto block_130;
}
else
{
lean_object* x_140; 
x_140 = lean_mk_string_unchecked("true", 4, 4);
x_122 = x_137;
x_123 = x_140;
goto block_130;
}
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
return x_108;
}
block_47:
{
uint8_t x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get_uint8(x_13, sizeof(void*)*1);
x_17 = lean_ctor_get_uint8(x_13, sizeof(void*)*1 + 1);
x_18 = lean_ctor_get_uint8(x_13, sizeof(void*)*1 + 2);
x_19 = lean_ctor_get(x_13, 0);
lean_inc(x_19);
x_20 = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set_uint8(x_20, sizeof(void*)*1, x_16);
lean_ctor_set_uint8(x_20, sizeof(void*)*1 + 1, x_17);
lean_ctor_set_uint8(x_20, sizeof(void*)*1 + 2, x_18);
lean_ctor_set_uint8(x_20, sizeof(void*)*1 + 3, x_1);
x_21 = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_maybeAddBlockImplicit_spec__0___redArg(x_20, x_15);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
switch (lean_obj_tag(x_22)) {
case 1:
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_maybeAddBlockImplicit(x_20, x_11, x_14, x_10, x_12, x_9, x_23);
lean_dec(x_11);
lean_dec(x_20);
return x_24;
}
case 3:
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_dec(x_21);
x_26 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeSort___redArg(x_25);
return x_26;
}
case 4:
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_22);
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
lean_dec(x_21);
x_28 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst(x_20, x_11, x_14, x_10, x_12, x_9, x_27);
return x_28;
}
case 5:
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_22);
x_29 = lean_ctor_get(x_21, 1);
lean_inc(x_29);
lean_dec(x_21);
x_30 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeApp(x_20, x_11, x_14, x_10, x_12, x_9, x_29);
lean_dec(x_20);
return x_30;
}
case 6:
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_22);
x_31 = lean_ctor_get(x_21, 1);
lean_inc(x_31);
lean_dec(x_21);
x_32 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLam(x_20, x_11, x_14, x_10, x_12, x_9, x_31);
return x_32;
}
case 7:
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_22);
x_33 = lean_ctor_get(x_21, 1);
lean_inc(x_33);
lean_dec(x_21);
x_34 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzePi(x_20, x_11, x_14, x_10, x_12, x_9, x_33);
return x_34;
}
case 8:
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_22);
x_35 = lean_ctor_get(x_21, 1);
lean_inc(x_35);
lean_dec(x_21);
x_36 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet(x_20, x_11, x_14, x_10, x_12, x_9, x_35);
return x_36;
}
case 10:
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_22);
x_37 = lean_ctor_get(x_21, 1);
lean_inc(x_37);
lean_dec(x_21);
x_38 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeMData(x_20, x_11, x_14, x_10, x_12, x_9, x_37);
return x_38;
}
case 11:
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_22);
x_39 = lean_ctor_get(x_21, 1);
lean_inc(x_39);
lean_dec(x_21);
x_40 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeProj(x_20, x_11, x_14, x_10, x_12, x_9, x_39);
return x_40;
}
default: 
{
uint8_t x_41; 
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_41 = !lean_is_exclusive(x_21);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_21, 0);
lean_dec(x_42);
x_43 = lean_box(0);
lean_ctor_set(x_21, 0, x_43);
return x_21;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_21, 1);
lean_inc(x_44);
lean_dec(x_21);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
}
}
block_51:
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
block_76:
{
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; uint8_t x_61; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_unbox(x_60);
lean_dec(x_60);
if (x_61 == 0)
{
lean_object* x_62; 
lean_dec(x_55);
x_62 = lean_ctor_get(x_59, 1);
lean_inc(x_62);
lean_dec(x_59);
x_9 = x_53;
x_10 = x_52;
x_11 = x_54;
x_12 = x_56;
x_13 = x_57;
x_14 = x_58;
x_15 = x_62;
goto block_47;
}
else
{
lean_object* x_63; uint8_t x_64; 
x_63 = lean_ctor_get(x_59, 1);
lean_inc(x_63);
lean_dec(x_59);
x_64 = l_Lean_getPPProofsWithType(x_55);
lean_dec(x_55);
if (x_64 == 0)
{
lean_dec(x_58);
lean_dec(x_56);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
x_48 = x_63;
goto block_51;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_65 = lean_box(0);
x_66 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___boxed), 8, 1);
lean_closure_set(x_66, 0, x_65);
x_67 = lean_box(x_64);
x_68 = lean_box(x_64);
x_69 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_withKnowing___boxed), 11, 4);
lean_closure_set(x_69, 0, lean_box(0));
lean_closure_set(x_69, 1, x_67);
lean_closure_set(x_69, 2, x_68);
lean_closure_set(x_69, 3, x_66);
x_70 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_spec__0___redArg(x_69, x_57, x_54, x_58, x_52, x_56, x_53, x_63);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; 
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
lean_dec(x_70);
x_48 = x_71;
goto block_51;
}
else
{
return x_70;
}
}
}
}
else
{
uint8_t x_72; 
lean_dec(x_58);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
x_72 = !lean_is_exclusive(x_59);
if (x_72 == 0)
{
return x_59;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_59, 0);
x_74 = lean_ctor_get(x_59, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_59);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
block_87:
{
if (x_86 == 0)
{
lean_dec(x_85);
lean_dec(x_81);
x_9 = x_78;
x_10 = x_77;
x_11 = x_79;
x_12 = x_82;
x_13 = x_83;
x_14 = x_84;
x_15 = x_80;
goto block_47;
}
else
{
lean_dec(x_80);
x_52 = x_77;
x_53 = x_78;
x_54 = x_79;
x_55 = x_81;
x_56 = x_82;
x_57 = x_83;
x_58 = x_84;
x_59 = x_85;
goto block_76;
}
}
block_106:
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_95 = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_maybeAddBlockImplicit_spec__0___redArg(x_88, x_94);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
x_98 = l_Lean_Expr_isAtomic(x_96);
if (x_98 == 0)
{
lean_object* x_99; uint8_t x_100; 
x_99 = lean_ctor_get(x_92, 2);
lean_inc(x_99);
x_100 = l_Lean_getPPProofs(x_99);
if (x_100 == 0)
{
lean_object* x_101; 
lean_inc(x_93);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
x_101 = l_Lean_Meta_isProof(x_96, x_90, x_91, x_92, x_93, x_97);
if (lean_obj_tag(x_101) == 0)
{
x_52 = x_91;
x_53 = x_93;
x_54 = x_89;
x_55 = x_99;
x_56 = x_92;
x_57 = x_88;
x_58 = x_90;
x_59 = x_101;
goto block_76;
}
else
{
lean_object* x_102; lean_object* x_103; uint8_t x_104; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
x_104 = l_Lean_Exception_isInterrupt(x_102);
if (x_104 == 0)
{
uint8_t x_105; 
x_105 = l_Lean_Exception_isRuntime(x_102);
lean_dec(x_102);
x_77 = x_91;
x_78 = x_93;
x_79 = x_89;
x_80 = x_103;
x_81 = x_99;
x_82 = x_92;
x_83 = x_88;
x_84 = x_90;
x_85 = x_101;
x_86 = x_105;
goto block_87;
}
else
{
lean_dec(x_102);
x_77 = x_91;
x_78 = x_93;
x_79 = x_89;
x_80 = x_103;
x_81 = x_99;
x_82 = x_92;
x_83 = x_88;
x_84 = x_90;
x_85 = x_101;
x_86 = x_104;
goto block_87;
}
}
}
else
{
lean_dec(x_99);
lean_dec(x_96);
x_9 = x_93;
x_10 = x_91;
x_11 = x_89;
x_12 = x_92;
x_13 = x_88;
x_14 = x_90;
x_15 = x_97;
goto block_47;
}
}
else
{
lean_dec(x_96);
x_9 = x_93;
x_10 = x_91;
x_11 = x_89;
x_12 = x_92;
x_13 = x_88;
x_14 = x_90;
x_15 = x_97;
goto block_47;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet_spec__0_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = lean_apply_8(x_1, x_4, x_2, x_3, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet_spec__0_spec__0___redArg___lam__0), 9, 3);
lean_closure_set(x_13, 0, x_4);
lean_closure_set(x_13, 1, x_6);
lean_closure_set(x_13, 2, x_7);
x_14 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), x_1, x_2, x_3, x_13, x_5, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
return x_14;
}
else
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
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_withLetDecl___at___Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet_spec__0_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet_spec__0_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__0___boxed), 7, 0);
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__1), 9, 0);
x_12 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__0___boxed), 5, 0);
x_13 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__1), 7, 0);
x_14 = l_instMonadEIO(lean_box(0));
x_15 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
lean_inc(x_17);
x_18 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_18, 0, x_17);
x_19 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_19, 0, x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_closure((void*)(l_instMonadEIO___lam__1), 5, 0);
x_22 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_22, 0, x_21);
x_23 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_23, 0, x_22);
x_24 = lean_alloc_closure((void*)(l_instMonadEIO___lam__2), 5, 0);
x_25 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_25, 0, x_24);
x_26 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_26, 0, x_25);
x_27 = lean_alloc_closure((void*)(l_EStateM_seqRight), 7, 2);
lean_closure_set(x_27, 0, lean_box(0));
lean_closure_set(x_27, 1, lean_box(0));
x_28 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_28, 0, x_27);
x_29 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_29, 0, x_28);
lean_inc(x_29);
lean_inc(x_26);
lean_inc(x_23);
x_30 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_30, 0, x_20);
lean_ctor_set(x_30, 1, x_12);
lean_ctor_set(x_30, 2, x_23);
lean_ctor_set(x_30, 3, x_26);
lean_ctor_set(x_30, 4, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_13);
x_32 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_31);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec(x_33);
lean_inc(x_34);
x_35 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_35, 0, x_34);
x_36 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_36, 0, x_34);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_38, 0, x_23);
x_39 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_39, 0, x_38);
x_40 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_40, 0, x_26);
x_41 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_41, 0, x_40);
x_42 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_42, 0, x_29);
x_43 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_43, 0, x_42);
x_44 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_44, 0, x_37);
lean_ctor_set(x_44, 1, x_10);
lean_ctor_set(x_44, 2, x_39);
lean_ctor_set(x_44, 3, x_41);
lean_ctor_set(x_44, 4, x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_11);
x_46 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_45);
x_47 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_46);
x_48 = l_instInhabitedOfMonad___redArg(x_47, x_1);
x_49 = lean_panic_fn(x_48, x_2);
x_50 = lean_apply_7(x_49, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_50;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_panic___at___Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet_spec__0_spec__1___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_expr_instantiate1(x_1, x_3);
x_12 = lean_unsigned_to_nat(2u);
x_13 = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_spec__0_spec__0___redArg(x_11, x_12, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_maybeAddBlockImplicit_spec__0___redArg(x_3, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 8)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
lean_dec(x_1);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_11, 2);
lean_inc(x_15);
x_16 = lean_ctor_get(x_11, 3);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet_spec__0___redArg___lam__0___boxed), 10, 2);
lean_closure_set(x_17, 0, x_16);
lean_closure_set(x_17, 1, x_2);
x_18 = lean_box(0);
x_19 = lean_unbox(x_18);
x_20 = l_Lean_Meta_withLetDecl___at___Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet_spec__0_spec__0___redArg(x_13, x_14, x_15, x_17, x_19, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_11);
lean_dec(x_2);
x_21 = lean_ctor_get(x_10, 1);
lean_inc(x_21);
lean_dec(x_10);
x_22 = lean_mk_string_unchecked("Lean.PrettyPrinter.Delaborator.SubExpr", 38, 38);
x_23 = lean_mk_string_unchecked("Lean.PrettyPrinter.Delaborator.SubExpr.withLetBody", 50, 50);
x_24 = lean_unsigned_to_nat(124u);
x_25 = lean_unsigned_to_nat(38u);
x_26 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_27 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_22, x_23, x_24, x_25, x_26);
lean_dec(x_26);
lean_dec(x_23);
lean_dec(x_22);
x_28 = l_panic___at___Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet_spec__0_spec__1___redArg(x_1, x_27, x_3, x_4, x_5, x_6, x_7, x_8, x_21);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetVarType___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_maybeAddBlockImplicit_spec__0___redArg(x_3, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 8)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_1);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_spec__0_spec__0___redArg(x_13, x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_3);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_11);
lean_dec(x_2);
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_dec(x_10);
x_17 = lean_mk_string_unchecked("Lean.PrettyPrinter.Delaborator.SubExpr", 38, 38);
x_18 = lean_mk_string_unchecked("Lean.PrettyPrinter.Delaborator.SubExpr.withLetVarType", 53, 53);
x_19 = lean_unsigned_to_nat(116u);
x_20 = lean_unsigned_to_nat(38u);
x_21 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_22 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_17, x_18, x_19, x_20, x_21);
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_17);
x_23 = l_panic___at___Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet_spec__0_spec__1___redArg(x_1, x_22, x_3, x_4, x_5, x_6, x_7, x_8, x_16);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetVarType___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetVarType___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet_spec__3___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetValue___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_maybeAddBlockImplicit_spec__0___redArg(x_3, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 8)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_1);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 2);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_unsigned_to_nat(1u);
x_15 = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_spec__0_spec__0___redArg(x_13, x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_3);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_11);
lean_dec(x_2);
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_dec(x_10);
x_17 = lean_mk_string_unchecked("Lean.PrettyPrinter.Delaborator.SubExpr", 38, 38);
x_18 = lean_mk_string_unchecked("Lean.PrettyPrinter.Delaborator.SubExpr.withLetValue", 51, 51);
x_19 = lean_unsigned_to_nat(120u);
x_20 = lean_unsigned_to_nat(38u);
x_21 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_22 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_17, x_18, x_19, x_20, x_21);
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_17);
x_23 = l_panic___at___Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet_spec__0_spec__1___redArg(x_1, x_22, x_3, x_4, x_5, x_6, x_7, x_8, x_16);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetValue___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetValue___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet_spec__4___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_maybeAddBlockImplicit_spec__0___redArg(x_1, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 8)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 2);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_box(0);
x_13 = lean_unsigned_to_nat(10u);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_14 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_canBottomUp(x_11, x_12, x_13, x_1, x_2, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_29; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_box(0);
x_29 = lean_unbox(x_15);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_30 = lean_mk_string_unchecked("pp", 2, 2);
x_31 = lean_mk_string_unchecked("analysis", 8, 8);
x_32 = lean_mk_string_unchecked("letVarType", 10, 10);
x_33 = l_Lean_Name_mkStr3(x_30, x_31, x_32);
x_34 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBool(x_33, x_1, x_2, x_3, x_4, x_5, x_6, x_16);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_box(1);
lean_inc(x_15);
x_37 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___boxed), 8, 1);
lean_closure_set(x_37, 0, x_15);
lean_inc(x_37);
x_38 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_withKnowing___boxed), 11, 4);
lean_closure_set(x_38, 0, lean_box(0));
lean_closure_set(x_38, 1, x_36);
lean_closure_set(x_38, 2, x_15);
lean_closure_set(x_38, 3, x_37);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_39 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetVarType___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet_spec__3___redArg(x_17, x_38, x_1, x_2, x_3, x_4, x_5, x_6, x_35);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
x_41 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_withKnowing___boxed), 11, 4);
lean_closure_set(x_41, 0, lean_box(0));
lean_closure_set(x_41, 1, x_36);
lean_closure_set(x_41, 2, x_36);
lean_closure_set(x_41, 3, x_37);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_42 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetValue___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet_spec__4___redArg(x_17, x_41, x_1, x_2, x_3, x_4, x_5, x_6, x_40);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_18 = x_1;
x_19 = x_2;
x_20 = x_3;
x_21 = x_4;
x_22 = x_5;
x_23 = x_6;
x_24 = x_43;
goto block_28;
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_42;
}
}
else
{
lean_dec(x_37);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_39;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; 
x_44 = lean_box(0);
x_45 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___boxed), 8, 1);
lean_closure_set(x_45, 0, x_44);
lean_inc_n(x_15, 2);
x_46 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_withKnowing___boxed), 11, 4);
lean_closure_set(x_46, 0, lean_box(0));
lean_closure_set(x_46, 1, x_15);
lean_closure_set(x_46, 2, x_15);
lean_closure_set(x_46, 3, x_45);
x_47 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_48 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 1);
x_49 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 3);
x_50 = lean_ctor_get(x_1, 0);
lean_inc(x_50);
x_51 = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set_uint8(x_51, sizeof(void*)*1, x_47);
lean_ctor_set_uint8(x_51, sizeof(void*)*1 + 1, x_48);
x_52 = lean_unbox(x_15);
lean_dec(x_15);
lean_ctor_set_uint8(x_51, sizeof(void*)*1 + 2, x_52);
lean_ctor_set_uint8(x_51, sizeof(void*)*1 + 3, x_49);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_53 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetValue___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet_spec__4___redArg(x_17, x_46, x_51, x_2, x_3, x_4, x_5, x_6, x_16);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec(x_53);
x_18 = x_1;
x_19 = x_2;
x_20 = x_3;
x_21 = x_4;
x_22 = x_5;
x_23 = x_6;
x_24 = x_54;
goto block_28;
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_53;
}
}
block_28:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_box(0);
x_26 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___boxed), 8, 1);
lean_closure_set(x_26, 0, x_25);
x_27 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet_spec__0___redArg(x_17, x_26, x_18, x_19, x_20, x_21, x_22, x_23, x_24);
return x_27;
}
}
else
{
uint8_t x_55; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_14);
if (x_55 == 0)
{
return x_14;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_14, 0);
x_57 = lean_ctor_get(x_14, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_14);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_9);
x_59 = lean_ctor_get(x_8, 1);
lean_inc(x_59);
lean_dec(x_8);
x_60 = lean_mk_string_unchecked("Lean.PrettyPrinter.Delaborator.TopDownAnalyze", 45, 45);
x_61 = lean_mk_string_unchecked("Lean.PrettyPrinter.Delaborator.TopDownAnalyze.analyze.analyzeLet", 64, 64);
x_62 = lean_unsigned_to_nat(458u);
x_63 = lean_unsigned_to_nat(46u);
x_64 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_65 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_60, x_61, x_62, x_63, x_64);
lean_dec(x_64);
lean_dec(x_61);
lean_dec(x_60);
x_66 = l_panic___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst_spec__0(x_65, x_1, x_2, x_3, x_4, x_5, x_6, x_59);
return x_66;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeMData_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_maybeAddBlockImplicit_spec__0___redArg(x_3, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 10)
{
uint8_t x_12; 
lean_dec(x_1);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_13 = lean_ctor_get(x_10, 1);
x_14 = lean_ctor_get(x_10, 0);
lean_dec(x_14);
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_ctor_get_uint8(x_3, sizeof(void*)*1);
x_17 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 1);
x_18 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 2);
x_19 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 3);
x_20 = lean_ctor_get(x_3, 0);
lean_inc(x_20);
lean_dec(x_3);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
lean_ctor_set(x_10, 1, x_21);
lean_ctor_set(x_10, 0, x_15);
x_22 = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(x_22, 0, x_10);
lean_ctor_set_uint8(x_22, sizeof(void*)*1, x_16);
lean_ctor_set_uint8(x_22, sizeof(void*)*1 + 1, x_17);
lean_ctor_set_uint8(x_22, sizeof(void*)*1 + 2, x_18);
lean_ctor_set_uint8(x_22, sizeof(void*)*1 + 3, x_19);
x_23 = lean_apply_7(x_2, x_22, x_4, x_5, x_6, x_7, x_8, x_13);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_24 = lean_ctor_get(x_10, 1);
lean_inc(x_24);
lean_dec(x_10);
x_25 = lean_ctor_get(x_11, 1);
lean_inc(x_25);
lean_dec(x_11);
x_26 = lean_ctor_get_uint8(x_3, sizeof(void*)*1);
x_27 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 1);
x_28 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 2);
x_29 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 3);
x_30 = lean_ctor_get(x_3, 0);
lean_inc(x_30);
lean_dec(x_3);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_25);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set_uint8(x_33, sizeof(void*)*1, x_26);
lean_ctor_set_uint8(x_33, sizeof(void*)*1 + 1, x_27);
lean_ctor_set_uint8(x_33, sizeof(void*)*1 + 2, x_28);
lean_ctor_set_uint8(x_33, sizeof(void*)*1 + 3, x_29);
x_34 = lean_apply_7(x_2, x_33, x_4, x_5, x_6, x_7, x_8, x_24);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_11);
lean_dec(x_2);
x_35 = lean_ctor_get(x_10, 1);
lean_inc(x_35);
lean_dec(x_10);
x_36 = lean_mk_string_unchecked("Lean.PrettyPrinter.Delaborator.SubExpr", 38, 38);
x_37 = lean_mk_string_unchecked("Lean.PrettyPrinter.Delaborator.SubExpr.withMDataExpr", 52, 52);
x_38 = lean_unsigned_to_nat(112u);
x_39 = lean_unsigned_to_nat(33u);
x_40 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_41 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_36, x_37, x_38, x_39, x_40);
lean_dec(x_40);
lean_dec(x_37);
lean_dec(x_36);
x_42 = l_panic___at___Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet_spec__0_spec__1___redArg(x_1, x_41, x_3, x_4, x_5, x_6, x_7, x_8, x_35);
return x_42;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeMData_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeMData_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeMData(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_box(0);
x_9 = lean_box(0);
x_10 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___boxed), 8, 1);
lean_closure_set(x_10, 0, x_9);
x_11 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeMData_spec__0___redArg(x_8, x_10, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeProj_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_maybeAddBlockImplicit_spec__0___redArg(x_3, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 11)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_1);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 2);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_spec__0_spec__0___redArg(x_13, x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_3);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_11);
lean_dec(x_2);
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_dec(x_10);
x_17 = lean_mk_string_unchecked("Lean.PrettyPrinter.Delaborator.SubExpr", 38, 38);
x_18 = lean_mk_string_unchecked("Lean.PrettyPrinter.Delaborator.SubExpr.withProj", 47, 47);
x_19 = lean_unsigned_to_nat(108u);
x_20 = lean_unsigned_to_nat(34u);
x_21 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_22 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_17, x_18, x_19, x_20, x_21);
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_17);
x_23 = l_panic___at___Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet_spec__0_spec__1___redArg(x_1, x_22, x_3, x_4, x_5, x_6, x_7, x_8, x_16);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeProj_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeProj_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeProj(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_box(0);
x_9 = lean_box(0);
x_10 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___boxed), 8, 1);
lean_closure_set(x_10, 0, x_9);
x_11 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeProj_spec__0___redArg(x_8, x_10, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingDomain___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLam_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_maybeAddBlockImplicit_spec__0___redArg(x_2, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Expr_bindingDomain_x21(x_10);
lean_dec(x_10);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_spec__0_spec__0___redArg(x_12, x_13, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingDomain___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLam_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingDomain___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLam_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLam_spec__1_spec__1_spec__1___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet_spec__0_spec__0___redArg___lam__0), 9, 3);
lean_closure_set(x_13, 0, x_4);
lean_closure_set(x_13, 1, x_6);
lean_closure_set(x_13, 2, x_7);
x_14 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), x_1, x_2, x_3, x_13, x_5, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
return x_14;
}
else
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
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLam_spec__1_spec__1_spec__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_withLocalDecl___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLam_spec__1_spec__1_spec__1___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLam_spec__1_spec__1___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_12 = lean_apply_8(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Expr_bindingBody_x21(x_2);
x_16 = lean_expr_instantiate1(x_15, x_4);
lean_dec(x_4);
lean_dec(x_15);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_apply_1(x_3, x_13);
x_19 = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_spec__0_spec__0___redArg(x_16, x_17, x_18, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
lean_dec(x_5);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_20 = !lean_is_exclusive(x_12);
if (x_20 == 0)
{
return x_12;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_12, 0);
x_22 = lean_ctor_get(x_12, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_12);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLam_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_11 = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_maybeAddBlockImplicit_spec__0___redArg(x_4, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_12);
x_14 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLam_spec__1_spec__1___redArg___lam__0___boxed), 11, 3);
lean_closure_set(x_14, 0, x_2);
lean_closure_set(x_14, 1, x_12);
lean_closure_set(x_14, 2, x_3);
x_15 = l_Lean_Expr_binderInfo(x_12);
x_16 = l_Lean_Expr_bindingDomain_x21(x_12);
lean_dec(x_12);
x_17 = lean_box(0);
x_18 = lean_unbox(x_17);
x_19 = l_Lean_Meta_withLocalDecl___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLam_spec__1_spec__1_spec__1___redArg(x_1, x_15, x_16, x_14, x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLam_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLam_spec__1_spec__1___redArg(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLam_spec__1___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = lean_apply_7(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLam_spec__1___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLam_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLam_spec__1___redArg___lam__0___boxed), 9, 1);
lean_closure_set(x_10, 0, x_2);
x_11 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLam_spec__1___redArg___lam__1___boxed), 8, 0);
x_12 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLam_spec__1_spec__1___redArg(x_1, x_11, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLam_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLam_spec__1___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLam(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_24; 
x_24 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_mk_string_unchecked("pp", 2, 2);
x_26 = lean_mk_string_unchecked("funBinderTypes", 14, 14);
x_27 = l_Lean_Name_mkStr2(x_25, x_26);
x_28 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBool(x_27, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_8 = x_1;
x_9 = x_2;
x_10 = x_3;
x_11 = x_4;
x_12 = x_5;
x_13 = x_6;
x_14 = x_29;
goto block_23;
}
else
{
x_8 = x_1;
x_9 = x_2;
x_10 = x_3;
x_11 = x_4;
x_12 = x_5;
x_13 = x_6;
x_14 = x_7;
goto block_23;
}
block_23:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_box(1);
x_16 = lean_box(0);
x_17 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___boxed), 8, 1);
lean_closure_set(x_17, 0, x_16);
lean_inc(x_17);
x_18 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_withKnowing___boxed), 11, 4);
lean_closure_set(x_18, 0, lean_box(0));
lean_closure_set(x_18, 1, x_15);
lean_closure_set(x_18, 2, x_16);
lean_closure_set(x_18, 3, x_17);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_19 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingDomain___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLam_spec__0___redArg(x_18, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_box(0);
x_22 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLam_spec__1___redArg(x_21, x_17, x_8, x_9, x_10, x_11, x_12, x_13, x_20);
return x_22;
}
else
{
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzePi(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_box(1);
x_9 = lean_box(0);
x_10 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___boxed), 8, 1);
lean_closure_set(x_10, 0, x_9);
lean_inc(x_10);
x_11 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_withKnowing___boxed), 11, 4);
lean_closure_set(x_11, 0, lean_box(0));
lean_closure_set(x_11, 1, x_8);
lean_closure_set(x_11, 2, x_9);
lean_closure_set(x_11, 3, x_10);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_12 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingDomain___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLam_spec__0___redArg(x_11, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_box(0);
x_15 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLam_spec__1___redArg(x_14, x_10, x_1, x_2, x_3, x_4, x_5, x_6, x_13);
return x_15;
}
else
{
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeApp___lam__0(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBool(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_box(x_2);
x_14 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___boxed), 8, 1);
lean_closure_set(x_14, 0, x_13);
x_15 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_withKnowing___redArg(x_3, x_2, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_12);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_35 = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_maybeAddBlockImplicit_spec__0___redArg(x_1, x_7);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_box(0);
x_39 = lean_unsigned_to_nat(10u);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_40 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_canBottomUp(x_36, x_38, x_39, x_1, x_2, x_3, x_4, x_5, x_6, x_37);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_44; uint8_t x_45; uint8_t x_46; lean_object* x_47; uint8_t x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; uint8_t x_70; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
if (x_43 == 0)
{
uint8_t x_81; 
x_81 = lean_unbox(x_41);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_82 = lean_mk_string_unchecked("pp", 2, 2);
x_83 = lean_mk_string_unchecked("analysis", 8, 8);
x_84 = lean_mk_string_unchecked("needsType", 9, 9);
x_85 = l_Lean_Name_mkStr3(x_82, x_83, x_84);
x_86 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBool(x_85, x_1, x_2, x_3, x_4, x_5, x_6, x_42);
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
lean_dec(x_86);
x_88 = lean_box(1);
lean_inc(x_41);
x_89 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___boxed), 8, 1);
lean_closure_set(x_89, 0, x_41);
x_90 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_withKnowing___boxed), 11, 4);
lean_closure_set(x_90, 0, lean_box(0));
lean_closure_set(x_90, 1, x_88);
lean_closure_set(x_90, 2, x_41);
lean_closure_set(x_90, 3, x_89);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_91 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_spec__0___redArg(x_90, x_1, x_2, x_3, x_4, x_5, x_6, x_87);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; uint8_t x_93; 
x_92 = lean_ctor_get(x_91, 1);
lean_inc(x_92);
lean_dec(x_91);
x_93 = lean_unbox(x_88);
x_8 = x_93;
x_9 = x_1;
x_10 = x_2;
x_11 = x_3;
x_12 = x_4;
x_13 = x_5;
x_14 = x_6;
x_15 = x_92;
goto block_34;
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_91;
}
}
else
{
lean_dec(x_41);
x_70 = x_43;
goto block_80;
}
}
else
{
lean_object* x_94; uint8_t x_95; 
lean_dec(x_41);
x_94 = lean_box(0);
x_95 = lean_unbox(x_94);
x_70 = x_95;
goto block_80;
}
block_56:
{
if (x_46 == 0)
{
x_8 = x_43;
x_9 = x_1;
x_10 = x_2;
x_11 = x_3;
x_12 = x_4;
x_13 = x_5;
x_14 = x_6;
x_15 = x_47;
goto block_34;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_48 = lean_mk_string_unchecked("pp", 2, 2);
x_49 = lean_mk_string_unchecked("structureInstanceTypes", 22, 22);
x_50 = l_Lean_Name_mkStr2(x_48, x_49);
x_51 = lean_box(x_45);
x_52 = lean_box(x_44);
x_53 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeApp___lam__0___boxed), 10, 3);
lean_closure_set(x_53, 0, x_50);
lean_closure_set(x_53, 1, x_51);
lean_closure_set(x_53, 2, x_52);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_54 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_spec__0___redArg(x_53, x_1, x_2, x_3, x_4, x_5, x_6, x_47);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
lean_dec(x_54);
x_8 = x_46;
x_9 = x_1;
x_10 = x_2;
x_11 = x_3;
x_12 = x_4;
x_13 = x_5;
x_14 = x_6;
x_15 = x_55;
goto block_34;
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_54;
}
}
}
block_69:
{
lean_object* x_61; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_61 = l_Lean_PrettyPrinter_Delaborator_isStructureInstance(x_60, x_3, x_4, x_5, x_6, x_59);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = lean_unbox(x_62);
lean_dec(x_62);
x_44 = x_57;
x_45 = x_58;
x_46 = x_64;
x_47 = x_63;
goto block_56;
}
else
{
uint8_t x_65; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_65 = !lean_is_exclusive(x_61);
if (x_65 == 0)
{
return x_61;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_61, 0);
x_67 = lean_ctor_get(x_61, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_61);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
block_80:
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_71 = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_maybeAddBlockImplicit_spec__0___redArg(x_1, x_42);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = lean_box(1);
if (x_43 == 0)
{
uint8_t x_75; 
x_75 = lean_unbox(x_74);
x_57 = x_75;
x_58 = x_70;
x_59 = x_73;
x_60 = x_72;
goto block_69;
}
else
{
if (x_70 == 0)
{
uint8_t x_76; 
x_76 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 2);
if (x_76 == 0)
{
uint8_t x_77; 
lean_dec(x_72);
x_77 = lean_unbox(x_74);
x_44 = x_77;
x_45 = x_70;
x_46 = x_76;
x_47 = x_73;
goto block_56;
}
else
{
uint8_t x_78; 
x_78 = lean_unbox(x_74);
x_57 = x_78;
x_58 = x_70;
x_59 = x_73;
x_60 = x_72;
goto block_69;
}
}
else
{
uint8_t x_79; 
x_79 = lean_unbox(x_74);
x_57 = x_79;
x_58 = x_70;
x_59 = x_73;
x_60 = x_72;
goto block_69;
}
}
}
}
else
{
uint8_t x_96; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_96 = !lean_is_exclusive(x_40);
if (x_96 == 0)
{
return x_40;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_40, 0);
x_98 = lean_ctor_get(x_40, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_40);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
block_34:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_16 = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_maybeAddBlockImplicit_spec__0___redArg(x_9, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_maybeAddBlockImplicit_spec__0___redArg(x_9, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_box(1);
x_23 = l_Lean_Expr_getAppFn(x_17);
lean_dec(x_17);
x_24 = lean_box(0);
x_25 = l_Lean_Expr_sort___override(x_24);
x_26 = l_Lean_Expr_getAppNumArgs(x_20);
lean_inc(x_26);
x_27 = lean_mk_array(x_26, x_25);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_sub(x_26, x_28);
lean_dec(x_26);
x_30 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_20, x_27, x_29);
x_31 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeAppStaged___boxed), 9, 2);
lean_closure_set(x_31, 0, x_23);
lean_closure_set(x_31, 1, x_30);
x_32 = lean_unbox(x_22);
x_33 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_withKnowing___redArg(x_8, x_32, x_31, x_9, x_10, x_11, x_12, x_13, x_14, x_21);
return x_33;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeAppStaged___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_12 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_canBottomUp(x_1, x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_19; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_15 = x_12;
} else {
 lean_dec_ref(x_12);
 x_15 = lean_box(0);
}
x_19 = lean_unbox(x_13);
lean_dec(x_13);
if (x_19 == 0)
{
if (x_4 == 0)
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
goto block_18;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_15);
x_20 = lean_mk_string_unchecked("pp", 2, 2);
x_21 = lean_mk_string_unchecked("analysis", 8, 8);
x_22 = lean_mk_string_unchecked("noDot", 5, 5);
x_23 = l_Lean_Name_mkStr3(x_20, x_21, x_22);
x_24 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBool(x_23, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_24;
}
}
else
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
goto block_18;
}
block_18:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_box(0);
if (lean_is_scalar(x_15)) {
 x_17 = lean_alloc_ctor(0, 2, 0);
} else {
 x_17 = x_15;
}
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_14);
return x_17;
}
}
else
{
uint8_t x_25; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeAppStaged(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_10 = lean_infer_type(x_1, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars(x_11, x_5, x_6, x_7, x_8, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_array_get_size(x_2);
x_17 = lean_box(0);
x_18 = lean_unbox(x_17);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_16);
lean_inc(x_14);
x_19 = l_Lean_Meta_forallMetaBoundedTelescope(x_14, x_16, x_18, x_5, x_6, x_7, x_8, x_15);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_142; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_dec(x_21);
x_26 = lean_array_get_size(x_23);
lean_inc(x_26);
x_27 = l_Array_extract(lean_box(0), x_2, x_26, x_16);
x_28 = l_Array_shrink___redArg(x_2, x_26);
lean_dec(x_26);
x_142 = lean_ctor_get_uint8(x_3, sizeof(void*)*1);
if (x_142 == 0)
{
lean_dec(x_25);
x_102 = x_3;
x_103 = x_4;
x_104 = x_5;
x_105 = x_6;
x_106 = x_7;
x_107 = x_8;
x_108 = x_22;
goto block_141;
}
else
{
lean_object* x_143; lean_object* x_144; 
lean_inc(x_1);
x_143 = l_Lean_mkAppN(x_1, x_28);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_144 = lean_infer_type(x_143, x_5, x_6, x_7, x_8, x_22);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
lean_dec(x_144);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_147 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_tryUnify(x_145, x_25, x_3, x_4, x_5, x_6, x_7, x_8, x_146);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; 
x_148 = lean_ctor_get(x_147, 1);
lean_inc(x_148);
lean_dec(x_147);
x_102 = x_3;
x_103 = x_4;
x_104 = x_5;
x_105 = x_6;
x_106 = x_7;
x_107 = x_8;
x_108 = x_148;
goto block_141;
}
else
{
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_147;
}
}
else
{
uint8_t x_149; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_149 = !lean_is_exclusive(x_144);
if (x_149 == 0)
{
return x_144;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_ctor_get(x_144, 0);
x_151 = lean_ctor_get(x_144, 1);
lean_inc(x_151);
lean_inc(x_150);
lean_dec(x_144);
x_152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_151);
return x_152;
}
}
}
block_67:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_inc(x_28);
lean_inc(x_1);
x_37 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_37, 0, x_1);
lean_ctor_set(x_37, 1, x_14);
lean_ctor_set(x_37, 2, x_28);
lean_ctor_set(x_37, 3, x_23);
lean_ctor_set(x_37, 4, x_24);
lean_ctor_set_uint8(x_37, sizeof(void*)*5, x_36);
x_38 = lean_array_get_size(x_28);
x_39 = lean_box(0);
x_40 = lean_mk_array(x_38, x_39);
x_41 = lean_unsigned_to_nat(0u);
x_42 = lean_mk_empty_array_with_capacity(x_41);
lean_inc_n(x_40, 3);
x_43 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_40);
lean_ctor_set(x_43, 2, x_40);
lean_ctor_set(x_43, 3, x_40);
lean_ctor_set(x_43, 4, x_42);
lean_inc(x_32);
lean_inc(x_29);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_34);
x_44 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore(x_37, x_43, x_35, x_34, x_30, x_31, x_29, x_32, x_33);
if (lean_obj_tag(x_44) == 0)
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_46 = lean_ctor_get(x_44, 1);
x_47 = lean_ctor_get(x_44, 0);
lean_dec(x_47);
x_48 = l_Array_isEmpty___redArg(x_27);
if (x_48 == 0)
{
uint8_t x_49; 
x_49 = l_Array_isEmpty___redArg(x_28);
if (x_49 == 0)
{
lean_object* x_50; 
lean_free_object(x_44);
x_50 = l_Lean_mkAppN(x_1, x_28);
lean_dec(x_28);
x_1 = x_50;
x_2 = x_27;
x_3 = x_35;
x_4 = x_34;
x_5 = x_30;
x_6 = x_31;
x_7 = x_29;
x_8 = x_32;
x_9 = x_46;
goto _start;
}
else
{
lean_object* x_52; 
lean_dec(x_34);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_1);
x_52 = lean_box(0);
lean_ctor_set(x_44, 0, x_52);
return x_44;
}
}
else
{
lean_object* x_53; 
lean_dec(x_34);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_1);
x_53 = lean_box(0);
lean_ctor_set(x_44, 0, x_53);
return x_44;
}
}
else
{
lean_object* x_54; uint8_t x_55; 
x_54 = lean_ctor_get(x_44, 1);
lean_inc(x_54);
lean_dec(x_44);
x_55 = l_Array_isEmpty___redArg(x_27);
if (x_55 == 0)
{
uint8_t x_56; 
x_56 = l_Array_isEmpty___redArg(x_28);
if (x_56 == 0)
{
lean_object* x_57; 
x_57 = l_Lean_mkAppN(x_1, x_28);
lean_dec(x_28);
x_1 = x_57;
x_2 = x_27;
x_3 = x_35;
x_4 = x_34;
x_5 = x_30;
x_6 = x_31;
x_7 = x_29;
x_8 = x_32;
x_9 = x_54;
goto _start;
}
else
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_34);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_1);
x_59 = lean_box(0);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_54);
return x_60;
}
}
else
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_34);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_1);
x_61 = lean_box(0);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_54);
return x_62;
}
}
}
else
{
uint8_t x_63; 
lean_dec(x_34);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_1);
x_63 = !lean_is_exclusive(x_44);
if (x_63 == 0)
{
return x_44;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_44, 0);
x_65 = lean_ctor_get(x_44, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_44);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
block_84:
{
if (x_77 == 0)
{
uint8_t x_78; 
x_78 = l_Lean_getPPAnalyzeTrustSubtypeMk(x_70);
lean_dec(x_70);
if (x_78 == 0)
{
lean_dec(x_72);
x_29 = x_68;
x_30 = x_69;
x_31 = x_71;
x_32 = x_73;
x_33 = x_75;
x_34 = x_74;
x_35 = x_76;
x_36 = x_78;
goto block_67;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_79 = lean_mk_string_unchecked("Subtype", 7, 7);
x_80 = lean_mk_string_unchecked("mk", 2, 2);
x_81 = l_Lean_Name_mkStr2(x_79, x_80);
x_82 = lean_unsigned_to_nat(4u);
x_83 = l_Lean_Expr_isAppOfArity(x_72, x_81, x_82);
lean_dec(x_81);
lean_dec(x_72);
x_29 = x_68;
x_30 = x_69;
x_31 = x_71;
x_32 = x_73;
x_33 = x_75;
x_34 = x_74;
x_35 = x_76;
x_36 = x_83;
goto block_67;
}
}
else
{
lean_dec(x_72);
lean_dec(x_70);
x_29 = x_68;
x_30 = x_69;
x_31 = x_71;
x_32 = x_73;
x_33 = x_75;
x_34 = x_74;
x_35 = x_76;
x_36 = x_77;
goto block_67;
}
}
block_101:
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; 
x_92 = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_maybeAddBlockImplicit_spec__0___redArg(x_85, x_91);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
x_95 = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_maybeAddBlockImplicit_spec__0___redArg(x_85, x_94);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
x_98 = lean_ctor_get(x_89, 2);
lean_inc(x_98);
x_99 = l_Lean_getPPAnalyzeTrustSubst(x_98);
if (x_99 == 0)
{
lean_dec(x_93);
x_68 = x_89;
x_69 = x_87;
x_70 = x_98;
x_71 = x_88;
x_72 = x_96;
x_73 = x_90;
x_74 = x_86;
x_75 = x_97;
x_76 = x_85;
x_77 = x_99;
goto block_84;
}
else
{
uint8_t x_100; 
x_100 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isSubstLike(x_93);
lean_dec(x_93);
x_68 = x_89;
x_69 = x_87;
x_70 = x_98;
x_71 = x_88;
x_72 = x_96;
x_73 = x_90;
x_74 = x_86;
x_75 = x_97;
x_76 = x_85;
x_77 = x_100;
goto block_84;
}
}
block_141:
{
lean_object* x_109; uint8_t x_110; 
x_109 = lean_ctor_get(x_106, 2);
lean_inc(x_109);
x_110 = l_Lean_getPPFieldNotation(x_109);
if (x_110 == 0)
{
lean_dec(x_109);
x_85 = x_102;
x_86 = x_103;
x_87 = x_104;
x_88 = x_105;
x_89 = x_106;
x_90 = x_107;
x_91 = x_108;
goto block_101;
}
else
{
uint8_t x_111; lean_object* x_112; 
x_111 = l_Lean_getPPFieldNotationGeneralized(x_109);
lean_dec(x_109);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_28);
lean_inc(x_1);
x_112 = l_Lean_PrettyPrinter_Delaborator_fieldNotationCandidate_x3f(x_1, x_28, x_111, x_104, x_105, x_106, x_107, x_108);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; 
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; 
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
lean_dec(x_112);
x_85 = x_102;
x_86 = x_103;
x_87 = x_104;
x_88 = x_105;
x_89 = x_106;
x_90 = x_107;
x_91 = x_114;
goto block_101;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; 
x_115 = lean_ctor_get(x_113, 0);
lean_inc(x_115);
lean_dec(x_113);
x_116 = lean_ctor_get(x_112, 1);
lean_inc(x_116);
lean_dec(x_112);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
lean_dec(x_115);
x_118 = lean_array_get_size(x_28);
x_119 = lean_nat_dec_lt(x_117, x_118);
lean_dec(x_118);
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
lean_dec(x_117);
x_120 = lean_mk_string_unchecked("pp", 2, 2);
x_121 = lean_mk_string_unchecked("analysis", 8, 8);
x_122 = lean_mk_string_unchecked("noDot", 5, 5);
x_123 = l_Lean_Name_mkStr3(x_120, x_121, x_122);
x_124 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBool(x_123, x_102, x_103, x_104, x_105, x_106, x_107, x_116);
x_125 = lean_ctor_get(x_124, 1);
lean_inc(x_125);
lean_dec(x_124);
x_85 = x_102;
x_86 = x_103;
x_87 = x_104;
x_88 = x_105;
x_89 = x_106;
x_90 = x_107;
x_91 = x_125;
goto block_101;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; uint8_t x_134; lean_object* x_135; 
x_126 = lean_box(0);
x_127 = l_Lean_instInhabitedExpr;
x_128 = lean_array_get(x_127, x_28, x_117);
lean_dec(x_117);
x_129 = lean_box(0);
x_130 = lean_unsigned_to_nat(10u);
x_131 = lean_box(x_110);
x_132 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeAppStaged___lam__0___boxed), 11, 4);
lean_closure_set(x_132, 0, x_128);
lean_closure_set(x_132, 1, x_129);
lean_closure_set(x_132, 2, x_130);
lean_closure_set(x_132, 3, x_131);
x_133 = lean_unbox(x_126);
x_134 = lean_unbox(x_126);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
x_135 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_withKnowing___redArg(x_133, x_134, x_132, x_102, x_103, x_104, x_105, x_106, x_107, x_116);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; 
x_136 = lean_ctor_get(x_135, 1);
lean_inc(x_136);
lean_dec(x_135);
x_85 = x_102;
x_86 = x_103;
x_87 = x_104;
x_88 = x_105;
x_89 = x_106;
x_90 = x_107;
x_91 = x_136;
goto block_101;
}
else
{
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_105);
lean_dec(x_104);
lean_dec(x_103);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_14);
lean_dec(x_1);
return x_135;
}
}
}
}
else
{
uint8_t x_137; 
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_105);
lean_dec(x_104);
lean_dec(x_103);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_14);
lean_dec(x_1);
x_137 = !lean_is_exclusive(x_112);
if (x_137 == 0)
{
return x_112;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_112, 0);
x_139 = lean_ctor_get(x_112, 1);
lean_inc(x_139);
lean_inc(x_138);
lean_dec(x_112);
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
return x_140;
}
}
}
}
}
else
{
uint8_t x_153; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_153 = !lean_is_exclusive(x_19);
if (x_153 == 0)
{
return x_19;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_154 = lean_ctor_get(x_19, 0);
x_155 = lean_ctor_get(x_19, 1);
lean_inc(x_155);
lean_inc(x_154);
lean_dec(x_19);
x_156 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_156, 0, x_154);
lean_ctor_set(x_156, 1, x_155);
return x_156;
}
}
}
else
{
uint8_t x_157; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_157 = !lean_is_exclusive(x_10);
if (x_157 == 0)
{
return x_10;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_158 = lean_ctor_get(x_10, 0);
x_159 = lean_ctor_get(x_10, 1);
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_10);
x_160 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_160, 0, x_158);
lean_ctor_set(x_160, 1, x_159);
return x_160;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_1, 1);
x_14 = lean_nat_dec_lt(x_3, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_5);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_12);
return x_16;
}
else
{
lean_object* x_17; 
lean_dec(x_2);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_4);
lean_inc(x_3);
x_17 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeArg(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_box(0);
x_22 = lean_ctor_get(x_1, 2);
x_23 = lean_nat_add(x_3, x_22);
lean_dec(x_3);
x_2 = x_21;
x_3 = x_23;
x_5 = x_20;
x_12 = x_19;
goto _start;
}
else
{
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_spec__0___redArg(x_1, x_2, x_3, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_10 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectBottomUps(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_14 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_checkOutParams(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_18 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectHigherOrders(x_1, x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_22 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_hBinOpHeuristic(x_1, x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_26 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectTrivialBottomUps(x_1, x_25, x_3, x_4, x_5, x_6, x_7, x_8, x_24);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_33; lean_object* x_34; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_box(1);
x_31 = lean_box(0);
x_32 = lean_unbox(x_30);
x_33 = lean_unbox(x_31);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_34 = l_Lean_Meta_processPostponed(x_32, x_33, x_5, x_6, x_7, x_8, x_28);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_36 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic(x_1, x_29, x_3, x_4, x_5, x_6, x_7, x_8, x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_40 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeFn(x_1, x_39, x_3, x_4, x_5, x_6, x_7, x_8, x_38);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_unsigned_to_nat(0u);
x_45 = lean_ctor_get(x_1, 2);
lean_inc(x_45);
x_46 = lean_array_get_size(x_45);
lean_dec(x_45);
x_47 = lean_unsigned_to_nat(1u);
x_48 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_48, 0, x_44);
lean_ctor_set(x_48, 1, x_46);
lean_ctor_set(x_48, 2, x_47);
x_49 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_50 = l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_spec__0___redArg(x_48, x_49, x_44, x_1, x_43, x_3, x_4, x_5, x_6, x_7, x_8, x_42);
lean_dec(x_48);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit(x_1, x_53, x_3, x_4, x_5, x_6, x_7, x_8, x_52);
return x_54;
}
else
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_50;
}
}
else
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_40;
}
}
else
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_36;
}
}
else
{
uint8_t x_55; 
lean_dec(x_29);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_34);
if (x_55 == 0)
{
return x_34;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_34, 0);
x_57 = lean_ctor_get(x_34, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_34);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_26;
}
}
else
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_22;
}
}
else
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_18;
}
}
else
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_14;
}
}
else
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_10;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit_spec__0(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_uget(x_1, x_2);
x_6 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_nameNotRoundtrippable(x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; size_t x_8; size_t x_9; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_usize_of_nat(x_7);
x_9 = lean_usize_add(x_2, x_8);
x_2 = x_9;
goto _start;
}
else
{
return x_6;
}
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_box(0);
x_12 = lean_unbox(x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_hBinOpHeuristic_spec__0___redArg(x_3, x_4, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_16 = lean_infer_type(x_14, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_unsigned_to_nat(3u);
x_20 = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core_spec__2_spec__2_spec__2___redArg(x_17, x_19, x_1, x_2, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_18);
return x_20;
}
else
{
uint8_t x_21; 
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_16);
if (x_21 == 0)
{
return x_16;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_16, 0);
x_23 = lean_ctor_get(x_16, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_16);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit_spec__1___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit_spec__2_spec__2___redArg___lam__0(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_withKnowing___redArg(x_1, x_2, x_3, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_5);
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
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_5);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
uint8_t x_21; 
lean_dec(x_5);
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
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit_spec__2_spec__2___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBool(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_3);
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_11, 0);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_11);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_3);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit_spec__2_spec__2___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_61; uint8_t x_62; 
x_23 = lean_box(0);
x_61 = lean_ctor_get(x_4, 1);
x_62 = lean_nat_dec_lt(x_6, x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_5);
lean_ctor_set(x_63, 1, x_8);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_15);
return x_64;
}
else
{
uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
lean_dec(x_5);
x_65 = l_instInhabitedBool;
x_66 = lean_ctor_get(x_8, 3);
lean_inc(x_66);
x_67 = lean_box(x_65);
x_68 = lean_array_get(x_67, x_66, x_6);
lean_dec(x_66);
x_69 = lean_unbox(x_68);
lean_dec(x_68);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_70 = lean_mk_string_unchecked("pp", 2, 2);
x_71 = l_Lean_Expr_getAppNumArgs(x_3);
x_72 = lean_nat_add(x_71, x_6);
lean_dec(x_71);
x_73 = lean_mk_string_unchecked("analysis", 8, 8);
x_74 = lean_mk_string_unchecked("hole", 4, 4);
x_75 = l_Lean_Name_mkStr3(x_70, x_73, x_74);
x_76 = lean_alloc_closure((void*)(l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit_spec__2_spec__2___redArg___lam__1___boxed), 10, 1);
lean_closure_set(x_76, 0, x_75);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_7);
x_77 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_spec__0___redArg(x_72, x_76, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_72);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_7);
x_43 = x_7;
x_44 = x_80;
x_45 = x_9;
x_46 = x_10;
x_47 = x_11;
x_48 = x_12;
x_49 = x_13;
x_50 = x_14;
x_51 = x_79;
goto block_60;
}
else
{
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
return x_77;
}
}
else
{
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_7);
x_43 = x_7;
x_44 = x_8;
x_45 = x_9;
x_46 = x_10;
x_47 = x_11;
x_48 = x_12;
x_49 = x_13;
x_50 = x_14;
x_51 = x_15;
goto block_60;
}
}
block_22:
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_4, 2);
x_20 = lean_nat_add(x_6, x_19);
lean_dec(x_6);
x_5 = x_16;
x_6 = x_20;
x_8 = x_17;
x_15 = x_18;
goto _start;
}
block_42:
{
if (x_33 == 0)
{
lean_dec(x_32);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
x_16 = x_23;
x_17 = x_27;
x_18 = x_30;
goto block_22;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_34 = lean_box(0);
x_35 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___boxed), 8, 1);
lean_closure_set(x_35, 0, x_34);
x_36 = lean_box(x_1);
x_37 = lean_alloc_closure((void*)(l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit_spec__2_spec__2___redArg___lam__0___boxed), 12, 3);
lean_closure_set(x_37, 0, x_36);
lean_closure_set(x_37, 1, x_34);
lean_closure_set(x_37, 2, x_35);
x_38 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit_spec__1___redArg(x_37, x_32, x_27, x_31, x_28, x_26, x_24, x_25, x_29, x_30);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_16 = x_23;
x_17 = x_41;
x_18 = x_40;
goto block_22;
}
else
{
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
return x_38;
}
}
}
block_60:
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; uint8_t x_56; uint8_t x_57; 
x_52 = lean_box(0);
x_53 = lean_array_get(x_52, x_2, x_6);
x_54 = lean_unbox(x_53);
lean_dec(x_53);
x_55 = lean_box(3);
x_56 = lean_unbox(x_55);
x_57 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(x_54, x_56);
if (x_57 == 0)
{
x_24 = x_48;
x_25 = x_49;
x_26 = x_47;
x_27 = x_44;
x_28 = x_46;
x_29 = x_50;
x_30 = x_51;
x_31 = x_45;
x_32 = x_43;
x_33 = x_57;
goto block_42;
}
else
{
lean_object* x_58; uint8_t x_59; 
x_58 = lean_ctor_get(x_49, 2);
lean_inc(x_58);
x_59 = l_Lean_getPPInstanceTypes(x_58);
lean_dec(x_58);
x_24 = x_48;
x_25 = x_49;
x_26 = x_47;
x_27 = x_44;
x_28 = x_46;
x_29 = x_50;
x_30 = x_51;
x_31 = x_45;
x_32 = x_43;
x_33 = x_59;
goto block_42;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit_spec__2_spec__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; 
x_18 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit_spec__2_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit_spec__2___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_61; uint8_t x_62; 
x_23 = lean_box(0);
x_61 = lean_ctor_get(x_4, 1);
x_62 = lean_nat_dec_lt(x_6, x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_5);
lean_ctor_set(x_63, 1, x_8);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_15);
return x_64;
}
else
{
uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
lean_dec(x_5);
x_65 = l_instInhabitedBool;
x_66 = lean_ctor_get(x_8, 3);
lean_inc(x_66);
x_67 = lean_box(x_65);
x_68 = lean_array_get(x_67, x_66, x_6);
lean_dec(x_66);
x_69 = lean_unbox(x_68);
lean_dec(x_68);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_70 = lean_mk_string_unchecked("pp", 2, 2);
x_71 = l_Lean_Expr_getAppNumArgs(x_3);
x_72 = lean_nat_add(x_71, x_6);
lean_dec(x_71);
x_73 = lean_mk_string_unchecked("analysis", 8, 8);
x_74 = lean_mk_string_unchecked("hole", 4, 4);
x_75 = l_Lean_Name_mkStr3(x_70, x_73, x_74);
x_76 = lean_alloc_closure((void*)(l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit_spec__2_spec__2___redArg___lam__1___boxed), 10, 1);
lean_closure_set(x_76, 0, x_75);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_7);
x_77 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_spec__0___redArg(x_72, x_76, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_72);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_7);
x_43 = x_7;
x_44 = x_80;
x_45 = x_9;
x_46 = x_10;
x_47 = x_11;
x_48 = x_12;
x_49 = x_13;
x_50 = x_14;
x_51 = x_79;
goto block_60;
}
else
{
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
return x_77;
}
}
else
{
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_7);
x_43 = x_7;
x_44 = x_8;
x_45 = x_9;
x_46 = x_10;
x_47 = x_11;
x_48 = x_12;
x_49 = x_13;
x_50 = x_14;
x_51 = x_15;
goto block_60;
}
}
block_22:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_4, 2);
x_20 = lean_nat_add(x_6, x_19);
x_21 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit_spec__2_spec__2___redArg(x_1, x_2, x_3, x_4, x_16, x_20, x_7, x_17, x_9, x_10, x_11, x_12, x_13, x_14, x_18);
return x_21;
}
block_42:
{
if (x_33 == 0)
{
lean_dec(x_32);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_24);
x_16 = x_23;
x_17 = x_30;
x_18 = x_31;
goto block_22;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_34 = lean_box(0);
x_35 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___boxed), 8, 1);
lean_closure_set(x_35, 0, x_34);
x_36 = lean_box(x_1);
x_37 = lean_alloc_closure((void*)(l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit_spec__2_spec__2___redArg___lam__0___boxed), 12, 3);
lean_closure_set(x_37, 0, x_36);
lean_closure_set(x_37, 1, x_34);
lean_closure_set(x_37, 2, x_35);
x_38 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit_spec__1___redArg(x_37, x_25, x_30, x_26, x_32, x_27, x_28, x_29, x_24, x_31);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_16 = x_23;
x_17 = x_41;
x_18 = x_40;
goto block_22;
}
else
{
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
return x_38;
}
}
}
block_60:
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; uint8_t x_56; uint8_t x_57; 
x_52 = lean_box(0);
x_53 = lean_array_get(x_52, x_2, x_6);
x_54 = lean_unbox(x_53);
lean_dec(x_53);
x_55 = lean_box(3);
x_56 = lean_unbox(x_55);
x_57 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(x_54, x_56);
if (x_57 == 0)
{
x_24 = x_50;
x_25 = x_43;
x_26 = x_45;
x_27 = x_47;
x_28 = x_48;
x_29 = x_49;
x_30 = x_44;
x_31 = x_51;
x_32 = x_46;
x_33 = x_57;
goto block_42;
}
else
{
lean_object* x_58; uint8_t x_59; 
x_58 = lean_ctor_get(x_49, 2);
lean_inc(x_58);
x_59 = l_Lean_getPPInstanceTypes(x_58);
lean_dec(x_58);
x_24 = x_50;
x_25 = x_43;
x_26 = x_45;
x_27 = x_47;
x_28 = x_48;
x_29 = x_49;
x_30 = x_44;
x_31 = x_51;
x_32 = x_46;
x_33 = x_59;
goto block_42;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit_spec__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; 
x_18 = l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 2);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 4);
lean_inc(x_16);
x_17 = lean_ctor_get(x_2, 4);
lean_inc(x_17);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_array_get_size(x_17);
x_20 = lean_nat_dec_lt(x_18, x_19);
if (x_20 == 0)
{
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
goto block_13;
}
else
{
if (x_20 == 0)
{
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
goto block_13;
}
else
{
size_t x_21; size_t x_22; uint8_t x_23; 
x_21 = lean_usize_of_nat(x_18);
x_22 = lean_usize_of_nat(x_19);
lean_dec(x_19);
x_23 = l_Array_anyMUnsafe_any___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit_spec__0(x_17, x_21, x_22);
lean_dec(x_17);
if (x_23 == 0)
{
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
goto block_13;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_24 = lean_mk_string_unchecked("pp", 2, 2);
x_25 = lean_mk_string_unchecked("explicit", 8, 8);
x_26 = l_Lean_Name_mkStr2(x_24, x_25);
x_27 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBool(x_26, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_array_get_size(x_15);
lean_dec(x_15);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_31, 0, x_18);
lean_ctor_set(x_31, 1, x_29);
lean_ctor_set(x_31, 2, x_30);
x_32 = lean_box(0);
x_33 = l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit_spec__2___redArg(x_23, x_16, x_14, x_31, x_32, x_18, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_28);
lean_dec(x_31);
lean_dec(x_14);
lean_dec(x_16);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_35, 0);
lean_dec(x_37);
lean_ctor_set(x_35, 0, x_32);
return x_33;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_32);
lean_ctor_set(x_39, 1, x_38);
lean_ctor_set(x_33, 0, x_39);
return x_33;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_33, 0);
x_41 = lean_ctor_get(x_33, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_33);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_43 = x_40;
} else {
 lean_dec_ref(x_40);
 x_43 = lean_box(0);
}
if (lean_is_scalar(x_43)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_43;
}
lean_ctor_set(x_44, 0, x_32);
lean_ctor_set(x_44, 1, x_42);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_41);
return x_45;
}
}
else
{
return x_33;
}
}
}
}
block_13:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_2);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeArg___lam__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_ctor_get(x_7, 3);
lean_inc(x_29);
x_30 = lean_box(x_3);
x_31 = lean_array_get(x_30, x_29, x_4);
lean_dec(x_29);
x_32 = lean_unbox(x_31);
lean_dec(x_31);
if (x_32 == 0)
{
x_15 = x_14;
goto block_28;
}
else
{
lean_object* x_33; 
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_1);
x_33 = l___private_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_0__Lean_PrettyPrinter_Delaborator_TopDownAnalyze_typeUnknown(x_1, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_46; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_46 = lean_unbox(x_34);
lean_dec(x_34);
if (x_46 == 0)
{
x_36 = x_32;
goto block_45;
}
else
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_box(0);
x_48 = lean_unbox(x_47);
x_36 = x_48;
goto block_45;
}
block_45:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_box(0);
x_38 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___boxed), 8, 1);
lean_closure_set(x_38, 0, x_37);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_39 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_withKnowing___redArg(x_36, x_32, x_38, x_8, x_9, x_10, x_11, x_12, x_13, x_35);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
x_15 = x_40;
goto block_28;
}
else
{
uint8_t x_41; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_39);
if (x_41 == 0)
{
return x_39;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_39, 0);
x_43 = lean_ctor_get(x_39, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_39);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_33);
if (x_49 == 0)
{
return x_33;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_33, 0);
x_51 = lean_ctor_get(x_33, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_33);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
block_28:
{
lean_object* x_16; 
x_16 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_tryUnify(x_1, x_2, x_8, x_9, x_10, x_11, x_12, x_13, x_15);
lean_dec(x_10);
lean_dec(x_9);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_7);
lean_ctor_set(x_16, 0, x_19);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_16, 0);
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_16);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_7);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_7);
x_24 = !lean_is_exclusive(x_16);
if (x_24 == 0)
{
return x_16;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_16, 0);
x_26 = lean_ctor_get(x_16, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_16);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeArg___lam__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20) {
_start:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_59; uint8_t x_60; lean_object* x_61; uint8_t x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_99; lean_object* x_100; lean_object* x_101; uint8_t x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; uint8_t x_121; uint8_t x_122; uint8_t x_123; uint8_t x_216; 
x_121 = lean_ctor_get_uint8(x_14, sizeof(void*)*1);
x_122 = lean_ctor_get_uint8(x_14, sizeof(void*)*1 + 1);
x_216 = lean_ctor_get_uint8(x_14, sizeof(void*)*1 + 2);
if (x_216 == 0)
{
lean_object* x_217; lean_object* x_218; uint8_t x_219; 
x_217 = lean_box(x_7);
x_218 = lean_array_get(x_217, x_11, x_1);
x_219 = lean_unbox(x_218);
lean_dec(x_218);
x_123 = x_219;
goto block_215;
}
else
{
x_123 = x_216;
goto block_215;
}
block_34:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_24 = lean_box(1);
x_25 = lean_box(0);
x_26 = lean_ctor_get(x_22, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_22, 2);
lean_inc(x_28);
x_29 = lean_ctor_get(x_22, 3);
lean_inc(x_29);
x_30 = lean_array_set(x_29, x_1, x_24);
x_31 = lean_ctor_get(x_22, 4);
lean_inc(x_31);
lean_dec(x_22);
x_32 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_32, 0, x_26);
lean_ctor_set(x_32, 1, x_27);
lean_ctor_set(x_32, 2, x_28);
lean_ctor_set(x_32, 3, x_30);
lean_ctor_set(x_32, 4, x_31);
x_33 = lean_apply_10(x_2, x_25, x_12, x_32, x_21, x_15, x_16, x_17, x_18, x_19, x_23);
return x_33;
}
block_46:
{
if (x_36 == 0)
{
x_21 = x_35;
x_22 = x_13;
x_23 = x_37;
goto block_34;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_38 = lean_mk_string_unchecked("pp", 2, 2);
x_39 = lean_mk_string_unchecked("analysis", 8, 8);
x_40 = lean_mk_string_unchecked("hole", 4, 4);
x_41 = l_Lean_Name_mkStr3(x_38, x_39, x_40);
x_42 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBool(x_41, x_35, x_15, x_16, x_17, x_18, x_19, x_37);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_apply_10(x_2, x_43, x_12, x_13, x_35, x_15, x_16, x_17, x_18, x_19, x_44);
return x_45;
}
}
block_58:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_50 = lean_mk_string_unchecked("pp", 2, 2);
x_51 = lean_mk_string_unchecked("analysis", 8, 8);
x_52 = lean_mk_string_unchecked("skip", 4, 4);
x_53 = l_Lean_Name_mkStr3(x_50, x_51, x_52);
x_54 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBool(x_53, x_49, x_15, x_16, x_17, x_18, x_19, x_47);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = lean_apply_10(x_2, x_55, x_12, x_48, x_49, x_15, x_16, x_17, x_18, x_19, x_56);
return x_57;
}
block_83:
{
if (x_3 == 0)
{
lean_object* x_62; 
x_62 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_mvarName(x_4, x_16, x_17, x_18, x_19, x_61);
lean_dec(x_4);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_annotateNamedArg___redArg(x_63, x_13, x_59, x_15, x_16, x_17, x_18, x_19, x_64);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = lean_box(0);
x_70 = lean_ctor_get(x_68, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_68, 1);
lean_inc(x_71);
x_72 = lean_ctor_get(x_68, 2);
lean_inc(x_72);
x_73 = lean_ctor_get(x_68, 3);
lean_inc(x_73);
x_74 = lean_box(x_60);
x_75 = lean_array_set(x_73, x_1, x_74);
x_76 = lean_ctor_get(x_68, 4);
lean_inc(x_76);
lean_dec(x_68);
x_77 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_77, 0, x_70);
lean_ctor_set(x_77, 1, x_71);
lean_ctor_set(x_77, 2, x_72);
lean_ctor_set(x_77, 3, x_75);
lean_ctor_set(x_77, 4, x_76);
x_78 = lean_apply_10(x_2, x_69, x_12, x_77, x_59, x_15, x_16, x_17, x_18, x_19, x_67);
return x_78;
}
else
{
uint8_t x_79; 
lean_dec(x_59);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_2);
x_79 = !lean_is_exclusive(x_62);
if (x_79 == 0)
{
return x_62;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_62, 0);
x_81 = lean_ctor_get(x_62, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_62);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
else
{
lean_dec(x_4);
x_47 = x_61;
x_48 = x_13;
x_49 = x_59;
goto block_58;
}
}
block_98:
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_88 = lean_box(0);
x_89 = lean_ctor_get(x_85, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_85, 1);
lean_inc(x_90);
x_91 = lean_ctor_get(x_85, 2);
lean_inc(x_91);
x_92 = lean_ctor_get(x_85, 3);
lean_inc(x_92);
x_93 = lean_box(x_84);
x_94 = lean_array_set(x_92, x_1, x_93);
x_95 = lean_ctor_get(x_85, 4);
lean_inc(x_95);
lean_dec(x_85);
x_96 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_96, 0, x_89);
lean_ctor_set(x_96, 1, x_90);
lean_ctor_set(x_96, 2, x_91);
lean_ctor_set(x_96, 3, x_94);
lean_ctor_set(x_96, 4, x_95);
x_97 = lean_apply_10(x_2, x_88, x_12, x_96, x_86, x_15, x_16, x_17, x_18, x_19, x_87);
return x_97;
}
block_113:
{
lean_object* x_102; 
x_102 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_mvarName(x_4, x_16, x_17, x_18, x_19, x_101);
lean_dec(x_4);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
x_105 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_annotateNamedArg___redArg(x_103, x_13, x_100, x_15, x_16, x_17, x_18, x_19, x_104);
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec(x_106);
x_84 = x_99;
x_85 = x_108;
x_86 = x_100;
x_87 = x_107;
goto block_98;
}
else
{
uint8_t x_109; 
lean_dec(x_100);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_2);
x_109 = !lean_is_exclusive(x_102);
if (x_109 == 0)
{
return x_102;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_102, 0);
x_111 = lean_ctor_get(x_102, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_102);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
block_120:
{
if (x_118 == 0)
{
lean_dec(x_115);
x_99 = x_114;
x_100 = x_116;
x_101 = x_117;
goto block_113;
}
else
{
lean_object* x_119; 
lean_dec(x_116);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_2);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_115);
lean_ctor_set(x_119, 1, x_117);
return x_119;
}
}
block_215:
{
uint8_t x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_124 = lean_ctor_get_uint8(x_14, sizeof(void*)*1 + 3);
x_125 = lean_ctor_get(x_14, 0);
lean_inc(x_125);
x_126 = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set_uint8(x_126, sizeof(void*)*1, x_121);
lean_ctor_set_uint8(x_126, sizeof(void*)*1 + 1, x_122);
lean_ctor_set_uint8(x_126, sizeof(void*)*1 + 2, x_123);
lean_ctor_set_uint8(x_126, sizeof(void*)*1 + 3, x_124);
x_127 = lean_box(x_5);
switch (lean_obj_tag(x_127)) {
case 0:
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_9);
lean_inc(x_4);
x_128 = l___private_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_0__Lean_PrettyPrinter_Delaborator_TopDownAnalyze_valUnknown___redArg(x_4, x_17, x_20);
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
lean_dec(x_128);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_6);
x_131 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isFunLike(x_6, x_16, x_17, x_18, x_19, x_130);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
lean_dec(x_131);
x_134 = lean_ctor_get(x_18, 2);
lean_inc(x_134);
x_135 = l_Lean_getPPAnalyzeExplicitHoles(x_134);
lean_dec(x_134);
if (x_135 == 0)
{
lean_dec(x_132);
lean_dec(x_129);
lean_dec(x_6);
lean_dec(x_4);
x_35 = x_126;
x_36 = x_135;
x_37 = x_133;
goto block_46;
}
else
{
uint8_t x_136; 
x_136 = lean_unbox(x_129);
lean_dec(x_129);
if (x_136 == 0)
{
if (x_135 == 0)
{
lean_dec(x_132);
lean_dec(x_6);
lean_dec(x_4);
x_35 = x_126;
x_36 = x_135;
x_37 = x_133;
goto block_46;
}
else
{
if (x_123 == 0)
{
uint8_t x_137; 
x_137 = lean_unbox(x_132);
lean_dec(x_132);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; uint8_t x_140; 
x_138 = lean_box(x_7);
x_139 = lean_array_get(x_138, x_8, x_1);
x_140 = lean_unbox(x_139);
lean_dec(x_139);
if (x_140 == 0)
{
lean_object* x_141; 
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
x_141 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_checkpointDefEq(x_4, x_6, x_16, x_17, x_18, x_19, x_133);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; uint8_t x_144; 
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
lean_dec(x_141);
x_144 = lean_unbox(x_142);
lean_dec(x_142);
x_35 = x_126;
x_36 = x_144;
x_37 = x_143;
goto block_46;
}
else
{
uint8_t x_145; 
lean_dec(x_126);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_2);
x_145 = !lean_is_exclusive(x_141);
if (x_145 == 0)
{
return x_141;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_141, 0);
x_147 = lean_ctor_get(x_141, 1);
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_141);
x_148 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_147);
return x_148;
}
}
}
else
{
lean_dec(x_6);
lean_dec(x_4);
x_21 = x_126;
x_22 = x_13;
x_23 = x_133;
goto block_34;
}
}
else
{
lean_dec(x_6);
lean_dec(x_4);
x_21 = x_126;
x_22 = x_13;
x_23 = x_133;
goto block_34;
}
}
else
{
lean_dec(x_132);
lean_dec(x_6);
lean_dec(x_4);
x_21 = x_126;
x_22 = x_13;
x_23 = x_133;
goto block_34;
}
}
}
else
{
lean_dec(x_132);
lean_dec(x_6);
lean_dec(x_4);
x_21 = x_126;
x_22 = x_13;
x_23 = x_133;
goto block_34;
}
}
}
else
{
uint8_t x_149; 
lean_dec(x_129);
lean_dec(x_126);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_149 = !lean_is_exclusive(x_131);
if (x_149 == 0)
{
return x_131;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_ctor_get(x_131, 0);
x_151 = lean_ctor_get(x_131, 1);
lean_inc(x_151);
lean_inc(x_150);
lean_dec(x_131);
x_152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_151);
return x_152;
}
}
}
case 3:
{
lean_object* x_153; uint8_t x_154; 
x_153 = lean_ctor_get(x_18, 2);
lean_inc(x_153);
x_154 = l_Lean_getPPInstances(x_153);
if (x_154 == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_153);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
x_155 = lean_mk_string_unchecked("pp", 2, 2);
x_156 = lean_mk_string_unchecked("analysis", 8, 8);
x_157 = lean_mk_string_unchecked("skip", 4, 4);
x_158 = l_Lean_Name_mkStr3(x_155, x_156, x_157);
x_159 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBool(x_158, x_126, x_15, x_16, x_17, x_18, x_19, x_20);
x_160 = lean_ctor_get(x_159, 1);
lean_inc(x_160);
lean_dec(x_159);
x_84 = x_154;
x_85 = x_13;
x_86 = x_126;
x_87 = x_160;
goto block_98;
}
else
{
uint8_t x_161; 
x_161 = l_Lean_getPPAnalyzeCheckInstances(x_153);
lean_dec(x_153);
if (x_161 == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
x_162 = lean_mk_string_unchecked("pp", 2, 2);
x_163 = lean_mk_string_unchecked("analysis", 8, 8);
x_164 = lean_mk_string_unchecked("skip", 4, 4);
x_165 = l_Lean_Name_mkStr3(x_162, x_163, x_164);
x_166 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBool(x_165, x_126, x_15, x_16, x_17, x_18, x_19, x_20);
x_167 = lean_ctor_get(x_166, 1);
lean_inc(x_167);
lean_dec(x_166);
x_84 = x_161;
x_85 = x_13;
x_86 = x_126;
x_87 = x_167;
goto block_98;
}
else
{
lean_object* x_168; lean_object* x_169; 
x_168 = lean_box(0);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
x_169 = l_Lean_Meta_trySynthInstance(x_9, x_168, x_16, x_17, x_18, x_19, x_20);
if (lean_obj_tag(x_169) == 0)
{
lean_object* x_170; 
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
if (lean_obj_tag(x_170) == 1)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_171 = lean_ctor_get(x_169, 1);
lean_inc(x_171);
lean_dec(x_169);
x_172 = lean_ctor_get(x_170, 0);
lean_inc(x_172);
lean_dec(x_170);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
x_173 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_checkpointDefEq(x_172, x_6, x_16, x_17, x_18, x_19, x_171);
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_174; uint8_t x_175; 
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
x_175 = lean_unbox(x_174);
lean_dec(x_174);
if (x_175 == 0)
{
lean_object* x_176; lean_object* x_177; 
x_176 = lean_ctor_get(x_173, 1);
lean_inc(x_176);
lean_dec(x_173);
x_177 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_mvarName(x_4, x_16, x_17, x_18, x_19, x_176);
lean_dec(x_4);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_177, 1);
lean_inc(x_179);
lean_dec(x_177);
x_180 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_annotateNamedArg___redArg(x_178, x_13, x_126, x_15, x_16, x_17, x_18, x_19, x_179);
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_180, 1);
lean_inc(x_182);
lean_dec(x_180);
x_183 = lean_ctor_get(x_181, 1);
lean_inc(x_183);
lean_dec(x_181);
x_84 = x_161;
x_85 = x_183;
x_86 = x_126;
x_87 = x_182;
goto block_98;
}
else
{
uint8_t x_184; 
lean_dec(x_126);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_2);
x_184 = !lean_is_exclusive(x_177);
if (x_184 == 0)
{
return x_177;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_185 = lean_ctor_get(x_177, 0);
x_186 = lean_ctor_get(x_177, 1);
lean_inc(x_186);
lean_inc(x_185);
lean_dec(x_177);
x_187 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_187, 0, x_185);
lean_ctor_set(x_187, 1, x_186);
return x_187;
}
}
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; uint8_t x_196; 
lean_dec(x_4);
x_188 = lean_ctor_get(x_173, 1);
lean_inc(x_188);
lean_dec(x_173);
x_189 = lean_mk_string_unchecked("pp", 2, 2);
x_190 = lean_mk_string_unchecked("analysis", 8, 8);
x_191 = lean_mk_string_unchecked("skip", 4, 4);
x_192 = l_Lean_Name_mkStr3(x_189, x_190, x_191);
x_193 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBool(x_192, x_126, x_15, x_16, x_17, x_18, x_19, x_188);
x_194 = lean_ctor_get(x_193, 1);
lean_inc(x_194);
lean_dec(x_193);
x_195 = lean_box(0);
x_196 = lean_unbox(x_195);
x_84 = x_196;
x_85 = x_13;
x_86 = x_126;
x_87 = x_194;
goto block_98;
}
}
else
{
uint8_t x_197; 
lean_dec(x_126);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_2);
x_197 = !lean_is_exclusive(x_173);
if (x_197 == 0)
{
return x_173;
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_198 = lean_ctor_get(x_173, 0);
x_199 = lean_ctor_get(x_173, 1);
lean_inc(x_199);
lean_inc(x_198);
lean_dec(x_173);
x_200 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_200, 0, x_198);
lean_ctor_set(x_200, 1, x_199);
return x_200;
}
}
}
else
{
lean_object* x_201; 
lean_dec(x_170);
lean_dec(x_6);
x_201 = lean_ctor_get(x_169, 1);
lean_inc(x_201);
lean_dec(x_169);
x_99 = x_161;
x_100 = x_126;
x_101 = x_201;
goto block_113;
}
}
else
{
lean_object* x_202; lean_object* x_203; uint8_t x_204; 
lean_dec(x_6);
x_202 = lean_ctor_get(x_169, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_169, 1);
lean_inc(x_203);
lean_dec(x_169);
x_204 = l_Lean_Exception_isInterrupt(x_202);
if (x_204 == 0)
{
uint8_t x_205; 
x_205 = l_Lean_Exception_isRuntime(x_202);
x_114 = x_161;
x_115 = x_202;
x_116 = x_126;
x_117 = x_203;
x_118 = x_205;
goto block_120;
}
else
{
x_114 = x_161;
x_115 = x_202;
x_116 = x_126;
x_117 = x_203;
x_118 = x_204;
goto block_120;
}
}
}
}
}
default: 
{
lean_object* x_206; lean_object* x_207; uint8_t x_208; 
lean_dec(x_127);
lean_dec(x_9);
lean_dec(x_6);
lean_inc(x_4);
x_206 = l___private_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_0__Lean_PrettyPrinter_Delaborator_TopDownAnalyze_valUnknown___redArg(x_4, x_17, x_20);
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
x_208 = lean_unbox(x_207);
if (x_208 == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; uint8_t x_212; 
lean_dec(x_207);
x_209 = lean_ctor_get(x_206, 1);
lean_inc(x_209);
lean_dec(x_206);
x_210 = lean_box(x_7);
x_211 = lean_array_get(x_210, x_10, x_1);
x_212 = lean_unbox(x_211);
lean_dec(x_211);
if (x_212 == 0)
{
lean_dec(x_4);
x_47 = x_209;
x_48 = x_13;
x_49 = x_126;
goto block_58;
}
else
{
x_59 = x_126;
x_60 = x_212;
x_61 = x_209;
goto block_83;
}
}
else
{
lean_object* x_213; uint8_t x_214; 
x_213 = lean_ctor_get(x_206, 1);
lean_inc(x_213);
lean_dec(x_206);
x_214 = lean_unbox(x_207);
lean_dec(x_207);
x_59 = x_126;
x_60 = x_214;
x_61 = x_213;
goto block_83;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 2);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 3);
lean_inc(x_13);
x_14 = lean_ctor_get(x_2, 4);
lean_inc(x_14);
x_15 = lean_ctor_get_uint8(x_2, sizeof(void*)*5);
x_16 = lean_ctor_get(x_3, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_3, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_3, 2);
lean_inc(x_18);
x_19 = l_Lean_instInhabitedExpr;
x_20 = lean_array_get(x_19, x_12, x_1);
lean_dec(x_12);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_20);
x_21 = lean_infer_type(x_20, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_instInhabitedBool;
x_25 = lean_box(0);
x_26 = lean_array_get(x_19, x_13, x_1);
lean_dec(x_13);
x_27 = lean_box(x_24);
lean_inc(x_1);
lean_inc(x_20);
lean_inc(x_26);
x_28 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeArg___lam__0___boxed), 14, 4);
lean_closure_set(x_28, 0, x_26);
lean_closure_set(x_28, 1, x_20);
lean_closure_set(x_28, 2, x_27);
lean_closure_set(x_28, 3, x_1);
x_29 = l_Lean_Expr_getAppNumArgs(x_11);
lean_dec(x_11);
x_30 = lean_nat_add(x_29, x_1);
lean_dec(x_29);
x_31 = lean_array_get(x_25, x_14, x_1);
lean_dec(x_14);
x_32 = lean_unbox(x_31);
lean_dec(x_31);
x_33 = lean_box(x_15);
x_34 = lean_box(x_32);
x_35 = lean_box(x_24);
x_36 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeArg___lam__1___boxed), 20, 11);
lean_closure_set(x_36, 0, x_1);
lean_closure_set(x_36, 1, x_28);
lean_closure_set(x_36, 2, x_33);
lean_closure_set(x_36, 3, x_26);
lean_closure_set(x_36, 4, x_34);
lean_closure_set(x_36, 5, x_20);
lean_closure_set(x_36, 6, x_35);
lean_closure_set(x_36, 7, x_18);
lean_closure_set(x_36, 8, x_22);
lean_closure_set(x_36, 9, x_17);
lean_closure_set(x_36, 10, x_16);
x_37 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_spec__0___redArg(x_30, x_36, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_23);
lean_dec(x_30);
return x_37;
}
else
{
uint8_t x_38; 
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_21);
if (x_38 == 0)
{
return x_21;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_21, 0);
x_40 = lean_ctor_get(x_21, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_21);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeFn_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_instantiateMVars___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeFn_spec__0___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeFn_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_instantiateMVars___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeFn_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryFn___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeFn_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryFn___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeFn_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryFn___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeFn_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryFn___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeFn_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeFn(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_5);
lean_dec(x_5);
x_14 = l_Lean_Meta_withLetDecl___at___Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_13, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_6);
lean_dec(x_6);
x_15 = l_Lean_Meta_withLetDecl___at___Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_14, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet_spec__0___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet_spec__0___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingDomain___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLam_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingDomain___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLam_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingDomain___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLam_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingDomain___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLam_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLam_spec__1_spec__1_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = lean_unbox(x_5);
lean_dec(x_5);
x_15 = l_Lean_Meta_withLocalDecl___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLam_spec__1_spec__1_spec__1___redArg(x_1, x_13, x_3, x_4, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLam_spec__1_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_unbox(x_3);
lean_dec(x_3);
x_15 = lean_unbox(x_6);
lean_dec(x_6);
x_16 = l_Lean_Meta_withLocalDecl___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLam_spec__1_spec__1_spec__1(x_1, x_2, x_14, x_4, x_5, x_15, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLam_spec__1_spec__1___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLam_spec__1_spec__1___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLam_spec__1___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLam_spec__1___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLam_spec__1___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLam_spec__1___redArg___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeApp___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_2);
lean_dec(x_2);
x_12 = lean_unbox(x_3);
lean_dec(x_3);
x_13 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeApp___lam__0(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeApp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeApp(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeAppStaged___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_4);
lean_dec(x_4);
x_13 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeAppStaged___lam__0(x_1, x_2, x_3, x_12, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeAppStaged___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeAppStaged(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_6);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_8);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Array_anyMUnsafe_any___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit_spec__0(x_1, x_4, x_5);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit_spec__2_spec__2___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_unbox(x_1);
lean_dec(x_1);
x_14 = lean_unbox(x_2);
lean_dec(x_2);
x_15 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit_spec__2_spec__2___redArg___lam__0(x_13, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_6);
lean_dec(x_4);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit_spec__2_spec__2___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit_spec__2_spec__2___redArg___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit_spec__2_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_1);
lean_dec(x_1);
x_17 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit_spec__2_spec__2___redArg(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit_spec__2_spec__2___boxed(lean_object** _args) {
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
uint8_t x_18; lean_object* x_19; 
x_18 = lean_unbox(x_1);
lean_dec(x_1);
x_19 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit_spec__2_spec__2(x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_1);
lean_dec(x_1);
x_17 = l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit_spec__2___redArg(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit_spec__2___boxed(lean_object** _args) {
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
uint8_t x_18; lean_object* x_19; 
x_18 = lean_unbox(x_1);
lean_dec(x_1);
x_19 = l_Std_Range_forIn_x27_loop___at___Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit_spec__2(x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_3);
lean_dec(x_3);
x_16 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeArg___lam__0(x_1, x_2, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeArg___lam__1___boxed(lean_object** _args) {
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
_start:
{
uint8_t x_21; uint8_t x_22; uint8_t x_23; lean_object* x_24; 
x_21 = lean_unbox(x_3);
lean_dec(x_3);
x_22 = lean_unbox(x_5);
lean_dec(x_5);
x_23 = lean_unbox(x_7);
lean_dec(x_7);
x_24 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeArg___lam__1(x_1, x_2, x_21, x_4, x_22, x_6, x_23, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_1);
return x_24;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___Lean_PrettyPrinter_Delaborator_topDownAnalyze_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_apply_7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___Lean_PrettyPrinter_Delaborator_topDownAnalyze_spec__0___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___Lean_PrettyPrinter_Delaborator_topDownAnalyze_spec__0___redArg___lam__0), 8, 3);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_3);
lean_closure_set(x_10, 2, x_4);
x_11 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp___redArg(x_2, x_10, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
return x_11;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
return x_11;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_11);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___Lean_PrettyPrinter_Delaborator_topDownAnalyze_spec__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_withNewMCtxDepth___at___Lean_PrettyPrinter_Delaborator_topDownAnalyze_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_topDownAnalyze___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_MessageData_ofExpr(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_topDownAnalyze___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_topDownAnalyze___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_set(x_1, x_2, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_topDownAnalyze___lam__3(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_29; lean_object* x_30; lean_object* x_38; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint64_t x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_13 = lean_box(0);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_mk_empty_array_with_capacity(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_st_mk_ref(x_16, x_12);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_44 = lean_ctor_get(x_8, 0);
x_45 = lean_ctor_get(x_10, 2);
lean_inc(x_45);
x_46 = l_Lean_Elab_Term_setElabConfig(x_44);
x_47 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_46);
x_48 = lean_ctor_get_uint8(x_8, sizeof(void*)*7 + 8);
x_49 = lean_ctor_get(x_8, 1);
x_50 = lean_ctor_get(x_8, 2);
x_51 = lean_ctor_get(x_8, 3);
x_52 = lean_ctor_get(x_8, 4);
x_53 = lean_ctor_get(x_8, 5);
x_54 = lean_ctor_get(x_8, 6);
x_55 = lean_ctor_get_uint8(x_8, sizeof(void*)*7 + 9);
x_56 = lean_ctor_get_uint8(x_8, sizeof(void*)*7 + 10);
x_57 = l_Lean_getPPAnalyzeKnowsType(x_45);
lean_dec(x_45);
x_58 = l_Lean_SubExpr_mkRoot(x_2);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
x_59 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_59, 0, x_46);
lean_ctor_set(x_59, 1, x_49);
lean_ctor_set(x_59, 2, x_50);
lean_ctor_set(x_59, 3, x_51);
lean_ctor_set(x_59, 4, x_52);
lean_ctor_set(x_59, 5, x_53);
lean_ctor_set(x_59, 6, x_54);
lean_ctor_set_uint64(x_59, sizeof(void*)*7, x_47);
lean_ctor_set_uint8(x_59, sizeof(void*)*7 + 8, x_48);
lean_ctor_set_uint8(x_59, sizeof(void*)*7 + 9, x_55);
lean_ctor_set_uint8(x_59, sizeof(void*)*7 + 10, x_56);
x_60 = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set_uint8(x_60, sizeof(void*)*1, x_57);
lean_ctor_set_uint8(x_60, sizeof(void*)*1 + 1, x_57);
lean_ctor_set_uint8(x_60, sizeof(void*)*1 + 2, x_3);
lean_ctor_set_uint8(x_60, sizeof(void*)*1 + 3, x_3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_59);
lean_inc(x_18);
x_61 = l_Lean_Meta_withNewMCtxDepth___at___Lean_PrettyPrinter_Delaborator_topDownAnalyze_spec__0___redArg(x_4, x_3, x_60, x_18, x_59, x_9, x_10, x_11, x_19);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_59);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
lean_dec(x_61);
x_63 = lean_st_ref_get(x_18, x_62);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = lean_st_ref_get(x_18, x_65);
lean_dec(x_18);
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
lean_dec(x_66);
x_68 = lean_ctor_get(x_64, 0);
lean_inc(x_68);
lean_dec(x_64);
x_20 = x_68;
x_21 = x_67;
goto block_28;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; uint8_t x_107; 
lean_dec(x_18);
x_69 = lean_ctor_get(x_61, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_61, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_71 = x_61;
} else {
 lean_dec_ref(x_61);
 x_71 = lean_box(0);
}
x_107 = l_Lean_Exception_isInterrupt(x_69);
if (x_107 == 0)
{
uint8_t x_108; 
x_108 = l_Lean_Exception_isRuntime(x_69);
x_72 = x_108;
goto block_106;
}
else
{
x_72 = x_107;
goto block_106;
}
block_106:
{
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_73 = lean_mk_string_unchecked("error", 5, 5);
x_74 = l_Lean_Name_mkStr3(x_5, x_6, x_73);
lean_inc(x_74);
x_75 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0(x_74, x_59, x_9, x_10, x_11, x_70);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_unbox(x_76);
lean_dec(x_76);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_74);
lean_dec(x_71);
lean_dec(x_69);
x_78 = lean_ctor_get(x_75, 1);
lean_inc(x_78);
lean_dec(x_75);
x_79 = lean_box(0);
lean_inc(x_9);
x_80 = lean_apply_6(x_7, x_79, x_59, x_9, x_10, x_11, x_78);
x_38 = x_80;
goto block_43;
}
else
{
uint8_t x_81; 
x_81 = !lean_is_exclusive(x_75);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_82 = lean_ctor_get(x_75, 1);
x_83 = lean_ctor_get(x_75, 0);
lean_dec(x_83);
x_84 = lean_mk_string_unchecked("failed ", 7, 7);
x_85 = l_Lean_stringToMessageData(x_84);
lean_dec(x_84);
x_86 = l_Lean_Exception_toMessageData(x_69);
lean_ctor_set_tag(x_75, 7);
lean_ctor_set(x_75, 1, x_86);
lean_ctor_set(x_75, 0, x_85);
x_87 = lean_mk_string_unchecked("", 0, 0);
x_88 = l_Lean_stringToMessageData(x_87);
lean_dec(x_87);
if (lean_is_scalar(x_71)) {
 x_89 = lean_alloc_ctor(7, 2, 0);
} else {
 x_89 = x_71;
 lean_ctor_set_tag(x_89, 7);
}
lean_ctor_set(x_89, 0, x_75);
lean_ctor_set(x_89, 1, x_88);
x_90 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_74, x_89, x_59, x_9, x_10, x_11, x_82);
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
lean_dec(x_90);
x_92 = lean_box(0);
lean_inc(x_9);
x_93 = lean_apply_6(x_7, x_92, x_59, x_9, x_10, x_11, x_91);
x_38 = x_93;
goto block_43;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_94 = lean_ctor_get(x_75, 1);
lean_inc(x_94);
lean_dec(x_75);
x_95 = lean_mk_string_unchecked("failed ", 7, 7);
x_96 = l_Lean_stringToMessageData(x_95);
lean_dec(x_95);
x_97 = l_Lean_Exception_toMessageData(x_69);
x_98 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
x_99 = lean_mk_string_unchecked("", 0, 0);
x_100 = l_Lean_stringToMessageData(x_99);
lean_dec(x_99);
if (lean_is_scalar(x_71)) {
 x_101 = lean_alloc_ctor(7, 2, 0);
} else {
 x_101 = x_71;
 lean_ctor_set_tag(x_101, 7);
}
lean_ctor_set(x_101, 0, x_98);
lean_ctor_set(x_101, 1, x_100);
x_102 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_74, x_101, x_59, x_9, x_10, x_11, x_94);
x_103 = lean_ctor_get(x_102, 1);
lean_inc(x_103);
lean_dec(x_102);
x_104 = lean_box(0);
lean_inc(x_9);
x_105 = lean_apply_6(x_7, x_104, x_59, x_9, x_10, x_11, x_103);
x_38 = x_105;
goto block_43;
}
}
}
else
{
lean_dec(x_71);
lean_dec(x_59);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_29 = x_69;
x_30 = x_70;
goto block_37;
}
}
}
block_28:
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
lean_inc(x_20);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_20);
x_23 = l_Lean_PrettyPrinter_Delaborator_topDownAnalyze___lam__2(x_9, x_1, x_22, x_21);
lean_dec(x_22);
lean_dec(x_9);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
lean_ctor_set(x_23, 0, x_20);
return x_23;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_20);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
block_37:
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_box(0);
x_32 = l_Lean_PrettyPrinter_Delaborator_topDownAnalyze___lam__2(x_9, x_1, x_31, x_30);
lean_dec(x_9);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_32, 0);
lean_dec(x_34);
lean_ctor_set_tag(x_32, 1);
lean_ctor_set(x_32, 0, x_29);
return x_32;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_29);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
block_43:
{
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_20 = x_39;
x_21 = x_40;
goto block_28;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_38, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_38, 1);
lean_inc(x_42);
lean_dec(x_38);
x_29 = x_41;
x_30 = x_42;
goto block_37;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_topDownAnalyze(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_7 = lean_st_ref_get(x_3, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_topDownAnalyze___lam__0___boxed), 7, 1);
lean_closure_set(x_10, 0, x_1);
x_11 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_topDownAnalyze___lam__1___boxed), 6, 0);
x_12 = lean_mk_string_unchecked("pp", 2, 2);
x_13 = lean_mk_string_unchecked("analyze", 7, 7);
lean_inc(x_13);
lean_inc(x_12);
x_14 = l_Lean_Name_mkStr2(x_12, x_13);
x_15 = lean_box(0);
x_16 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___boxed), 8, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_topDownAnalyze___lam__3___boxed), 12, 7);
lean_closure_set(x_17, 0, x_8);
lean_closure_set(x_17, 1, x_1);
lean_closure_set(x_17, 2, x_15);
lean_closure_set(x_17, 3, x_16);
lean_closure_set(x_17, 4, x_12);
lean_closure_set(x_17, 5, x_13);
lean_closure_set(x_17, 6, x_11);
x_18 = lean_box(1);
x_19 = lean_mk_string_unchecked("", 0, 0);
x_20 = lean_unbox(x_18);
x_21 = l_Lean_withTraceNode___at___Lean_Meta_processPostponed_spec__0(lean_box(0), x_14, x_10, x_17, x_20, x_19, x_2, x_3, x_4, x_5, x_9);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___Lean_PrettyPrinter_Delaborator_topDownAnalyze_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = l_Lean_Meta_withNewMCtxDepth___at___Lean_PrettyPrinter_Delaborator_topDownAnalyze_spec__0___redArg(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___Lean_PrettyPrinter_Delaborator_topDownAnalyze_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = l_Lean_Meta_withNewMCtxDepth___at___Lean_PrettyPrinter_Delaborator_topDownAnalyze_spec__0(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_topDownAnalyze___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Delaborator_topDownAnalyze___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_topDownAnalyze___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Delaborator_topDownAnalyze___lam__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_topDownAnalyze___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Delaborator_topDownAnalyze___lam__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_topDownAnalyze___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_3);
lean_dec(x_3);
x_14 = l_Lean_PrettyPrinter_Delaborator_topDownAnalyze___lam__3(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_8);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_10869_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_2 = lean_mk_string_unchecked("pp", 2, 2);
x_3 = lean_mk_string_unchecked("analyze", 7, 7);
lean_inc(x_3);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(0);
x_6 = lean_box(0);
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
lean_inc(x_7);
x_8 = l_Lean_Name_str___override(x_6, x_7);
x_9 = lean_mk_string_unchecked("PrettyPrinter", 13, 13);
lean_inc(x_9);
x_10 = l_Lean_Name_str___override(x_8, x_9);
x_11 = lean_mk_string_unchecked("Delaborator", 11, 11);
lean_inc(x_11);
x_12 = l_Lean_Name_str___override(x_10, x_11);
x_13 = lean_mk_string_unchecked("initFn", 6, 6);
x_14 = l_Lean_Name_str___override(x_12, x_13);
x_15 = lean_mk_string_unchecked("_@", 2, 2);
x_16 = l_Lean_Name_str___override(x_14, x_15);
x_17 = l_Lean_Name_str___override(x_16, x_7);
x_18 = l_Lean_Name_str___override(x_17, x_9);
x_19 = l_Lean_Name_str___override(x_18, x_11);
x_20 = lean_mk_string_unchecked("TopDownAnalyze", 14, 14);
x_21 = l_Lean_Name_str___override(x_19, x_20);
x_22 = lean_mk_string_unchecked("_hyg", 4, 4);
x_23 = l_Lean_Name_str___override(x_21, x_22);
x_24 = lean_unsigned_to_nat(10869u);
x_25 = l_Lean_Name_num___override(x_23, x_24);
x_26 = lean_unbox(x_5);
lean_inc(x_25);
x_27 = l_Lean_registerTraceClass(x_4, x_26, x_25, x_1);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_mk_string_unchecked("annotate", 8, 8);
lean_inc(x_3);
lean_inc(x_2);
x_30 = l_Lean_Name_mkStr3(x_2, x_3, x_29);
x_31 = lean_box(1);
x_32 = lean_unbox(x_31);
lean_inc(x_25);
x_33 = l_Lean_registerTraceClass(x_30, x_32, x_25, x_28);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; 
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_mk_string_unchecked("tryUnify", 8, 8);
lean_inc(x_3);
lean_inc(x_2);
x_36 = l_Lean_Name_mkStr3(x_2, x_3, x_35);
x_37 = lean_unbox(x_31);
lean_inc(x_25);
x_38 = l_Lean_registerTraceClass(x_36, x_37, x_25, x_34);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_mk_string_unchecked("error", 5, 5);
x_41 = l_Lean_Name_mkStr3(x_2, x_3, x_40);
x_42 = lean_unbox(x_31);
x_43 = l_Lean_registerTraceClass(x_41, x_42, x_25, x_39);
return x_43;
}
else
{
lean_dec(x_25);
lean_dec(x_3);
lean_dec(x_2);
return x_38;
}
}
else
{
lean_dec(x_25);
lean_dec(x_3);
lean_dec(x_2);
return x_33;
}
}
else
{
lean_dec(x_25);
lean_dec(x_3);
lean_dec(x_2);
return x_27;
}
}
}
lean_object* initialize_Lean_Data_RBMap(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_SynthInstance(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_CtorRecognizer(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_FindMVar(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_FindLevelMVar(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_CollectLevelParams(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_ReplaceLevel(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_PrettyPrinter_Delaborator_FieldNotation(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_PrettyPrinter_Delaborator_Options(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_PrettyPrinter_Delaborator_SubExpr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Config(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_PrettyPrinter_Delaborator_TopDownAnalyze(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_RBMap(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_SynthInstance(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_CtorRecognizer(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_FindMVar(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_FindLevelMVar(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_CollectLevelParams(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_ReplaceLevel(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_PrettyPrinter_Delaborator_FieldNotation(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_PrettyPrinter_Delaborator_Options(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_PrettyPrinter_Delaborator_SubExpr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Config(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
if (builtin) {res = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_7_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_pp_analyze = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_pp_analyze);
lean_dec_ref(res);
}if (builtin) {res = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_47_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_pp_analyze_checkInstances = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_pp_analyze_checkInstances);
lean_dec_ref(res);
}if (builtin) {res = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_87_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_pp_analyze_typeAscriptions = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_pp_analyze_typeAscriptions);
lean_dec_ref(res);
}if (builtin) {res = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_127_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_pp_analyze_trustSubst = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_pp_analyze_trustSubst);
lean_dec_ref(res);
}if (builtin) {res = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_167_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_pp_analyze_trustOfNat = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_pp_analyze_trustOfNat);
lean_dec_ref(res);
}if (builtin) {res = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_207_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_pp_analyze_trustOfScientific = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_pp_analyze_trustOfScientific);
lean_dec_ref(res);
}if (builtin) {res = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_247_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_pp_analyze_trustSubtypeMk = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_pp_analyze_trustSubtypeMk);
lean_dec_ref(res);
}if (builtin) {res = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_287_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_pp_analyze_trustId = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_pp_analyze_trustId);
lean_dec_ref(res);
}if (builtin) {res = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_327_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_pp_analyze_trustKnownFOType2TypeHOFuns = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_pp_analyze_trustKnownFOType2TypeHOFuns);
lean_dec_ref(res);
}if (builtin) {res = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_367_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_pp_analyze_omitMax = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_pp_analyze_omitMax);
lean_dec_ref(res);
}if (builtin) {res = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_407_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_pp_analyze_knowsType = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_pp_analyze_knowsType);
lean_dec_ref(res);
}if (builtin) {res = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_447_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_pp_analyze_explicitHoles = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_pp_analyze_explicitHoles);
lean_dec_ref(res);
}l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_instInhabitedContext = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_instInhabitedContext();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_instInhabitedContext);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_instMonadReaderOfSubExprAnalyzeM = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_instMonadReaderOfSubExprAnalyzeM();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_instMonadReaderOfSubExprAnalyzeM);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_instMonadWithReaderOfSubExprAnalyzeM = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_instMonadWithReaderOfSubExprAnalyzeM();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_instMonadWithReaderOfSubExprAnalyzeM);
if (builtin) {res = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_3632_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeFailureId = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeFailureId);
lean_dec_ref(res);
}if (builtin) {res = l_Lean_PrettyPrinter_Delaborator_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_10869_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
