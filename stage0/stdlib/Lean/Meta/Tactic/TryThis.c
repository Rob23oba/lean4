// Lean compiler output
// Module: Lean.Meta.Tactic.TryThis
// Imports: Lean.Server.CodeActions Lean.Widget.UserWidget Lean.Data.Json.Elab Lean.Data.Lsp.Utf16 Lean.Meta.CollectFVars Lean.Meta.Tactic.ExposeNames
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
lean_object* lean_format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_pp_mvars;
lean_object* l_Lean_FileMap_utf8RangeToLspRange(lean_object*, lean_object*);
double lean_float_mul(double, double);
lean_object* l_Lean_Server_Snapshots_Snapshot_infoTree(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextFull___at___Lean_Meta_recordSynthPendingFailure_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__1_spec__1___redArg(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addExactSuggestions(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_Suggestion_toJsonAndInfoM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
lean_object* l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_InfoTree_foldInfo___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_Tactic_TryThis_tryThisProvider_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addSuggestionCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentD(lean_object*);
uint8_t l_Array_isEmpty___redArg(lean_object*);
lean_object* l_Lean_PrettyPrinter_delab(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_tryThisWidget;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_joinSep(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addTermSuggestion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_tryThisProvider___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success;
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionText_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addSuggestionCore_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_instImpl____x40_Lean_Meta_Tactic_TryThis___hyg_52_;
lean_object* l_Lean_Lsp_WorkspaceEdit_ofTextEdit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addTermSuggestion___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at___Lean_Elab_Tactic_getMainTarget_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_tryThisProvider(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_instSuggestionStyleInhabited;
uint64_t lean_string_hash(lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_ofRange(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_format_inputWidth;
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Elab_Tactic_SavedState_restore(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepth;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_Tactic_TryThis_addTermSuggestions_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_getIndentAndColumn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_tryThisProvider___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis;
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_id___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisProvider__1(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Meta_Tactic_TryThis_addSuggestions_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisWidget__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_getInputWidth(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addSuggestionCore___lam__0(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addTermSuggestions___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logInfo___at___Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_String_findLineStart(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__1_spec__1(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
double lean_float_add(double, double);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_getIndentAndColumn___lam__0___boxed(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_instToMessageDataSuggestion___lam__0(lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_logInfo___at___Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_Tactic_TryThis_tryThisProvider_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestionText;
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_Tactic_TryThis_tryThisProvider_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_log___at___Lean_logError___at___Lean_Elab_logException___at___Lean_Elab_Tactic_closeUsingOrAdmit_spec__0_spec__2_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_TryThis_getIndentAndColumn___lam__0(uint32_t);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestion;
lean_object* l_Lean_Option_register___at___Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Options___hyg_5__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_getIndentAndColumn___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_instToMessageDataSuggestionText;
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_Tactic_TryThis_addSuggestions_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_instCoeStringSuggestionText;
extern lean_object* l_Lean_MessageData_nil;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addExactSuggestion(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_instCoeSuggestionTextSuggestion;
lean_object* l_Lean_MessageData_ofConst(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___boxed(lean_object*);
double pow(double, double);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_initFn____x40_Lean_Meta_Tactic_TryThis___hyg_609_(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_addBuiltinCodeActionProvider(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addExactSuggestion___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_diagnostics;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_syntax_ident(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___Lean_Meta_Tactic_TryThis_addSuggestion_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible;
lean_object* l_Lean_Syntax_TSepArray_ofElems(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_saveState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__1(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0_spec__0(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__0(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
double l_Float_ofScientific(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_throwErrorAt___at___Lean_Meta_mkProjections_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_ppExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_String_findAux(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonRange____x40_Lean_Data_Lsp_Basic___hyg_615_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(lean_object*, lean_object*);
lean_object* l_Lean_Widget_savePanelWidgetInfo(uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestions___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_instCoeStringSuggestionText___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_instToMessageDataSuggestion;
lean_object* l_Lean_Option_set___at___Lean_Environment_realizeConst_spec__2(lean_object*, lean_object*, uint8_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addSuggestionCore_spec__1(size_t, size_t, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Environment_mainModule(lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___Lean_Json_opt___at_____private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1558__spec__0_spec__0(size_t, size_t, lean_object*);
lean_object* lean_float_to_string(double);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addTermSuggestions(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addSuggestionCore_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_tryThisProvider___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestions(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_Tactic_TryThis_addTermSuggestions_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value(double, uint8_t);
lean_object* l_Lean_MessageData_sbracket(lean_object*);
lean_object* l_Lean_PrettyPrinter_ppCategory(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withoutRecover___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withExposedNames___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_instTypeNameTryThisInfo;
lean_object* l_Array_append(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_instToMessageDataSuggestionText___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_instSuggestionStyleToJson;
lean_object* l_Lean_Server_RequestM_readDoc___at___Lean_Server_RequestM_withWaitFindSnapAtPos_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_instCoeHeadTSyntaxConsSyntaxNodeKindNilSuggestionText___lam__0(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t l_instDecidableNot___redArg(uint8_t);
lean_object* l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(lean_object*, lean_object*);
uint8_t lean_float_decLe(double, double);
lean_object* l_Lean_Server_FileWorker_EditableDocument_versionedIdentifier(lean_object*);
lean_object* l_Lean_Syntax_getRange_x3f(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_Tactic_TryThis_tryThisProvider_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addSuggestionCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withoutErrToSorry___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_maybeWithoutRecovery_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_instCoeSuggestionTextSuggestion___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_getInputWidth___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Widget_addBuiltinModule(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Meta_getMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_instCoeHeadTSyntaxConsSyntaxNodeKindNilSuggestionText(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
double round(double);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestion___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionText_prettyExtra(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* l_Lean_pp_mvars_anonymous;
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___Lean_Meta_Tactic_TryThis_addSuggestion_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addExactSuggestions___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addSuggestionCore_spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_String_toSubstring_x27(lean_object*);
uint8_t l_instDecidableEqChar(uint32_t, uint32_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_Tactic_TryThis_addSuggestions_spec__0(size_t, size_t, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Meta_Tactic_TryThis_addSuggestions_spec__1(lean_object*, size_t, size_t, lean_object*);
uint32_t l_Char_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addSuggestionCore_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addSuggestionCore(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
double lean_float_sub(double, double);
lean_object* l_Lean_Elab_pushInfoLeaf___at___Lean_Elab_addConstInfo___at___Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_tryThisWidget() {
_start:
{
lean_object* x_1; uint64_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_mk_string_unchecked("\nimport * as React from 'react';\nimport { EditorContext, EnvPosContext } from '@leanprover/infoview';\nconst e = React.createElement;\nexport default function ({ suggestions, range, header, isInline, style }) {\n  const pos = React.useContext(EnvPosContext)\n  const editorConnection = React.useContext(EditorContext)\n  const defStyle = style || {\n    className: 'link pointer dim',\n    style: { color: 'var(--vscode-textLink-foreground)' }\n  }\n\n  // Construct the children of the HTML element for a given suggestion.\n  function makeSuggestion({ suggestion, preInfo, postInfo, style }) {\n    function onClick() {\n      editorConnection.api.applyEdit({\n        changes: { [pos.uri]: [{ range, newText: suggestion }] }\n      })\n    }\n    return [\n      preInfo,\n      e('span', { onClick, title: 'Apply suggestion', ...style || defStyle }, suggestion),\n      postInfo\n    ]\n  }\n\n  // Choose between an inline 'Try this'-like display and a list-based 'Try these'-like display.\n  let inner = null\n  if (isInline) {\n    inner = e('div', { className: 'ml1' },\n      e('pre', { className: 'font-code pre-wrap' }, header, makeSuggestion(suggestions[0])))\n  } else {\n    inner = e('div', { className: 'ml1' },\n      e('pre', { className: 'font-code pre-wrap' }, header),\n      e('ul', { style: { paddingInlineStart: '20px' } }, suggestions.map(s =>\n        e('li', { className: 'font-code pre-wrap' }, makeSuggestion(s)))))\n  }\n  return e('details', { open: true },\n    e('summary', { className: 'mv2 pointer' }, 'Suggestions'),\n    inner)\n}", 1528, 1528);
x_2 = lean_string_hash(x_1);
x_3 = lean_box_uint64(x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisWidget__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Meta", 4, 4);
x_4 = lean_mk_string_unchecked("Tactic", 6, 6);
x_5 = lean_mk_string_unchecked("TryThis", 7, 7);
x_6 = lean_mk_string_unchecked("tryThisWidget", 13, 13);
x_7 = l_Lean_Name_mkStr5(x_2, x_3, x_4, x_5, x_6);
x_8 = l_Lean_Meta_Tactic_TryThis_tryThisWidget;
x_9 = l_Lean_Widget_addBuiltinModule(x_7, x_8, x_1);
return x_9;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_instImpl____x40_Lean_Meta_Tactic_TryThis___hyg_52_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Meta", 4, 4);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("TryThis", 7, 7);
x_5 = lean_mk_string_unchecked("TryThisInfo", 11, 11);
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_instTypeNameTryThisInfo() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Tactic_TryThis_instImpl____x40_Lean_Meta_Tactic_TryThis___hyg_52_;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_Tactic_TryThis_tryThisProvider_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_5, 1);
x_9 = lean_nat_dec_lt(x_7, x_8);
if (x_9 == 0)
{
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_36; uint8_t x_37; lean_object* x_38; 
x_10 = lean_array_fget(x_1, x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_13 = x_10;
} else {
 lean_dec_ref(x_10);
 x_13 = lean_box(0);
}
x_36 = lean_unsigned_to_nat(0u);
x_37 = lean_nat_dec_eq(x_7, x_36);
if (lean_obj_tag(x_12) == 0)
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_mk_string_unchecked("Try this: ", 10, 10);
x_48 = lean_string_append(x_47, x_11);
x_38 = x_48;
goto block_46;
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_4, 0);
lean_inc(x_49);
x_50 = lean_string_append(x_49, x_11);
x_38 = x_50;
goto block_46;
}
}
else
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_12, 0);
lean_inc(x_51);
lean_dec(x_12);
x_38 = x_51;
goto block_46;
}
block_35:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_21 = lean_box(0);
x_22 = l_Lean_Server_FileWorker_EditableDocument_versionedIdentifier(x_2);
lean_inc(x_3);
x_23 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_23, 0, x_3);
lean_ctor_set(x_23, 1, x_11);
lean_ctor_set(x_23, 2, x_21);
lean_ctor_set(x_23, 3, x_17);
x_24 = l_Lean_Lsp_WorkspaceEdit_ofTextEdit(x_22, x_23);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_box(0);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_28, 0, x_14);
lean_ctor_set(x_28, 1, x_19);
lean_ctor_set(x_28, 2, x_16);
lean_ctor_set(x_28, 3, x_15);
lean_ctor_set(x_28, 4, x_18);
lean_ctor_set(x_28, 5, x_20);
lean_ctor_set(x_28, 6, x_21);
lean_ctor_set(x_28, 7, x_25);
lean_ctor_set(x_28, 8, x_26);
lean_ctor_set(x_28, 9, x_27);
x_29 = lean_box(0);
if (lean_is_scalar(x_13)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_13;
}
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_array_push(x_6, x_30);
x_32 = lean_ctor_get(x_5, 2);
x_33 = lean_nat_add(x_7, x_32);
lean_dec(x_7);
x_6 = x_31;
x_7 = x_33;
goto _start;
}
block_46:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_box(0);
x_40 = lean_mk_string_unchecked("quickfix", 8, 8);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = lean_box(0);
if (x_37 == 0)
{
lean_object* x_43; 
x_43 = lean_box(0);
x_14 = x_39;
x_15 = x_41;
x_16 = x_38;
x_17 = x_39;
x_18 = x_42;
x_19 = x_39;
x_20 = x_43;
goto block_35;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_box(x_37);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_44);
x_14 = x_39;
x_15 = x_41;
x_16 = x_38;
x_17 = x_39;
x_18 = x_42;
x_19 = x_39;
x_20 = x_45;
goto block_35;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_Tactic_TryThis_tryThisProvider_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_Tactic_TryThis_tryThisProvider_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_tryThisProvider___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_5) == 9)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_7, 0);
x_9 = lean_ctor_get(x_7, 1);
x_10 = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(x_9, x_1);
if (lean_obj_tag(x_10) == 0)
{
lean_dec(x_2);
return x_6;
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = lean_ctor_get(x_11, 2);
x_16 = lean_box(0);
x_17 = lean_unbox(x_16);
x_18 = l_Lean_Syntax_getRange_x3f(x_8, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_free_object(x_11);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_2);
return x_6;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_ctor_get(x_2, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_ctor_get(x_21, 3);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Lean_FileMap_utf8RangeToLspRange(x_22, x_19);
lean_dec(x_19);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_ctor_get(x_3, 3);
x_27 = lean_ctor_get(x_26, 1);
x_28 = lean_ctor_get(x_27, 0);
x_29 = lean_nat_dec_le(x_25, x_28);
lean_dec(x_25);
if (x_29 == 0)
{
lean_dec(x_23);
lean_free_object(x_11);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_2);
return x_6;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_30 = lean_ctor_get(x_26, 0);
x_31 = lean_ctor_get(x_30, 0);
x_32 = lean_ctor_get(x_23, 1);
lean_inc(x_32);
lean_dec(x_23);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_nat_dec_le(x_31, x_33);
lean_dec(x_33);
if (x_34 == 0)
{
lean_free_object(x_11);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_2);
return x_6;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_unsigned_to_nat(0u);
x_36 = lean_array_get_size(x_14);
x_37 = lean_unsigned_to_nat(1u);
lean_ctor_set(x_11, 2, x_37);
lean_ctor_set(x_11, 1, x_36);
lean_ctor_set(x_11, 0, x_35);
x_38 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_Tactic_TryThis_tryThisProvider_spec__0___redArg(x_14, x_2, x_13, x_15, x_11, x_6, x_35);
lean_dec(x_11);
lean_dec(x_2);
lean_dec(x_14);
return x_38;
}
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; 
x_39 = lean_ctor_get(x_11, 0);
x_40 = lean_ctor_get(x_11, 1);
x_41 = lean_ctor_get(x_11, 2);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_11);
x_42 = lean_box(0);
x_43 = lean_unbox(x_42);
x_44 = l_Lean_Syntax_getRange_x3f(x_8, x_43);
if (lean_obj_tag(x_44) == 0)
{
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_2);
return x_6;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_ctor_get(x_2, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
lean_dec(x_46);
x_48 = lean_ctor_get(x_47, 3);
lean_inc(x_48);
lean_dec(x_47);
x_49 = l_Lean_FileMap_utf8RangeToLspRange(x_48, x_45);
lean_dec(x_45);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
lean_dec(x_50);
x_52 = lean_ctor_get(x_3, 3);
x_53 = lean_ctor_get(x_52, 1);
x_54 = lean_ctor_get(x_53, 0);
x_55 = lean_nat_dec_le(x_51, x_54);
lean_dec(x_51);
if (x_55 == 0)
{
lean_dec(x_49);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_2);
return x_6;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_56 = lean_ctor_get(x_52, 0);
x_57 = lean_ctor_get(x_56, 0);
x_58 = lean_ctor_get(x_49, 1);
lean_inc(x_58);
lean_dec(x_49);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
lean_dec(x_58);
x_60 = lean_nat_dec_le(x_57, x_59);
lean_dec(x_59);
if (x_60 == 0)
{
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_2);
return x_6;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_61 = lean_unsigned_to_nat(0u);
x_62 = lean_array_get_size(x_40);
x_63 = lean_unsigned_to_nat(1u);
x_64 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_62);
lean_ctor_set(x_64, 2, x_63);
x_65 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_Tactic_TryThis_tryThisProvider_spec__0___redArg(x_40, x_2, x_39, x_41, x_64, x_6, x_61);
lean_dec(x_64);
lean_dec(x_2);
lean_dec(x_40);
return x_65;
}
}
}
}
}
}
else
{
lean_dec(x_2);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_tryThisProvider(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Server_RequestM_readDoc___at___Lean_Server_RequestM_withWaitFindSnapAtPos_spec__0(x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = l_Lean_Meta_Tactic_TryThis_instImpl____x40_Lean_Meta_Tactic_TryThis___hyg_52_;
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_TryThis_tryThisProvider___lam__0___boxed), 6, 3);
lean_closure_set(x_9, 0, x_8);
lean_closure_set(x_9, 1, x_7);
lean_closure_set(x_9, 2, x_1);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_mk_empty_array_with_capacity(x_10);
x_12 = l_Lean_Server_Snapshots_Snapshot_infoTree(x_2);
x_13 = l_Lean_Elab_InfoTree_foldInfo___redArg(x_9, x_11, x_12);
lean_ctor_set(x_5, 0, x_13);
return x_5;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_14 = lean_ctor_get(x_5, 0);
x_15 = lean_ctor_get(x_5, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_5);
x_16 = l_Lean_Meta_Tactic_TryThis_instImpl____x40_Lean_Meta_Tactic_TryThis___hyg_52_;
x_17 = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_TryThis_tryThisProvider___lam__0___boxed), 6, 3);
lean_closure_set(x_17, 0, x_16);
lean_closure_set(x_17, 1, x_14);
lean_closure_set(x_17, 2, x_1);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_mk_empty_array_with_capacity(x_18);
x_20 = l_Lean_Server_Snapshots_Snapshot_infoTree(x_2);
x_21 = l_Lean_Elab_InfoTree_foldInfo___redArg(x_17, x_19, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_15);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_Tactic_TryThis_tryThisProvider_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_Tactic_TryThis_tryThisProvider_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_Tactic_TryThis_tryThisProvider_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_Tactic_TryThis_tryThisProvider_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_tryThisProvider___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Tactic_TryThis_tryThisProvider___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_tryThisProvider___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Tactic_TryThis_tryThisProvider(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisProvider__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Meta", 4, 4);
x_4 = lean_mk_string_unchecked("Tactic", 6, 6);
x_5 = lean_mk_string_unchecked("TryThis", 7, 7);
x_6 = lean_mk_string_unchecked("tryThisProvider", 15, 15);
x_7 = l_Lean_Name_mkStr5(x_2, x_3, x_4, x_5, x_6);
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_TryThis_tryThisProvider___boxed), 4, 0);
x_9 = l_Lean_Server_addBuiltinCodeActionProvider(x_7, x_8, x_1);
return x_9;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_TryThis_getIndentAndColumn___lam__0(uint32_t x_1) {
_start:
{
lean_object* x_2; uint32_t x_3; uint8_t x_4; uint8_t x_5; 
x_2 = lean_unsigned_to_nat(32u);
x_3 = l_Char_ofNat(x_2);
x_4 = l_instDecidableEqChar(x_1, x_3);
x_5 = l_instDecidableNot___redArg(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_getIndentAndColumn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_TryThis_getIndentAndColumn___lam__0___boxed), 1, 0);
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
lean_inc(x_5);
x_6 = l_String_findLineStart(x_4, x_5);
lean_inc(x_6);
x_7 = l_String_findAux(x_4, x_3, x_5, x_6);
x_8 = lean_nat_sub(x_7, x_6);
lean_dec(x_7);
x_9 = lean_nat_sub(x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_getIndentAndColumn___lam__0___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Lean_Meta_Tactic_TryThis_getIndentAndColumn___lam__0(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_getIndentAndColumn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Tactic_TryThis_getIndentAndColumn(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_72; uint8_t x_73; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_4, 2);
lean_inc(x_10);
x_11 = l_Lean_pp_mvars_anonymous;
x_12 = lean_box(0);
x_13 = l_Lean_diagnostics;
x_14 = lean_box(0);
x_15 = lean_unbox(x_12);
x_16 = l_Lean_Option_set___at___Lean_Environment_realizeConst_spec__2(x_10, x_11, x_15);
x_17 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_16, x_13);
x_72 = lean_ctor_get(x_8, 0);
lean_inc(x_72);
lean_dec(x_8);
x_73 = l_Lean_Kernel_isDiagnosticsEnabled(x_72);
lean_dec(x_72);
if (x_73 == 0)
{
if (x_17 == 0)
{
x_18 = x_4;
x_19 = x_5;
x_20 = x_9;
goto block_37;
}
else
{
goto block_71;
}
}
else
{
if (x_17 == 0)
{
goto block_71;
}
else
{
x_18 = x_4;
x_19 = x_5;
x_20 = x_9;
goto block_37;
}
}
block_37:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_18, 3);
lean_inc(x_23);
x_24 = l_Lean_maxRecDepth;
x_25 = l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(x_16, x_24);
x_26 = lean_ctor_get(x_18, 5);
lean_inc(x_26);
x_27 = lean_ctor_get(x_18, 6);
lean_inc(x_27);
x_28 = lean_ctor_get(x_18, 7);
lean_inc(x_28);
x_29 = lean_ctor_get(x_18, 8);
lean_inc(x_29);
x_30 = lean_ctor_get(x_18, 9);
lean_inc(x_30);
x_31 = lean_ctor_get(x_18, 10);
lean_inc(x_31);
x_32 = lean_ctor_get(x_18, 11);
lean_inc(x_32);
x_33 = lean_ctor_get_uint8(x_18, sizeof(void*)*13 + 1);
x_34 = lean_ctor_get(x_18, 12);
lean_inc(x_34);
lean_dec(x_18);
x_35 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_35, 0, x_21);
lean_ctor_set(x_35, 1, x_22);
lean_ctor_set(x_35, 2, x_16);
lean_ctor_set(x_35, 3, x_23);
lean_ctor_set(x_35, 4, x_25);
lean_ctor_set(x_35, 5, x_26);
lean_ctor_set(x_35, 6, x_27);
lean_ctor_set(x_35, 7, x_28);
lean_ctor_set(x_35, 8, x_29);
lean_ctor_set(x_35, 9, x_30);
lean_ctor_set(x_35, 10, x_31);
lean_ctor_set(x_35, 11, x_32);
lean_ctor_set(x_35, 12, x_34);
lean_ctor_set_uint8(x_35, sizeof(void*)*13, x_17);
lean_ctor_set_uint8(x_35, sizeof(void*)*13 + 1, x_33);
x_36 = l_Lean_PrettyPrinter_delab(x_1, x_14, x_2, x_3, x_35, x_19, x_20);
return x_36;
}
block_71:
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_st_ref_take(x_5, x_9);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_40 = lean_ctor_get(x_38, 0);
x_41 = lean_ctor_get(x_38, 1);
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
x_43 = l_Lean_Kernel_enableDiag(x_42, x_17);
x_44 = lean_ctor_get(x_40, 1);
lean_inc(x_44);
x_45 = lean_ctor_get(x_40, 2);
lean_inc(x_45);
x_46 = lean_ctor_get(x_40, 3);
lean_inc(x_46);
x_47 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_47);
lean_inc(x_48);
lean_ctor_set(x_38, 1, x_48);
lean_ctor_set(x_38, 0, x_48);
x_49 = lean_ctor_get(x_40, 5);
lean_inc(x_49);
x_50 = lean_ctor_get(x_40, 6);
lean_inc(x_50);
x_51 = lean_ctor_get(x_40, 7);
lean_inc(x_51);
lean_dec(x_40);
x_52 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_52, 0, x_43);
lean_ctor_set(x_52, 1, x_44);
lean_ctor_set(x_52, 2, x_45);
lean_ctor_set(x_52, 3, x_46);
lean_ctor_set(x_52, 4, x_38);
lean_ctor_set(x_52, 5, x_49);
lean_ctor_set(x_52, 6, x_50);
lean_ctor_set(x_52, 7, x_51);
x_53 = lean_st_ref_set(x_5, x_52, x_41);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec(x_53);
x_18 = x_4;
x_19 = x_5;
x_20 = x_54;
goto block_37;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_55 = lean_ctor_get(x_38, 0);
x_56 = lean_ctor_get(x_38, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_38);
x_57 = lean_ctor_get(x_55, 0);
lean_inc(x_57);
x_58 = l_Lean_Kernel_enableDiag(x_57, x_17);
x_59 = lean_ctor_get(x_55, 1);
lean_inc(x_59);
x_60 = lean_ctor_get(x_55, 2);
lean_inc(x_60);
x_61 = lean_ctor_get(x_55, 3);
lean_inc(x_61);
x_62 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_63 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_63, 0, x_62);
lean_inc(x_63);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_63);
x_65 = lean_ctor_get(x_55, 5);
lean_inc(x_65);
x_66 = lean_ctor_get(x_55, 6);
lean_inc(x_66);
x_67 = lean_ctor_get(x_55, 7);
lean_inc(x_67);
lean_dec(x_55);
x_68 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_68, 0, x_58);
lean_ctor_set(x_68, 1, x_59);
lean_ctor_set(x_68, 2, x_60);
lean_ctor_set(x_68, 3, x_61);
lean_ctor_set(x_68, 4, x_64);
lean_ctor_set(x_68, 5, x_65);
lean_ctor_set(x_68, 6, x_66);
lean_ctor_set(x_68, 7, x_67);
x_69 = lean_st_ref_set(x_5, x_68, x_56);
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
lean_dec(x_69);
x_18 = x_4;
x_19 = x_5;
x_20 = x_70;
goto block_37;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_initFn____x40_Lean_Meta_Tactic_TryThis___hyg_609_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_2 = lean_mk_string_unchecked("format", 6, 6);
x_3 = lean_mk_string_unchecked("inputWidth", 10, 10);
lean_inc(x_3);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_unsigned_to_nat(100u);
x_6 = lean_mk_string_unchecked("", 0, 0);
x_7 = lean_mk_string_unchecked("ideal input width", 17, 17);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_6);
lean_ctor_set(x_8, 2, x_7);
x_9 = lean_mk_string_unchecked("Lean", 4, 4);
x_10 = lean_mk_string_unchecked("Meta", 4, 4);
x_11 = lean_mk_string_unchecked("Tactic", 6, 6);
x_12 = lean_mk_string_unchecked("TryThis", 7, 7);
x_13 = l_Lean_Name_mkStr6(x_9, x_10, x_11, x_12, x_2, x_3);
x_14 = l_Lean_Option_register___at___Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Options___hyg_5__spec__0(x_4, x_8, x_13, x_1);
lean_dec(x_8);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_getInputWidth(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Tactic_TryThis_format_inputWidth;
x_3 = l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_getInputWidth___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Tactic_TryThis_getInputWidth(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestionText() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_instToMessageDataSuggestionText___lam__0(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
lean_dec(x_1);
x_3 = l_Lean_MessageData_ofSyntax(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
lean_ctor_set_tag(x_1, 3);
x_5 = l_Lean_MessageData_ofFormat(x_1);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = l_Lean_MessageData_ofFormat(x_7);
return x_8;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_instToMessageDataSuggestionText() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_TryThis_instToMessageDataSuggestionText___lam__0), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_instCoeHeadTSyntaxConsSyntaxNodeKindNilSuggestionText___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_instCoeHeadTSyntaxConsSyntaxNodeKindNilSuggestionText(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_TryThis_instCoeHeadTSyntaxConsSyntaxNodeKindNilSuggestionText___lam__0), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_instCoeStringSuggestionText___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_instCoeStringSuggestionText() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_TryThis_instCoeStringSuggestionText___lam__0), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionText_pretty(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = l_Lean_PrettyPrinter_ppCategory(x_5, x_6, x_2, x_3, x_4);
return x_7;
}
else
{
uint8_t x_8; 
lean_dec(x_3);
lean_dec(x_2);
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; 
lean_ctor_set_tag(x_1, 3);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_4);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_4);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionText_prettyExtra(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_5, 2);
lean_inc(x_27);
x_28 = l_Lean_Meta_Tactic_TryThis_getInputWidth(x_27);
lean_dec(x_27);
x_10 = x_28;
x_11 = x_5;
x_12 = x_6;
x_13 = x_7;
goto block_26;
}
else
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_2, 0);
lean_inc(x_29);
lean_dec(x_2);
x_10 = x_29;
x_11 = x_5;
x_12 = x_6;
x_13 = x_7;
goto block_26;
}
block_26:
{
lean_object* x_14; 
x_14 = l_Lean_PrettyPrinter_ppCategory(x_8, x_9, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_format_pretty(x_16, x_10, x_3, x_4);
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
x_20 = lean_format_pretty(x_18, x_10, x_3, x_4);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
uint8_t x_22; 
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
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
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_30 = lean_ctor_get(x_1, 0);
lean_inc(x_30);
lean_dec(x_1);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_7);
return x_31;
}
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_instSuggestionStyleInhabited() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_instSuggestionStyleToJson() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_id___boxed), 2, 1);
lean_closure_set(x_1, 0, lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error(uint8_t x_1) {
_start:
{
lean_object* x_2; 
if (x_1 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_mk_string_unchecked("color", 5, 5);
x_15 = lean_mk_string_unchecked("var(--vscode-errorForeground)", 29, 29);
x_16 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_Json_mkObj(x_19);
x_2 = x_20;
goto block_13;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_21 = lean_mk_string_unchecked("color", 5, 5);
x_22 = lean_mk_string_unchecked("var(--vscode-errorForeground)", 29, 29);
x_23 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_mk_string_unchecked("textDecoration", 14, 14);
x_26 = lean_mk_string_unchecked("underline wavy var(--vscode-editorError-foreground) 1pt", 55, 55);
x_27 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_24);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_Json_mkObj(x_31);
x_2 = x_32;
goto block_13;
}
block_13:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_3 = lean_mk_string_unchecked("className", 9, 9);
x_4 = lean_mk_string_unchecked("pointer dim", 11, 11);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_mk_string_unchecked("style", 5, 5);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_2);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Lean_Json_mkObj(x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning(uint8_t x_1) {
_start:
{
if (x_1 == 0)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_mk_string_unchecked("className", 9, 9);
x_3 = lean_mk_string_unchecked("gold pointer dim", 16, 16);
x_4 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_4, 0, x_3);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_4);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
x_8 = l_Lean_Json_mkObj(x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_9 = lean_mk_string_unchecked("className", 9, 9);
x_10 = lean_mk_string_unchecked("gold pointer dim", 16, 16);
x_11 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_mk_string_unchecked("style", 5, 5);
x_14 = lean_mk_string_unchecked("textDecoration", 14, 14);
x_15 = lean_mk_string_unchecked("underline wavy var(--vscode-editorWarning-foreground) 1pt", 57, 57);
x_16 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_Json_mkObj(x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_13);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_18);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_12);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_Json_mkObj(x_23);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = lean_mk_string_unchecked("className", 9, 9);
x_2 = lean_mk_string_unchecked("information pointer dim", 23, 23);
x_3 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_3, 0, x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
x_7 = l_Lean_Json_mkObj(x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = lean_mk_string_unchecked("className", 9, 9);
x_2 = lean_mk_string_unchecked("goal-hyp pointer dim", 20, 20);
x_3 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_3, 0, x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
x_7 = l_Lean_Json_mkObj(x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = lean_mk_string_unchecked("className", 9, 9);
x_2 = lean_mk_string_unchecked("goal-inaccessible pointer dim", 29, 29);
x_3 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_3, 0, x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
x_7 = l_Lean_Json_mkObj(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value(double x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_15; double x_16; double x_65; lean_object* x_70; double x_71; uint8_t x_72; 
x_70 = lean_unsigned_to_nat(0u);
x_71 = lean_float_of_nat(x_70);
x_72 = lean_float_decLe(x_1, x_71);
if (x_72 == 0)
{
x_65 = x_1;
goto block_69;
}
else
{
x_65 = x_71;
goto block_69;
}
block_14:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Lean_Json_mkObj(x_12);
return x_13;
}
block_64:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; double x_25; double x_26; double x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; double x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; double x_37; double x_38; lean_object* x_39; double x_40; double x_41; lean_object* x_42; uint8_t x_43; double x_44; double x_45; double x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_17 = lean_mk_string_unchecked("className", 9, 9);
x_18 = lean_mk_string_unchecked("pointer dim", 11, 11);
x_19 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_mk_string_unchecked("style", 5, 5);
x_22 = lean_mk_string_unchecked("color", 5, 5);
x_23 = lean_mk_string_unchecked("hsl(", 4, 4);
x_24 = lean_unsigned_to_nat(120u);
x_25 = lean_float_of_nat(x_24);
x_26 = lean_float_mul(x_16, x_25);
x_27 = round(x_26);
x_28 = lean_float_to_string(x_27);
x_29 = lean_string_append(x_23, x_28);
lean_dec(x_28);
x_30 = lean_mk_string_unchecked(" 95% ", 5, 5);
x_31 = lean_string_append(x_29, x_30);
lean_dec(x_30);
x_32 = lean_unsigned_to_nat(60u);
x_33 = lean_float_of_nat(x_32);
x_34 = lean_unsigned_to_nat(5u);
x_35 = lean_box(1);
x_36 = lean_unbox(x_35);
x_37 = l_Float_ofScientific(x_34, x_36, x_15);
x_38 = lean_float_sub(x_16, x_37);
x_39 = lean_unsigned_to_nat(2u);
x_40 = lean_float_of_nat(x_39);
x_41 = pow(x_38, x_40);
x_42 = lean_unsigned_to_nat(75u);
x_43 = lean_unbox(x_35);
x_44 = l_Float_ofScientific(x_42, x_43, x_39);
x_45 = lean_float_add(x_41, x_44);
x_46 = lean_float_mul(x_33, x_45);
x_47 = lean_float_to_string(x_46);
x_48 = lean_string_append(x_31, x_47);
lean_dec(x_47);
x_49 = lean_mk_string_unchecked("%)", 2, 2);
x_50 = lean_string_append(x_48, x_49);
lean_dec(x_49);
x_51 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_51, 0, x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_22);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_box(0);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = l_Lean_Json_mkObj(x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_21);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_mk_string_unchecked("title", 5, 5);
if (x_2 == 0)
{
lean_object* x_58; 
x_58 = lean_mk_string_unchecked("Apply suggestion", 16, 16);
x_3 = x_57;
x_4 = x_56;
x_5 = x_20;
x_6 = x_53;
x_7 = x_58;
goto block_14;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_59 = lean_mk_string_unchecked("Apply suggestion (", 18, 18);
x_60 = lean_float_to_string(x_16);
x_61 = lean_string_append(x_59, x_60);
lean_dec(x_60);
x_62 = lean_mk_string_unchecked(")", 1, 1);
x_63 = lean_string_append(x_61, x_62);
lean_dec(x_62);
x_3 = x_57;
x_4 = x_56;
x_5 = x_20;
x_6 = x_53;
x_7 = x_63;
goto block_14;
}
}
block_69:
{
lean_object* x_66; double x_67; uint8_t x_68; 
x_66 = lean_unsigned_to_nat(1u);
x_67 = lean_float_of_nat(x_66);
x_68 = lean_float_decLe(x_65, x_67);
if (x_68 == 0)
{
x_15 = x_66;
x_16 = x_67;
goto block_64;
}
else
{
x_15 = x_66;
x_16 = x_65;
goto block_64;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
double x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox_float(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value(x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestion() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
x_4 = lean_box(0);
x_5 = lean_box(0);
x_6 = lean_box(0);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_4);
lean_ctor_set(x_8, 2, x_4);
lean_ctor_set(x_8, 3, x_5);
lean_ctor_set(x_8, 4, x_6);
lean_ctor_set(x_8, 5, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_Suggestion_toJsonAndInfoM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = l_Lean_Meta_Tactic_TryThis_SuggestionText_prettyExtra(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_20; lean_object* x_21; lean_object* x_32; lean_object* x_33; lean_object* x_40; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
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
x_52 = lean_mk_string_unchecked("suggestion", 10, 10);
lean_inc(x_10);
x_53 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_53, 0, x_10);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_box(0);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_ctor_get(x_1, 1);
lean_inc(x_57);
if (lean_obj_tag(x_57) == 0)
{
x_40 = x_56;
goto block_51;
}
else
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_mk_string_unchecked("preInfo", 7, 7);
lean_ctor_set_tag(x_57, 3);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_57);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_56);
x_40 = x_61;
goto block_51;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_62 = lean_ctor_get(x_57, 0);
lean_inc(x_62);
lean_dec(x_57);
x_63 = lean_mk_string_unchecked("preInfo", 7, 7);
x_64 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_64, 0, x_62);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_56);
x_40 = x_66;
goto block_51;
}
}
block_19:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_10);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
if (lean_is_scalar(x_12)) {
 x_18 = lean_alloc_ctor(0, 2, 0);
} else {
 x_18 = x_12;
}
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_13);
return x_18;
}
block_31:
{
lean_object* x_22; lean_object* x_23; 
x_22 = l_Lean_Json_mkObj(x_20);
x_23 = lean_ctor_get(x_1, 5);
lean_inc(x_23);
lean_dec(x_1);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
x_24 = lean_box(0);
x_13 = x_21;
x_14 = x_22;
x_15 = x_24;
goto block_19;
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_23, 0);
lean_inc(x_10);
x_27 = lean_apply_1(x_26, x_10);
lean_ctor_set(x_23, 0, x_27);
x_13 = x_21;
x_14 = x_22;
x_15 = x_23;
goto block_19;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_23, 0);
lean_inc(x_28);
lean_dec(x_23);
lean_inc(x_10);
x_29 = lean_apply_1(x_28, x_10);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_13 = x_21;
x_14 = x_22;
x_15 = x_30;
goto block_19;
}
}
}
block_39:
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_1, 3);
lean_inc(x_34);
if (lean_obj_tag(x_34) == 0)
{
x_20 = x_32;
x_21 = x_33;
goto block_31;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_mk_string_unchecked("style", 5, 5);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_32);
x_20 = x_38;
x_21 = x_33;
goto block_31;
}
}
block_51:
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_1, 2);
lean_inc(x_41);
if (lean_obj_tag(x_41) == 0)
{
x_32 = x_40;
x_33 = x_11;
goto block_39;
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_mk_string_unchecked("postInfo", 8, 8);
lean_ctor_set_tag(x_41, 3);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_41);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_40);
x_32 = x_45;
x_33 = x_11;
goto block_39;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_46 = lean_ctor_get(x_41, 0);
lean_inc(x_46);
lean_dec(x_41);
x_47 = lean_mk_string_unchecked("postInfo", 8, 8);
x_48 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_48, 0, x_46);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_40);
x_32 = x_50;
x_33 = x_11;
goto block_39;
}
}
}
}
else
{
uint8_t x_67; 
lean_dec(x_1);
x_67 = !lean_is_exclusive(x_9);
if (x_67 == 0)
{
return x_9;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_9, 0);
x_69 = lean_ctor_get(x_9, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_9);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_instToMessageDataSuggestion___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 4);
lean_inc(x_2);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l_Lean_MessageData_ofSyntax(x_4);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; 
lean_ctor_set_tag(x_3, 3);
x_7 = l_Lean_MessageData_ofFormat(x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = l_Lean_MessageData_ofFormat(x_9);
return x_10;
}
}
}
else
{
lean_object* x_11; 
lean_dec(x_1);
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
lean_dec(x_2);
return x_11;
}
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_instToMessageDataSuggestion() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_TryThis_instToMessageDataSuggestion___lam__0), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_instCoeSuggestionTextSuggestion___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_box(0);
x_3 = lean_box(0);
x_4 = lean_box(0);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_2);
lean_ctor_set(x_6, 3, x_3);
lean_ctor_set(x_6, 4, x_4);
lean_ctor_set(x_6, 5, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_instCoeSuggestionTextSuggestion() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_TryThis_instCoeSuggestionTextSuggestion___lam__0), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_1);
x_7 = l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_mk_string_unchecked("term", 4, 4);
x_11 = l_Lean_Name_mkStr1(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
x_13 = lean_box(0);
x_14 = lean_box(0);
x_15 = l_Lean_MessageData_ofExpr(x_1);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_13);
lean_ctor_set(x_18, 2, x_13);
lean_ctor_set(x_18, 3, x_14);
lean_ctor_set(x_18, 4, x_16);
lean_ctor_set(x_18, 5, x_17);
lean_ctor_set(x_7, 0, x_18);
return x_7;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_19 = lean_ctor_get(x_7, 0);
x_20 = lean_ctor_get(x_7, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_7);
x_21 = lean_mk_string_unchecked("term", 4, 4);
x_22 = l_Lean_Name_mkStr1(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_19);
x_24 = lean_box(0);
x_25 = lean_box(0);
x_26 = l_Lean_MessageData_ofExpr(x_1);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_29, 1, x_24);
lean_ctor_set(x_29, 2, x_24);
lean_ctor_set(x_29, 3, x_25);
lean_ctor_set(x_29, 4, x_27);
lean_ctor_set(x_29, 5, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_20);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_1);
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addSuggestionCore_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_4, x_3);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_array_uget(x_5, x_4);
x_12 = lean_box(0);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_2);
lean_inc(x_1);
x_13 = l_Lean_Meta_Tactic_TryThis_Suggestion_toJsonAndInfoM(x_11, x_12, x_1, x_2, x_6, x_7, x_8);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_box(0);
x_17 = lean_array_uset(x_5, x_4, x_16);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_usize_of_nat(x_18);
x_20 = lean_usize_add(x_4, x_19);
x_21 = lean_array_uset(x_17, x_4, x_14);
x_4 = x_20;
x_5 = x_21;
x_8 = x_15;
goto _start;
}
else
{
uint8_t x_23; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_13);
if (x_23 == 0)
{
return x_13;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_13, 0);
x_25 = lean_ctor_get(x_13, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_13);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addSuggestionCore_spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_box(0);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_usize_of_nat(x_9);
x_11 = lean_usize_add(x_2, x_10);
x_12 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_11;
x_3 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addSuggestionCore_spec__2(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_box(0);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec(x_5);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_usize_of_nat(x_9);
x_11 = lean_usize_add(x_2, x_10);
x_12 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_11;
x_3 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addSuggestionCore___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addSuggestionCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint64_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_31; size_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_92; 
x_31 = l_Lean_Meta_Tactic_TryThis_instImpl____x40_Lean_Meta_Tactic_TryThis___hyg_52_;
if (lean_obj_tag(x_5) == 0)
{
x_92 = x_1;
goto block_119;
}
else
{
lean_object* x_120; 
x_120 = lean_ctor_get(x_5, 0);
x_92 = x_120;
goto block_119;
}
block_30:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_11);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_12);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_17);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_16);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_14);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_Json_mkObj(x_26);
x_28 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addSuggestionCore___lam__0), 2, 1);
lean_closure_set(x_28, 0, x_27);
x_29 = l_Lean_Widget_savePanelWidgetInfo(x_15, x_28, x_18, x_8, x_9, x_13);
lean_dec(x_9);
lean_dec(x_8);
return x_29;
}
block_91:
{
lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_39 = lean_box(1);
x_40 = lean_unbox(x_39);
x_41 = l_Lean_Syntax_ofRange(x_38, x_40);
lean_dec(x_38);
x_42 = l_Lean_FileMap_utf8RangeToLspRange(x_33, x_34);
lean_dec(x_34);
lean_inc(x_42);
x_43 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_36);
lean_ctor_set(x_43, 2, x_7);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_31);
lean_ctor_set(x_44, 1, x_43);
lean_inc(x_41);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_41);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(x_46, 0, x_45);
x_47 = l_Lean_Elab_pushInfoLeaf___at___Lean_Elab_addConstInfo___at___Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__3(x_46, x_8, x_9, x_37);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint64_t x_53; lean_object* x_54; size_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_49 = lean_ctor_get(x_47, 1);
x_50 = lean_ctor_get(x_47, 0);
lean_dec(x_50);
x_51 = l_Lean_Meta_Tactic_TryThis_tryThisWidget;
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_string_hash(x_52);
lean_dec(x_52);
x_54 = lean_mk_string_unchecked("suggestions", 11, 11);
x_55 = lean_array_size(x_35);
x_56 = l_Array_mapMUnsafe_map___at___Lean_Json_opt___at_____private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1558__spec__0_spec__0(x_55, x_32, x_35);
x_57 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_47, 1, x_57);
lean_ctor_set(x_47, 0, x_54);
x_58 = lean_mk_string_unchecked("range", 5, 5);
x_59 = l___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonRange____x40_Lean_Data_Lsp_Basic___hyg_615_(x_42);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_mk_string_unchecked("header", 6, 6);
x_62 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_62, 0, x_3);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
x_64 = lean_mk_string_unchecked("isInline", 8, 8);
x_65 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_65, 0, x_4);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
x_67 = lean_mk_string_unchecked("style", 5, 5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_68; 
x_68 = lean_box(0);
x_11 = x_67;
x_12 = x_66;
x_13 = x_49;
x_14 = x_47;
x_15 = x_53;
x_16 = x_60;
x_17 = x_63;
x_18 = x_41;
x_19 = x_68;
goto block_30;
}
else
{
lean_object* x_69; 
x_69 = lean_ctor_get(x_6, 0);
lean_inc(x_69);
lean_dec(x_6);
x_11 = x_67;
x_12 = x_66;
x_13 = x_49;
x_14 = x_47;
x_15 = x_53;
x_16 = x_60;
x_17 = x_63;
x_18 = x_41;
x_19 = x_69;
goto block_30;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; uint64_t x_73; lean_object* x_74; size_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_70 = lean_ctor_get(x_47, 1);
lean_inc(x_70);
lean_dec(x_47);
x_71 = l_Lean_Meta_Tactic_TryThis_tryThisWidget;
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_string_hash(x_72);
lean_dec(x_72);
x_74 = lean_mk_string_unchecked("suggestions", 11, 11);
x_75 = lean_array_size(x_35);
x_76 = l_Array_mapMUnsafe_map___at___Lean_Json_opt___at_____private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1558__spec__0_spec__0(x_75, x_32, x_35);
x_77 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_77, 0, x_76);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_74);
lean_ctor_set(x_78, 1, x_77);
x_79 = lean_mk_string_unchecked("range", 5, 5);
x_80 = l___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonRange____x40_Lean_Data_Lsp_Basic___hyg_615_(x_42);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
x_82 = lean_mk_string_unchecked("header", 6, 6);
x_83 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_83, 0, x_3);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
x_85 = lean_mk_string_unchecked("isInline", 8, 8);
x_86 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_86, 0, x_4);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
x_88 = lean_mk_string_unchecked("style", 5, 5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_89; 
x_89 = lean_box(0);
x_11 = x_88;
x_12 = x_87;
x_13 = x_70;
x_14 = x_78;
x_15 = x_73;
x_16 = x_81;
x_17 = x_84;
x_18 = x_41;
x_19 = x_89;
goto block_30;
}
else
{
lean_object* x_90; 
x_90 = lean_ctor_get(x_6, 0);
lean_inc(x_90);
lean_dec(x_6);
x_11 = x_88;
x_12 = x_87;
x_13 = x_70;
x_14 = x_78;
x_15 = x_73;
x_16 = x_81;
x_17 = x_84;
x_18 = x_41;
x_19 = x_90;
goto block_30;
}
}
}
block_119:
{
lean_object* x_93; uint8_t x_94; lean_object* x_95; 
x_93 = lean_box(0);
x_94 = lean_unbox(x_93);
x_95 = l_Lean_Syntax_getRange_x3f(x_92, x_94);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_96 = lean_box(0);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_10);
return x_97;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; size_t x_103; lean_object* x_104; size_t x_105; lean_object* x_106; 
x_98 = lean_ctor_get(x_95, 0);
lean_inc(x_98);
lean_dec(x_95);
x_99 = lean_ctor_get(x_8, 1);
lean_inc(x_99);
lean_inc(x_98);
x_100 = l_Lean_Meta_Tactic_TryThis_getIndentAndColumn(x_99, x_98);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
x_103 = lean_array_size(x_2);
x_104 = lean_unsigned_to_nat(0u);
x_105 = lean_usize_of_nat(x_104);
lean_inc(x_9);
lean_inc(x_8);
x_106 = l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addSuggestionCore_spec__0(x_101, x_102, x_103, x_105, x_2, x_8, x_9, x_10);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; size_t x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; lean_object* x_113; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec(x_106);
x_109 = lean_array_size(x_107);
lean_inc(x_107);
x_110 = l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addSuggestionCore_spec__1(x_109, x_105, x_107);
x_111 = l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addSuggestionCore_spec__2(x_109, x_105, x_107);
x_112 = lean_unbox(x_93);
x_113 = l_Lean_Syntax_getRange_x3f(x_1, x_112);
if (lean_obj_tag(x_113) == 0)
{
lean_inc(x_98);
x_32 = x_105;
x_33 = x_99;
x_34 = x_98;
x_35 = x_111;
x_36 = x_110;
x_37 = x_108;
x_38 = x_98;
goto block_91;
}
else
{
lean_object* x_114; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
lean_dec(x_113);
x_32 = x_105;
x_33 = x_99;
x_34 = x_98;
x_35 = x_111;
x_36 = x_110;
x_37 = x_108;
x_38 = x_114;
goto block_91;
}
}
else
{
uint8_t x_115; 
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_115 = !lean_is_exclusive(x_106);
if (x_115 == 0)
{
return x_106;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_106, 0);
x_117 = lean_ctor_get(x_106, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_106);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
return x_118;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addSuggestionCore_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addSuggestionCore_spec__0(x_1, x_2, x_9, x_10, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addSuggestionCore_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addSuggestionCore_spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addSuggestionCore_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addSuggestionCore_spec__2(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addSuggestionCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addSuggestionCore(x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___Lean_Meta_Tactic_TryThis_addSuggestion_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestion(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_29; 
x_11 = lean_mk_string_unchecked("", 0, 0);
x_12 = l_Lean_stringToMessageData(x_11);
lean_dec(x_11);
x_13 = l_Lean_stringToMessageData(x_4);
lean_inc(x_12);
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
lean_inc(x_12);
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_12);
x_29 = lean_ctor_get(x_2, 4);
lean_inc(x_29);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_2, 0);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = l_Lean_MessageData_ofSyntax(x_31);
x_16 = x_32;
goto block_28;
}
else
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_30);
if (x_33 == 0)
{
lean_object* x_34; 
lean_ctor_set_tag(x_30, 3);
x_34 = l_Lean_MessageData_ofFormat(x_30);
x_16 = x_34;
goto block_28;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_30, 0);
lean_inc(x_35);
lean_dec(x_30);
x_36 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_37 = l_Lean_MessageData_ofFormat(x_36);
x_16 = x_37;
goto block_28;
}
}
}
else
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_29, 0);
lean_inc(x_38);
lean_dec(x_29);
x_16 = x_38;
goto block_28;
}
block_28:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_12);
lean_inc(x_8);
x_19 = l_Lean_logInfoAt___at___Lean_Meta_Tactic_TryThis_addSuggestion_spec__0(x_1, x_18, x_6, x_7, x_8, x_9, x_10);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_mk_empty_array_with_capacity(x_21);
x_23 = lean_array_push(x_22, x_2);
x_24 = lean_box(1);
x_25 = lean_box(0);
x_26 = lean_unbox(x_24);
x_27 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addSuggestionCore(x_1, x_23, x_4, x_26, x_3, x_25, x_5, x_8, x_9, x_20);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___Lean_Meta_Tactic_TryThis_addSuggestion_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_logInfoAt___at___Lean_Meta_Tactic_TryThis_addSuggestion_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestion___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Tactic_TryThis_addSuggestion(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_Tactic_TryThis_addSuggestions_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_15; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_box(0);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_15 = lean_ctor_get(x_5, 4);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_5, 0);
lean_inc(x_16);
lean_dec(x_5);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Lean_MessageData_ofSyntax(x_17);
x_8 = x_18;
goto block_14;
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_16);
if (x_19 == 0)
{
lean_object* x_20; 
lean_ctor_set_tag(x_16, 3);
x_20 = l_Lean_MessageData_ofFormat(x_16);
x_8 = x_20;
goto block_14;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_16, 0);
lean_inc(x_21);
lean_dec(x_16);
x_22 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = l_Lean_MessageData_ofFormat(x_22);
x_8 = x_23;
goto block_14;
}
}
}
else
{
lean_object* x_24; 
lean_dec(x_5);
x_24 = lean_ctor_get(x_15, 0);
lean_inc(x_24);
lean_dec(x_15);
x_8 = x_24;
goto block_14;
}
block_14:
{
lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_usize_of_nat(x_9);
x_11 = lean_usize_add(x_2, x_10);
x_12 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_11;
x_3 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Meta_Tactic_TryThis_addSuggestions_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_mk_string_unchecked("\n• ", 5, 3);
x_8 = l_Lean_stringToMessageData(x_7);
lean_dec(x_7);
x_9 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(2u);
x_11 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_6);
x_12 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_usize_of_nat(x_13);
x_15 = lean_usize_add(x_2, x_14);
x_2 = x_15;
x_4 = x_12;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestions(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_31; 
x_31 = l_Array_isEmpty___redArg(x_2);
if (x_31 == 0)
{
size_t x_32; lean_object* x_33; size_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_32 = lean_array_size(x_2);
x_33 = lean_unsigned_to_nat(0u);
x_34 = lean_usize_of_nat(x_33);
lean_inc(x_2);
x_35 = l_Array_mapMUnsafe_map___at___Lean_Meta_Tactic_TryThis_addSuggestions_spec__0(x_32, x_34, x_2);
x_36 = l_Lean_MessageData_nil;
x_37 = lean_array_get_size(x_35);
x_38 = lean_nat_dec_lt(x_33, x_37);
if (x_38 == 0)
{
lean_dec(x_37);
lean_dec(x_35);
x_12 = x_9;
x_13 = x_10;
x_14 = x_11;
x_15 = x_7;
x_16 = x_8;
x_17 = x_36;
goto block_30;
}
else
{
uint8_t x_39; 
x_39 = lean_nat_dec_le(x_37, x_37);
if (x_39 == 0)
{
lean_dec(x_37);
lean_dec(x_35);
x_12 = x_9;
x_13 = x_10;
x_14 = x_11;
x_15 = x_7;
x_16 = x_8;
x_17 = x_36;
goto block_30;
}
else
{
size_t x_40; lean_object* x_41; 
x_40 = lean_usize_of_nat(x_37);
lean_dec(x_37);
x_41 = l_Array_foldlMUnsafe_fold___at___Lean_Meta_Tactic_TryThis_addSuggestions_spec__1(x_35, x_34, x_40, x_36);
lean_dec(x_35);
x_12 = x_9;
x_13 = x_10;
x_14 = x_11;
x_15 = x_7;
x_16 = x_8;
x_17 = x_41;
goto block_30;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_42 = lean_mk_string_unchecked("no suggestions available", 24, 24);
x_43 = l_Lean_stringToMessageData(x_42);
lean_dec(x_42);
x_44 = l_Lean_throwErrorAt___at___Lean_Meta_mkProjections_spec__5___redArg(x_1, x_43, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_44;
}
block_30:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_18 = lean_mk_string_unchecked("", 0, 0);
x_19 = l_Lean_stringToMessageData(x_18);
lean_dec(x_18);
x_20 = l_Lean_stringToMessageData(x_4);
lean_inc(x_19);
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
lean_inc(x_19);
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_17);
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_19);
lean_inc(x_12);
x_25 = l_Lean_logInfoAt___at___Lean_Meta_Tactic_TryThis_addSuggestion_spec__0(x_1, x_24, x_15, x_16, x_12, x_13, x_14);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_box(0);
x_28 = lean_unbox(x_27);
x_29 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addSuggestionCore(x_1, x_2, x_4, x_28, x_3, x_5, x_6, x_12, x_13, x_26);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_Tactic_TryThis_addSuggestions_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lean_Meta_Tactic_TryThis_addSuggestions_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Meta_Tactic_TryThis_addSuggestions_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Lean_Meta_Tactic_TryThis_addSuggestions_spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestions___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Tactic_TryThis_addSuggestions(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_26; lean_object* x_27; lean_object* x_35; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_13 = l_Lean_Elab_Tactic_saveState___redArg(x_5, x_7, x_9, x_10, x_11, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_box(0);
x_41 = lean_unbox(x_16);
x_42 = l_Lean_Elab_Tactic_SavedState_restore(x_1, x_41, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_15);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_44 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic), 10, 1);
lean_closure_set(x_44, 0, x_2);
x_45 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withoutRecover___boxed), 11, 2);
lean_closure_set(x_45, 0, lean_box(0));
lean_closure_set(x_45, 1, x_44);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_4);
x_46 = l_Lean_Elab_Term_withoutErrToSorry___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_maybeWithoutRecovery_spec__0(lean_box(0), x_45, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_43);
if (lean_obj_tag(x_46) == 0)
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
x_48 = lean_box(0);
x_26 = x_48;
x_27 = x_47;
goto block_34;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
lean_dec(x_46);
x_50 = lean_ctor_get(x_3, 0);
lean_inc(x_50);
lean_dec(x_3);
x_51 = l_Lean_Elab_Tactic_getMainGoal(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_49);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = l_Lean_MVarId_getType(x_52, x_8, x_9, x_10, x_11, x_53);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = l_Lean_instantiateMVars___at___Lean_Elab_Tactic_getMainTarget_spec__0___redArg(x_55, x_9, x_56);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = l_Lean_instantiateMVars___at___Lean_Elab_Tactic_getMainTarget_spec__0___redArg(x_50, x_9, x_59);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = lean_expr_eqv(x_58, x_61);
lean_dec(x_61);
lean_dec(x_58);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_mk_string_unchecked("tactic did not produce expected goal", 36, 36);
x_65 = l_Lean_stringToMessageData(x_64);
lean_dec(x_64);
x_66 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(x_65, x_8, x_9, x_10, x_11, x_62);
x_35 = x_66;
goto block_40;
}
else
{
lean_object* x_67; 
x_67 = lean_box(0);
x_26 = x_67;
x_27 = x_62;
goto block_34;
}
}
else
{
lean_object* x_68; lean_object* x_69; 
lean_dec(x_50);
x_68 = lean_ctor_get(x_54, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_54, 1);
lean_inc(x_69);
lean_dec(x_54);
x_17 = x_68;
x_18 = x_69;
goto block_25;
}
}
else
{
lean_object* x_70; lean_object* x_71; 
lean_dec(x_50);
x_70 = lean_ctor_get(x_51, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_51, 1);
lean_inc(x_71);
lean_dec(x_51);
x_17 = x_70;
x_18 = x_71;
goto block_25;
}
}
}
else
{
lean_dec(x_3);
x_35 = x_46;
goto block_40;
}
block_25:
{
uint8_t x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_unbox(x_16);
x_20 = l_Lean_Elab_Tactic_SavedState_restore(x_14, x_19, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_18);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
lean_ctor_set_tag(x_20, 1);
lean_ctor_set(x_20, 0, x_17);
return x_20;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_17);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
block_34:
{
uint8_t x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_unbox(x_16);
x_29 = l_Lean_Elab_Tactic_SavedState_restore(x_14, x_28, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_27);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_29, 0);
lean_dec(x_31);
lean_ctor_set(x_29, 0, x_26);
return x_29;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_26);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
block_40:
{
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_26 = x_36;
x_27 = x_37;
goto block_34;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_35, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_35, 1);
lean_inc(x_39);
lean_dec(x_35);
x_17 = x_38;
x_18 = x_39;
goto block_25;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_6);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = l_Lean_Elab_Tactic_saveState___redArg(x_6, x_8, x_10, x_11, x_12, x_13);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_29 = x_26;
} else {
 lean_dec_ref(x_26);
 x_29 = lean_box(0);
}
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
lean_inc(x_3);
x_30 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState(x_3, x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_28);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
lean_dec(x_27);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_30, 0);
lean_dec(x_32);
if (lean_is_scalar(x_29)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_29;
}
lean_ctor_set(x_33, 0, x_1);
lean_ctor_set(x_33, 1, x_2);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_30, 0, x_34);
return x_30;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_30, 1);
lean_inc(x_35);
lean_dec(x_30);
if (lean_is_scalar(x_29)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_29;
}
lean_ctor_set(x_36, 0, x_1);
lean_ctor_set(x_36, 1, x_2);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_35);
return x_38;
}
}
else
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_30);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; uint8_t x_241; 
x_40 = lean_ctor_get(x_30, 0);
x_41 = lean_ctor_get(x_30, 1);
lean_inc(x_41);
lean_inc(x_40);
x_241 = l_Lean_Exception_isInterrupt(x_40);
if (x_241 == 0)
{
uint8_t x_242; 
x_242 = l_Lean_Exception_isRuntime(x_40);
lean_dec(x_40);
x_42 = x_242;
goto block_240;
}
else
{
lean_dec(x_40);
x_42 = x_241;
goto block_240;
}
block_240:
{
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
lean_dec(x_30);
x_43 = l_Lean_Elab_Tactic_SavedState_restore(x_27, x_42, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_41);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_45 = lean_ctor_get(x_43, 1);
x_46 = lean_ctor_get(x_43, 0);
lean_dec(x_46);
x_47 = lean_st_ref_get(x_12, x_45);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_49 = lean_ctor_get(x_47, 1);
x_50 = lean_ctor_get(x_47, 0);
lean_dec(x_50);
x_51 = lean_ctor_get(x_11, 5);
lean_inc(x_51);
x_52 = l_Lean_SourceInfo_fromRef(x_51, x_42);
lean_dec(x_51);
x_53 = lean_mk_string_unchecked("Lean", 4, 4);
x_54 = lean_mk_string_unchecked("Parser", 6, 6);
x_55 = lean_mk_string_unchecked("Tactic", 6, 6);
x_56 = lean_mk_string_unchecked("tacticSeq", 9, 9);
x_57 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
x_58 = l_Lean_Name_mkStr4(x_53, x_54, x_55, x_57);
x_59 = lean_mk_string_unchecked("null", 4, 4);
x_60 = l_Lean_Name_mkStr1(x_59);
x_61 = lean_mk_string_unchecked("exposeNames", 11, 11);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
x_62 = l_Lean_Name_mkStr4(x_53, x_54, x_55, x_61);
x_63 = lean_mk_string_unchecked("expose_names", 12, 12);
lean_inc(x_52);
lean_ctor_set_tag(x_47, 2);
lean_ctor_set(x_47, 1, x_63);
lean_ctor_set(x_47, 0, x_52);
lean_inc(x_52);
x_64 = l_Lean_Syntax_node1(x_52, x_62, x_47);
x_65 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_52);
lean_ctor_set_tag(x_43, 2);
lean_ctor_set(x_43, 1, x_65);
lean_ctor_set(x_43, 0, x_52);
lean_inc(x_52);
x_66 = l_Lean_Syntax_node3(x_52, x_60, x_64, x_43, x_1);
x_67 = l_Lean_Elab_Tactic_saveState___redArg(x_6, x_8, x_10, x_11, x_12, x_49);
x_68 = !lean_is_exclusive(x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_69 = lean_ctor_get(x_67, 0);
x_70 = lean_ctor_get(x_67, 1);
x_71 = lean_mk_string_unchecked("paren", 5, 5);
x_72 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
x_73 = l_Lean_Name_mkStr4(x_53, x_54, x_55, x_56);
lean_inc(x_52);
x_74 = l_Lean_Syntax_node1(x_52, x_58, x_66);
x_75 = l_Lean_Name_mkStr4(x_53, x_54, x_55, x_71);
lean_inc(x_52);
lean_ctor_set_tag(x_67, 2);
lean_ctor_set(x_67, 1, x_72);
lean_ctor_set(x_67, 0, x_52);
lean_inc(x_52);
x_76 = l_Lean_Syntax_node1(x_52, x_73, x_74);
x_77 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_77);
lean_inc(x_52);
if (lean_is_scalar(x_29)) {
 x_78 = lean_alloc_ctor(2, 2, 0);
} else {
 x_78 = x_29;
 lean_ctor_set_tag(x_78, 2);
}
lean_ctor_set(x_78, 0, x_52);
lean_ctor_set(x_78, 1, x_77);
x_79 = l_Lean_Syntax_node3(x_52, x_75, x_67, x_76, x_78);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_79);
x_80 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState(x_3, x_79, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_70);
if (lean_obj_tag(x_80) == 0)
{
uint8_t x_81; 
lean_dec(x_69);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_81 = !lean_is_exclusive(x_80);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_82 = lean_ctor_get(x_80, 0);
lean_dec(x_82);
x_83 = lean_mk_string_unchecked("(expose_names; ", 15, 15);
x_84 = l_Lean_stringToMessageData(x_83);
lean_dec(x_83);
x_85 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_2);
x_86 = l_Lean_stringToMessageData(x_77);
lean_dec(x_77);
x_87 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_79);
lean_ctor_set(x_88, 1, x_87);
x_89 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_80, 0, x_89);
return x_80;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_90 = lean_ctor_get(x_80, 1);
lean_inc(x_90);
lean_dec(x_80);
x_91 = lean_mk_string_unchecked("(expose_names; ", 15, 15);
x_92 = l_Lean_stringToMessageData(x_91);
lean_dec(x_91);
x_93 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_2);
x_94 = l_Lean_stringToMessageData(x_77);
lean_dec(x_77);
x_95 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_79);
lean_ctor_set(x_96, 1, x_95);
x_97 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_97, 0, x_96);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_90);
return x_98;
}
}
else
{
uint8_t x_99; 
lean_dec(x_79);
lean_dec(x_77);
lean_dec(x_2);
x_99 = !lean_is_exclusive(x_80);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; uint8_t x_102; 
x_100 = lean_ctor_get(x_80, 0);
x_101 = lean_ctor_get(x_80, 1);
lean_inc(x_101);
lean_inc(x_100);
x_102 = l_Lean_Exception_isInterrupt(x_100);
if (x_102 == 0)
{
uint8_t x_103; 
x_103 = l_Lean_Exception_isRuntime(x_100);
lean_dec(x_100);
x_14 = x_101;
x_15 = x_80;
x_16 = x_69;
x_17 = x_103;
goto block_25;
}
else
{
lean_dec(x_100);
x_14 = x_101;
x_15 = x_80;
x_16 = x_69;
x_17 = x_102;
goto block_25;
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; 
x_104 = lean_ctor_get(x_80, 0);
x_105 = lean_ctor_get(x_80, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_80);
lean_inc(x_105);
lean_inc(x_104);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
x_107 = l_Lean_Exception_isInterrupt(x_104);
if (x_107 == 0)
{
uint8_t x_108; 
x_108 = l_Lean_Exception_isRuntime(x_104);
lean_dec(x_104);
x_14 = x_105;
x_15 = x_106;
x_16 = x_69;
x_17 = x_108;
goto block_25;
}
else
{
lean_dec(x_104);
x_14 = x_105;
x_15 = x_106;
x_16 = x_69;
x_17 = x_107;
goto block_25;
}
}
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_109 = lean_ctor_get(x_67, 0);
x_110 = lean_ctor_get(x_67, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_67);
x_111 = lean_mk_string_unchecked("paren", 5, 5);
x_112 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
x_113 = l_Lean_Name_mkStr4(x_53, x_54, x_55, x_56);
lean_inc(x_52);
x_114 = l_Lean_Syntax_node1(x_52, x_58, x_66);
x_115 = l_Lean_Name_mkStr4(x_53, x_54, x_55, x_111);
lean_inc(x_52);
x_116 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_116, 0, x_52);
lean_ctor_set(x_116, 1, x_112);
lean_inc(x_52);
x_117 = l_Lean_Syntax_node1(x_52, x_113, x_114);
x_118 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_118);
lean_inc(x_52);
if (lean_is_scalar(x_29)) {
 x_119 = lean_alloc_ctor(2, 2, 0);
} else {
 x_119 = x_29;
 lean_ctor_set_tag(x_119, 2);
}
lean_ctor_set(x_119, 0, x_52);
lean_ctor_set(x_119, 1, x_118);
x_120 = l_Lean_Syntax_node3(x_52, x_115, x_116, x_117, x_119);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_120);
x_121 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState(x_3, x_120, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_110);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_109);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_122 = lean_ctor_get(x_121, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 lean_ctor_release(x_121, 1);
 x_123 = x_121;
} else {
 lean_dec_ref(x_121);
 x_123 = lean_box(0);
}
x_124 = lean_mk_string_unchecked("(expose_names; ", 15, 15);
x_125 = l_Lean_stringToMessageData(x_124);
lean_dec(x_124);
x_126 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_2);
x_127 = l_Lean_stringToMessageData(x_118);
lean_dec(x_118);
x_128 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_120);
lean_ctor_set(x_129, 1, x_128);
x_130 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_130, 0, x_129);
if (lean_is_scalar(x_123)) {
 x_131 = lean_alloc_ctor(0, 2, 0);
} else {
 x_131 = x_123;
}
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_122);
return x_131;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; 
lean_dec(x_120);
lean_dec(x_118);
lean_dec(x_2);
x_132 = lean_ctor_get(x_121, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_121, 1);
lean_inc(x_133);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 lean_ctor_release(x_121, 1);
 x_134 = x_121;
} else {
 lean_dec_ref(x_121);
 x_134 = lean_box(0);
}
lean_inc(x_133);
lean_inc(x_132);
if (lean_is_scalar(x_134)) {
 x_135 = lean_alloc_ctor(1, 2, 0);
} else {
 x_135 = x_134;
}
lean_ctor_set(x_135, 0, x_132);
lean_ctor_set(x_135, 1, x_133);
x_136 = l_Lean_Exception_isInterrupt(x_132);
if (x_136 == 0)
{
uint8_t x_137; 
x_137 = l_Lean_Exception_isRuntime(x_132);
lean_dec(x_132);
x_14 = x_133;
x_15 = x_135;
x_16 = x_109;
x_17 = x_137;
goto block_25;
}
else
{
lean_dec(x_132);
x_14 = x_133;
x_15 = x_135;
x_16 = x_109;
x_17 = x_136;
goto block_25;
}
}
}
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_138 = lean_ctor_get(x_47, 1);
lean_inc(x_138);
lean_dec(x_47);
x_139 = lean_ctor_get(x_11, 5);
lean_inc(x_139);
x_140 = l_Lean_SourceInfo_fromRef(x_139, x_42);
lean_dec(x_139);
x_141 = lean_mk_string_unchecked("Lean", 4, 4);
x_142 = lean_mk_string_unchecked("Parser", 6, 6);
x_143 = lean_mk_string_unchecked("Tactic", 6, 6);
x_144 = lean_mk_string_unchecked("tacticSeq", 9, 9);
x_145 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
lean_inc(x_143);
lean_inc(x_142);
lean_inc(x_141);
x_146 = l_Lean_Name_mkStr4(x_141, x_142, x_143, x_145);
x_147 = lean_mk_string_unchecked("null", 4, 4);
x_148 = l_Lean_Name_mkStr1(x_147);
x_149 = lean_mk_string_unchecked("exposeNames", 11, 11);
lean_inc(x_143);
lean_inc(x_142);
lean_inc(x_141);
x_150 = l_Lean_Name_mkStr4(x_141, x_142, x_143, x_149);
x_151 = lean_mk_string_unchecked("expose_names", 12, 12);
lean_inc(x_140);
x_152 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_152, 0, x_140);
lean_ctor_set(x_152, 1, x_151);
lean_inc(x_140);
x_153 = l_Lean_Syntax_node1(x_140, x_150, x_152);
x_154 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_140);
lean_ctor_set_tag(x_43, 2);
lean_ctor_set(x_43, 1, x_154);
lean_ctor_set(x_43, 0, x_140);
lean_inc(x_140);
x_155 = l_Lean_Syntax_node3(x_140, x_148, x_153, x_43, x_1);
x_156 = l_Lean_Elab_Tactic_saveState___redArg(x_6, x_8, x_10, x_11, x_12, x_138);
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 lean_ctor_release(x_156, 1);
 x_159 = x_156;
} else {
 lean_dec_ref(x_156);
 x_159 = lean_box(0);
}
x_160 = lean_mk_string_unchecked("paren", 5, 5);
x_161 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_143);
lean_inc(x_142);
lean_inc(x_141);
x_162 = l_Lean_Name_mkStr4(x_141, x_142, x_143, x_144);
lean_inc(x_140);
x_163 = l_Lean_Syntax_node1(x_140, x_146, x_155);
x_164 = l_Lean_Name_mkStr4(x_141, x_142, x_143, x_160);
lean_inc(x_140);
if (lean_is_scalar(x_159)) {
 x_165 = lean_alloc_ctor(2, 2, 0);
} else {
 x_165 = x_159;
 lean_ctor_set_tag(x_165, 2);
}
lean_ctor_set(x_165, 0, x_140);
lean_ctor_set(x_165, 1, x_161);
lean_inc(x_140);
x_166 = l_Lean_Syntax_node1(x_140, x_162, x_163);
x_167 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_167);
lean_inc(x_140);
if (lean_is_scalar(x_29)) {
 x_168 = lean_alloc_ctor(2, 2, 0);
} else {
 x_168 = x_29;
 lean_ctor_set_tag(x_168, 2);
}
lean_ctor_set(x_168, 0, x_140);
lean_ctor_set(x_168, 1, x_167);
x_169 = l_Lean_Syntax_node3(x_140, x_164, x_165, x_166, x_168);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_169);
x_170 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState(x_3, x_169, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_158);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_157);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_171 = lean_ctor_get(x_170, 1);
lean_inc(x_171);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 x_172 = x_170;
} else {
 lean_dec_ref(x_170);
 x_172 = lean_box(0);
}
x_173 = lean_mk_string_unchecked("(expose_names; ", 15, 15);
x_174 = l_Lean_stringToMessageData(x_173);
lean_dec(x_173);
x_175 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_2);
x_176 = l_Lean_stringToMessageData(x_167);
lean_dec(x_167);
x_177 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_177, 0, x_175);
lean_ctor_set(x_177, 1, x_176);
x_178 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_178, 0, x_169);
lean_ctor_set(x_178, 1, x_177);
x_179 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_179, 0, x_178);
if (lean_is_scalar(x_172)) {
 x_180 = lean_alloc_ctor(0, 2, 0);
} else {
 x_180 = x_172;
}
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_171);
return x_180;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; uint8_t x_185; 
lean_dec(x_169);
lean_dec(x_167);
lean_dec(x_2);
x_181 = lean_ctor_get(x_170, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_170, 1);
lean_inc(x_182);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 x_183 = x_170;
} else {
 lean_dec_ref(x_170);
 x_183 = lean_box(0);
}
lean_inc(x_182);
lean_inc(x_181);
if (lean_is_scalar(x_183)) {
 x_184 = lean_alloc_ctor(1, 2, 0);
} else {
 x_184 = x_183;
}
lean_ctor_set(x_184, 0, x_181);
lean_ctor_set(x_184, 1, x_182);
x_185 = l_Lean_Exception_isInterrupt(x_181);
if (x_185 == 0)
{
uint8_t x_186; 
x_186 = l_Lean_Exception_isRuntime(x_181);
lean_dec(x_181);
x_14 = x_182;
x_15 = x_184;
x_16 = x_157;
x_17 = x_186;
goto block_25;
}
else
{
lean_dec(x_181);
x_14 = x_182;
x_15 = x_184;
x_16 = x_157;
x_17 = x_185;
goto block_25;
}
}
}
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_187 = lean_ctor_get(x_43, 1);
lean_inc(x_187);
lean_dec(x_43);
x_188 = lean_st_ref_get(x_12, x_187);
x_189 = lean_ctor_get(x_188, 1);
lean_inc(x_189);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 x_190 = x_188;
} else {
 lean_dec_ref(x_188);
 x_190 = lean_box(0);
}
x_191 = lean_ctor_get(x_11, 5);
lean_inc(x_191);
x_192 = l_Lean_SourceInfo_fromRef(x_191, x_42);
lean_dec(x_191);
x_193 = lean_mk_string_unchecked("Lean", 4, 4);
x_194 = lean_mk_string_unchecked("Parser", 6, 6);
x_195 = lean_mk_string_unchecked("Tactic", 6, 6);
x_196 = lean_mk_string_unchecked("tacticSeq", 9, 9);
x_197 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
lean_inc(x_195);
lean_inc(x_194);
lean_inc(x_193);
x_198 = l_Lean_Name_mkStr4(x_193, x_194, x_195, x_197);
x_199 = lean_mk_string_unchecked("null", 4, 4);
x_200 = l_Lean_Name_mkStr1(x_199);
x_201 = lean_mk_string_unchecked("exposeNames", 11, 11);
lean_inc(x_195);
lean_inc(x_194);
lean_inc(x_193);
x_202 = l_Lean_Name_mkStr4(x_193, x_194, x_195, x_201);
x_203 = lean_mk_string_unchecked("expose_names", 12, 12);
lean_inc(x_192);
if (lean_is_scalar(x_190)) {
 x_204 = lean_alloc_ctor(2, 2, 0);
} else {
 x_204 = x_190;
 lean_ctor_set_tag(x_204, 2);
}
lean_ctor_set(x_204, 0, x_192);
lean_ctor_set(x_204, 1, x_203);
lean_inc(x_192);
x_205 = l_Lean_Syntax_node1(x_192, x_202, x_204);
x_206 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_192);
x_207 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_207, 0, x_192);
lean_ctor_set(x_207, 1, x_206);
lean_inc(x_192);
x_208 = l_Lean_Syntax_node3(x_192, x_200, x_205, x_207, x_1);
x_209 = l_Lean_Elab_Tactic_saveState___redArg(x_6, x_8, x_10, x_11, x_12, x_189);
x_210 = lean_ctor_get(x_209, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_209, 1);
lean_inc(x_211);
if (lean_is_exclusive(x_209)) {
 lean_ctor_release(x_209, 0);
 lean_ctor_release(x_209, 1);
 x_212 = x_209;
} else {
 lean_dec_ref(x_209);
 x_212 = lean_box(0);
}
x_213 = lean_mk_string_unchecked("paren", 5, 5);
x_214 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_195);
lean_inc(x_194);
lean_inc(x_193);
x_215 = l_Lean_Name_mkStr4(x_193, x_194, x_195, x_196);
lean_inc(x_192);
x_216 = l_Lean_Syntax_node1(x_192, x_198, x_208);
x_217 = l_Lean_Name_mkStr4(x_193, x_194, x_195, x_213);
lean_inc(x_192);
if (lean_is_scalar(x_212)) {
 x_218 = lean_alloc_ctor(2, 2, 0);
} else {
 x_218 = x_212;
 lean_ctor_set_tag(x_218, 2);
}
lean_ctor_set(x_218, 0, x_192);
lean_ctor_set(x_218, 1, x_214);
lean_inc(x_192);
x_219 = l_Lean_Syntax_node1(x_192, x_215, x_216);
x_220 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_220);
lean_inc(x_192);
if (lean_is_scalar(x_29)) {
 x_221 = lean_alloc_ctor(2, 2, 0);
} else {
 x_221 = x_29;
 lean_ctor_set_tag(x_221, 2);
}
lean_ctor_set(x_221, 0, x_192);
lean_ctor_set(x_221, 1, x_220);
x_222 = l_Lean_Syntax_node3(x_192, x_217, x_218, x_219, x_221);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_222);
x_223 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState(x_3, x_222, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_211);
if (lean_obj_tag(x_223) == 0)
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
lean_dec(x_210);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_224 = lean_ctor_get(x_223, 1);
lean_inc(x_224);
if (lean_is_exclusive(x_223)) {
 lean_ctor_release(x_223, 0);
 lean_ctor_release(x_223, 1);
 x_225 = x_223;
} else {
 lean_dec_ref(x_223);
 x_225 = lean_box(0);
}
x_226 = lean_mk_string_unchecked("(expose_names; ", 15, 15);
x_227 = l_Lean_stringToMessageData(x_226);
lean_dec(x_226);
x_228 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_228, 0, x_227);
lean_ctor_set(x_228, 1, x_2);
x_229 = l_Lean_stringToMessageData(x_220);
lean_dec(x_220);
x_230 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_230, 0, x_228);
lean_ctor_set(x_230, 1, x_229);
x_231 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_231, 0, x_222);
lean_ctor_set(x_231, 1, x_230);
x_232 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_232, 0, x_231);
if (lean_is_scalar(x_225)) {
 x_233 = lean_alloc_ctor(0, 2, 0);
} else {
 x_233 = x_225;
}
lean_ctor_set(x_233, 0, x_232);
lean_ctor_set(x_233, 1, x_224);
return x_233;
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; uint8_t x_238; 
lean_dec(x_222);
lean_dec(x_220);
lean_dec(x_2);
x_234 = lean_ctor_get(x_223, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_223, 1);
lean_inc(x_235);
if (lean_is_exclusive(x_223)) {
 lean_ctor_release(x_223, 0);
 lean_ctor_release(x_223, 1);
 x_236 = x_223;
} else {
 lean_dec_ref(x_223);
 x_236 = lean_box(0);
}
lean_inc(x_235);
lean_inc(x_234);
if (lean_is_scalar(x_236)) {
 x_237 = lean_alloc_ctor(1, 2, 0);
} else {
 x_237 = x_236;
}
lean_ctor_set(x_237, 0, x_234);
lean_ctor_set(x_237, 1, x_235);
x_238 = l_Lean_Exception_isInterrupt(x_234);
if (x_238 == 0)
{
uint8_t x_239; 
x_239 = l_Lean_Exception_isRuntime(x_234);
lean_dec(x_234);
x_14 = x_235;
x_15 = x_237;
x_16 = x_210;
x_17 = x_239;
goto block_25;
}
else
{
lean_dec(x_234);
x_14 = x_235;
x_15 = x_237;
x_16 = x_210;
x_17 = x_238;
goto block_25;
}
}
}
}
else
{
lean_dec(x_41);
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_30;
}
}
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; uint8_t x_246; uint8_t x_303; 
x_243 = lean_ctor_get(x_30, 0);
x_244 = lean_ctor_get(x_30, 1);
lean_inc(x_244);
lean_inc(x_243);
lean_dec(x_30);
lean_inc(x_244);
lean_inc(x_243);
x_245 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_245, 0, x_243);
lean_ctor_set(x_245, 1, x_244);
x_303 = l_Lean_Exception_isInterrupt(x_243);
if (x_303 == 0)
{
uint8_t x_304; 
x_304 = l_Lean_Exception_isRuntime(x_243);
lean_dec(x_243);
x_246 = x_304;
goto block_302;
}
else
{
lean_dec(x_243);
x_246 = x_303;
goto block_302;
}
block_302:
{
if (x_246 == 0)
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; 
lean_dec(x_245);
x_247 = l_Lean_Elab_Tactic_SavedState_restore(x_27, x_246, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_244);
x_248 = lean_ctor_get(x_247, 1);
lean_inc(x_248);
if (lean_is_exclusive(x_247)) {
 lean_ctor_release(x_247, 0);
 lean_ctor_release(x_247, 1);
 x_249 = x_247;
} else {
 lean_dec_ref(x_247);
 x_249 = lean_box(0);
}
x_250 = lean_st_ref_get(x_12, x_248);
x_251 = lean_ctor_get(x_250, 1);
lean_inc(x_251);
if (lean_is_exclusive(x_250)) {
 lean_ctor_release(x_250, 0);
 lean_ctor_release(x_250, 1);
 x_252 = x_250;
} else {
 lean_dec_ref(x_250);
 x_252 = lean_box(0);
}
x_253 = lean_ctor_get(x_11, 5);
lean_inc(x_253);
x_254 = l_Lean_SourceInfo_fromRef(x_253, x_246);
lean_dec(x_253);
x_255 = lean_mk_string_unchecked("Lean", 4, 4);
x_256 = lean_mk_string_unchecked("Parser", 6, 6);
x_257 = lean_mk_string_unchecked("Tactic", 6, 6);
x_258 = lean_mk_string_unchecked("tacticSeq", 9, 9);
x_259 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
lean_inc(x_257);
lean_inc(x_256);
lean_inc(x_255);
x_260 = l_Lean_Name_mkStr4(x_255, x_256, x_257, x_259);
x_261 = lean_mk_string_unchecked("null", 4, 4);
x_262 = l_Lean_Name_mkStr1(x_261);
x_263 = lean_mk_string_unchecked("exposeNames", 11, 11);
lean_inc(x_257);
lean_inc(x_256);
lean_inc(x_255);
x_264 = l_Lean_Name_mkStr4(x_255, x_256, x_257, x_263);
x_265 = lean_mk_string_unchecked("expose_names", 12, 12);
lean_inc(x_254);
if (lean_is_scalar(x_252)) {
 x_266 = lean_alloc_ctor(2, 2, 0);
} else {
 x_266 = x_252;
 lean_ctor_set_tag(x_266, 2);
}
lean_ctor_set(x_266, 0, x_254);
lean_ctor_set(x_266, 1, x_265);
lean_inc(x_254);
x_267 = l_Lean_Syntax_node1(x_254, x_264, x_266);
x_268 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_254);
if (lean_is_scalar(x_249)) {
 x_269 = lean_alloc_ctor(2, 2, 0);
} else {
 x_269 = x_249;
 lean_ctor_set_tag(x_269, 2);
}
lean_ctor_set(x_269, 0, x_254);
lean_ctor_set(x_269, 1, x_268);
lean_inc(x_254);
x_270 = l_Lean_Syntax_node3(x_254, x_262, x_267, x_269, x_1);
x_271 = l_Lean_Elab_Tactic_saveState___redArg(x_6, x_8, x_10, x_11, x_12, x_251);
x_272 = lean_ctor_get(x_271, 0);
lean_inc(x_272);
x_273 = lean_ctor_get(x_271, 1);
lean_inc(x_273);
if (lean_is_exclusive(x_271)) {
 lean_ctor_release(x_271, 0);
 lean_ctor_release(x_271, 1);
 x_274 = x_271;
} else {
 lean_dec_ref(x_271);
 x_274 = lean_box(0);
}
x_275 = lean_mk_string_unchecked("paren", 5, 5);
x_276 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_257);
lean_inc(x_256);
lean_inc(x_255);
x_277 = l_Lean_Name_mkStr4(x_255, x_256, x_257, x_258);
lean_inc(x_254);
x_278 = l_Lean_Syntax_node1(x_254, x_260, x_270);
x_279 = l_Lean_Name_mkStr4(x_255, x_256, x_257, x_275);
lean_inc(x_254);
if (lean_is_scalar(x_274)) {
 x_280 = lean_alloc_ctor(2, 2, 0);
} else {
 x_280 = x_274;
 lean_ctor_set_tag(x_280, 2);
}
lean_ctor_set(x_280, 0, x_254);
lean_ctor_set(x_280, 1, x_276);
lean_inc(x_254);
x_281 = l_Lean_Syntax_node1(x_254, x_277, x_278);
x_282 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_282);
lean_inc(x_254);
if (lean_is_scalar(x_29)) {
 x_283 = lean_alloc_ctor(2, 2, 0);
} else {
 x_283 = x_29;
 lean_ctor_set_tag(x_283, 2);
}
lean_ctor_set(x_283, 0, x_254);
lean_ctor_set(x_283, 1, x_282);
x_284 = l_Lean_Syntax_node3(x_254, x_279, x_280, x_281, x_283);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_284);
x_285 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState(x_3, x_284, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_273);
if (lean_obj_tag(x_285) == 0)
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; 
lean_dec(x_272);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_286 = lean_ctor_get(x_285, 1);
lean_inc(x_286);
if (lean_is_exclusive(x_285)) {
 lean_ctor_release(x_285, 0);
 lean_ctor_release(x_285, 1);
 x_287 = x_285;
} else {
 lean_dec_ref(x_285);
 x_287 = lean_box(0);
}
x_288 = lean_mk_string_unchecked("(expose_names; ", 15, 15);
x_289 = l_Lean_stringToMessageData(x_288);
lean_dec(x_288);
x_290 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_290, 0, x_289);
lean_ctor_set(x_290, 1, x_2);
x_291 = l_Lean_stringToMessageData(x_282);
lean_dec(x_282);
x_292 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_292, 0, x_290);
lean_ctor_set(x_292, 1, x_291);
x_293 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_293, 0, x_284);
lean_ctor_set(x_293, 1, x_292);
x_294 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_294, 0, x_293);
if (lean_is_scalar(x_287)) {
 x_295 = lean_alloc_ctor(0, 2, 0);
} else {
 x_295 = x_287;
}
lean_ctor_set(x_295, 0, x_294);
lean_ctor_set(x_295, 1, x_286);
return x_295;
}
else
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; uint8_t x_300; 
lean_dec(x_284);
lean_dec(x_282);
lean_dec(x_2);
x_296 = lean_ctor_get(x_285, 0);
lean_inc(x_296);
x_297 = lean_ctor_get(x_285, 1);
lean_inc(x_297);
if (lean_is_exclusive(x_285)) {
 lean_ctor_release(x_285, 0);
 lean_ctor_release(x_285, 1);
 x_298 = x_285;
} else {
 lean_dec_ref(x_285);
 x_298 = lean_box(0);
}
lean_inc(x_297);
lean_inc(x_296);
if (lean_is_scalar(x_298)) {
 x_299 = lean_alloc_ctor(1, 2, 0);
} else {
 x_299 = x_298;
}
lean_ctor_set(x_299, 0, x_296);
lean_ctor_set(x_299, 1, x_297);
x_300 = l_Lean_Exception_isInterrupt(x_296);
if (x_300 == 0)
{
uint8_t x_301; 
x_301 = l_Lean_Exception_isRuntime(x_296);
lean_dec(x_296);
x_14 = x_297;
x_15 = x_299;
x_16 = x_272;
x_17 = x_301;
goto block_25;
}
else
{
lean_dec(x_296);
x_14 = x_297;
x_15 = x_299;
x_16 = x_272;
x_17 = x_300;
goto block_25;
}
}
}
else
{
lean_dec(x_244);
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_245;
}
}
}
}
block_25:
{
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
lean_dec(x_15);
x_18 = l_Lean_Elab_Tactic_SavedState_restore(x_16, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
x_21 = lean_box(0);
lean_ctor_set(x_18, 0, x_21);
return x_18;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_dec(x_18);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_7);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_3 = lean_mk_string_unchecked("found ", 6, 6);
x_4 = l_Lean_stringToMessageData(x_3);
lean_dec(x_3);
x_5 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_1);
x_6 = lean_mk_string_unchecked(", but the corresponding tactic failed:", 38, 38);
x_7 = l_Lean_stringToMessageData(x_6);
lean_dec(x_6);
x_8 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_7);
x_9 = l_Lean_indentD(x_2);
x_10 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_mk_string_unchecked("\n\nIt may be possible to correct this proof by adding type annotations, explicitly specifying implicit arguments, or eliminating unnecessary function abstractions.", 162, 162);
x_12 = l_Lean_stringToMessageData(x_11);
lean_dec(x_11);
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_55; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_55 = l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_55) == 0)
{
if (x_2 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = lean_st_ref_get(x_6, x_57);
x_59 = !lean_is_exclusive(x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_60 = lean_ctor_get(x_58, 1);
x_61 = lean_ctor_get(x_58, 0);
lean_dec(x_61);
x_62 = lean_ctor_get(x_5, 5);
lean_inc(x_62);
x_63 = l_Lean_SourceInfo_fromRef(x_62, x_2);
lean_dec(x_62);
x_64 = lean_mk_string_unchecked("Lean", 4, 4);
x_65 = lean_mk_string_unchecked("Parser", 6, 6);
x_66 = lean_mk_string_unchecked("Tactic", 6, 6);
x_67 = lean_mk_string_unchecked("exact", 5, 5);
lean_inc(x_67);
x_68 = l_Lean_Name_mkStr4(x_64, x_65, x_66, x_67);
lean_inc(x_63);
lean_ctor_set_tag(x_58, 2);
lean_ctor_set(x_58, 1, x_67);
lean_ctor_set(x_58, 0, x_63);
x_69 = l_Lean_Syntax_node2(x_63, x_68, x_58, x_56);
x_14 = x_69;
x_15 = x_3;
x_16 = x_4;
x_17 = x_5;
x_18 = x_6;
x_19 = x_60;
goto block_54;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_70 = lean_ctor_get(x_58, 1);
lean_inc(x_70);
lean_dec(x_58);
x_71 = lean_ctor_get(x_5, 5);
lean_inc(x_71);
x_72 = l_Lean_SourceInfo_fromRef(x_71, x_2);
lean_dec(x_71);
x_73 = lean_mk_string_unchecked("Lean", 4, 4);
x_74 = lean_mk_string_unchecked("Parser", 6, 6);
x_75 = lean_mk_string_unchecked("Tactic", 6, 6);
x_76 = lean_mk_string_unchecked("exact", 5, 5);
lean_inc(x_76);
x_77 = l_Lean_Name_mkStr4(x_73, x_74, x_75, x_76);
lean_inc(x_72);
x_78 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_78, 0, x_72);
lean_ctor_set(x_78, 1, x_76);
x_79 = l_Lean_Syntax_node2(x_72, x_77, x_78, x_56);
x_14 = x_79;
x_15 = x_3;
x_16 = x_4;
x_17 = x_5;
x_18 = x_6;
x_19 = x_70;
goto block_54;
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_80 = lean_ctor_get(x_55, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_55, 1);
lean_inc(x_81);
lean_dec(x_55);
x_82 = lean_st_ref_get(x_6, x_81);
x_83 = !lean_is_exclusive(x_82);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_84 = lean_ctor_get(x_82, 1);
x_85 = lean_ctor_get(x_82, 0);
lean_dec(x_85);
x_86 = lean_ctor_get(x_5, 5);
lean_inc(x_86);
x_87 = lean_box(0);
x_88 = lean_unbox(x_87);
x_89 = l_Lean_SourceInfo_fromRef(x_86, x_88);
lean_dec(x_86);
x_90 = lean_mk_string_unchecked("Lean", 4, 4);
x_91 = lean_mk_string_unchecked("Parser", 6, 6);
x_92 = lean_mk_string_unchecked("Tactic", 6, 6);
x_93 = lean_mk_string_unchecked("refine", 6, 6);
lean_inc(x_93);
x_94 = l_Lean_Name_mkStr4(x_90, x_91, x_92, x_93);
lean_inc(x_89);
lean_ctor_set_tag(x_82, 2);
lean_ctor_set(x_82, 1, x_93);
lean_ctor_set(x_82, 0, x_89);
x_95 = l_Lean_Syntax_node2(x_89, x_94, x_82, x_80);
x_14 = x_95;
x_15 = x_3;
x_16 = x_4;
x_17 = x_5;
x_18 = x_6;
x_19 = x_84;
goto block_54;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_96 = lean_ctor_get(x_82, 1);
lean_inc(x_96);
lean_dec(x_82);
x_97 = lean_ctor_get(x_5, 5);
lean_inc(x_97);
x_98 = lean_box(0);
x_99 = lean_unbox(x_98);
x_100 = l_Lean_SourceInfo_fromRef(x_97, x_99);
lean_dec(x_97);
x_101 = lean_mk_string_unchecked("Lean", 4, 4);
x_102 = lean_mk_string_unchecked("Parser", 6, 6);
x_103 = lean_mk_string_unchecked("Tactic", 6, 6);
x_104 = lean_mk_string_unchecked("refine", 6, 6);
lean_inc(x_104);
x_105 = l_Lean_Name_mkStr4(x_101, x_102, x_103, x_104);
lean_inc(x_100);
x_106 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_106, 0, x_100);
lean_ctor_set(x_106, 1, x_104);
x_107 = l_Lean_Syntax_node2(x_100, x_105, x_106, x_80);
x_14 = x_107;
x_15 = x_3;
x_16 = x_4;
x_17 = x_5;
x_18 = x_6;
x_19 = x_96;
goto block_54;
}
}
}
else
{
uint8_t x_108; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_108 = !lean_is_exclusive(x_55);
if (x_108 == 0)
{
return x_55;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_55, 0);
x_110 = lean_ctor_get(x_55, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_55);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
block_13:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
block_54:
{
lean_object* x_20; lean_object* x_21; 
x_20 = l_Lean_MessageData_ofExpr(x_1);
x_21 = l_Lean_addMessageContextFull___at___Lean_Meta_recordSynthPendingFailure_spec__3(x_20, x_15, x_16, x_17, x_18, x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
if (x_2 == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_21, 1);
x_25 = lean_mk_string_unchecked("exact ", 6, 6);
x_26 = l_Lean_stringToMessageData(x_25);
lean_dec(x_25);
lean_ctor_set_tag(x_21, 7);
lean_ctor_set(x_21, 1, x_23);
lean_ctor_set(x_21, 0, x_26);
x_27 = lean_mk_string_unchecked("", 0, 0);
x_28 = l_Lean_stringToMessageData(x_27);
lean_dec(x_27);
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_21);
lean_ctor_set(x_29, 1, x_28);
x_8 = x_14;
x_9 = x_24;
x_10 = x_29;
goto block_13;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_30 = lean_ctor_get(x_21, 0);
x_31 = lean_ctor_get(x_21, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_21);
x_32 = lean_mk_string_unchecked("exact ", 6, 6);
x_33 = l_Lean_stringToMessageData(x_32);
lean_dec(x_32);
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_30);
x_35 = lean_mk_string_unchecked("", 0, 0);
x_36 = l_Lean_stringToMessageData(x_35);
lean_dec(x_35);
x_37 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_36);
x_8 = x_14;
x_9 = x_31;
x_10 = x_37;
goto block_13;
}
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_21);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_39 = lean_ctor_get(x_21, 0);
x_40 = lean_ctor_get(x_21, 1);
x_41 = lean_mk_string_unchecked("refine ", 7, 7);
x_42 = l_Lean_stringToMessageData(x_41);
lean_dec(x_41);
lean_ctor_set_tag(x_21, 7);
lean_ctor_set(x_21, 1, x_39);
lean_ctor_set(x_21, 0, x_42);
x_43 = lean_mk_string_unchecked("", 0, 0);
x_44 = l_Lean_stringToMessageData(x_43);
lean_dec(x_43);
x_45 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_45, 0, x_21);
lean_ctor_set(x_45, 1, x_44);
x_8 = x_14;
x_9 = x_40;
x_10 = x_45;
goto block_13;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_46 = lean_ctor_get(x_21, 0);
x_47 = lean_ctor_get(x_21, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_21);
x_48 = lean_mk_string_unchecked("refine ", 7, 7);
x_49 = l_Lean_stringToMessageData(x_48);
lean_dec(x_48);
x_50 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_46);
x_51 = lean_mk_string_unchecked("", 0, 0);
x_52 = l_Lean_stringToMessageData(x_51);
lean_dec(x_51);
x_53 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_52);
x_8 = x_14;
x_9 = x_47;
x_10 = x_53;
goto block_13;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_74; uint8_t x_75; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_box(x_2);
x_12 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___boxed), 7, 2);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_11);
x_13 = lean_ctor_get(x_5, 2);
lean_inc(x_13);
x_14 = l_Lean_pp_mvars;
x_15 = lean_box(0);
x_16 = l_Lean_diagnostics;
x_17 = lean_unbox(x_15);
x_18 = l_Lean_Option_set___at___Lean_Environment_realizeConst_spec__2(x_13, x_14, x_17);
x_19 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_18, x_16);
x_74 = lean_ctor_get(x_9, 0);
lean_inc(x_74);
lean_dec(x_9);
x_75 = l_Lean_Kernel_isDiagnosticsEnabled(x_74);
lean_dec(x_74);
if (x_75 == 0)
{
if (x_19 == 0)
{
x_20 = x_5;
x_21 = x_6;
x_22 = x_10;
goto block_39;
}
else
{
goto block_73;
}
}
else
{
if (x_19 == 0)
{
goto block_73;
}
else
{
x_20 = x_5;
x_21 = x_6;
x_22 = x_10;
goto block_39;
}
}
block_39:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_20, 3);
lean_inc(x_25);
x_26 = l_Lean_maxRecDepth;
x_27 = l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(x_18, x_26);
x_28 = lean_ctor_get(x_20, 5);
lean_inc(x_28);
x_29 = lean_ctor_get(x_20, 6);
lean_inc(x_29);
x_30 = lean_ctor_get(x_20, 7);
lean_inc(x_30);
x_31 = lean_ctor_get(x_20, 8);
lean_inc(x_31);
x_32 = lean_ctor_get(x_20, 9);
lean_inc(x_32);
x_33 = lean_ctor_get(x_20, 10);
lean_inc(x_33);
x_34 = lean_ctor_get(x_20, 11);
lean_inc(x_34);
x_35 = lean_ctor_get_uint8(x_20, sizeof(void*)*13 + 1);
x_36 = lean_ctor_get(x_20, 12);
lean_inc(x_36);
lean_dec(x_20);
x_37 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_37, 0, x_23);
lean_ctor_set(x_37, 1, x_24);
lean_ctor_set(x_37, 2, x_18);
lean_ctor_set(x_37, 3, x_25);
lean_ctor_set(x_37, 4, x_27);
lean_ctor_set(x_37, 5, x_28);
lean_ctor_set(x_37, 6, x_29);
lean_ctor_set(x_37, 7, x_30);
lean_ctor_set(x_37, 8, x_31);
lean_ctor_set(x_37, 9, x_32);
lean_ctor_set(x_37, 10, x_33);
lean_ctor_set(x_37, 11, x_34);
lean_ctor_set(x_37, 12, x_36);
lean_ctor_set_uint8(x_37, sizeof(void*)*13, x_19);
lean_ctor_set_uint8(x_37, sizeof(void*)*13 + 1, x_35);
x_38 = l_Lean_Meta_withExposedNames___redArg(x_12, x_3, x_4, x_37, x_21, x_22);
return x_38;
}
block_73:
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_st_ref_take(x_6, x_10);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_42 = lean_ctor_get(x_40, 0);
x_43 = lean_ctor_get(x_40, 1);
x_44 = lean_ctor_get(x_42, 0);
lean_inc(x_44);
x_45 = l_Lean_Kernel_enableDiag(x_44, x_19);
x_46 = lean_ctor_get(x_42, 1);
lean_inc(x_46);
x_47 = lean_ctor_get(x_42, 2);
lean_inc(x_47);
x_48 = lean_ctor_get(x_42, 3);
lean_inc(x_48);
x_49 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_50 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_50, 0, x_49);
lean_inc(x_50);
lean_ctor_set(x_40, 1, x_50);
lean_ctor_set(x_40, 0, x_50);
x_51 = lean_ctor_get(x_42, 5);
lean_inc(x_51);
x_52 = lean_ctor_get(x_42, 6);
lean_inc(x_52);
x_53 = lean_ctor_get(x_42, 7);
lean_inc(x_53);
lean_dec(x_42);
x_54 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_54, 0, x_45);
lean_ctor_set(x_54, 1, x_46);
lean_ctor_set(x_54, 2, x_47);
lean_ctor_set(x_54, 3, x_48);
lean_ctor_set(x_54, 4, x_40);
lean_ctor_set(x_54, 5, x_51);
lean_ctor_set(x_54, 6, x_52);
lean_ctor_set(x_54, 7, x_53);
x_55 = lean_st_ref_set(x_6, x_54, x_43);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
x_20 = x_5;
x_21 = x_6;
x_22 = x_56;
goto block_39;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_57 = lean_ctor_get(x_40, 0);
x_58 = lean_ctor_get(x_40, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_40);
x_59 = lean_ctor_get(x_57, 0);
lean_inc(x_59);
x_60 = l_Lean_Kernel_enableDiag(x_59, x_19);
x_61 = lean_ctor_get(x_57, 1);
lean_inc(x_61);
x_62 = lean_ctor_get(x_57, 2);
lean_inc(x_62);
x_63 = lean_ctor_get(x_57, 3);
lean_inc(x_63);
x_64 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_65 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_65, 0, x_64);
lean_inc(x_65);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_65);
x_67 = lean_ctor_get(x_57, 5);
lean_inc(x_67);
x_68 = lean_ctor_get(x_57, 6);
lean_inc(x_68);
x_69 = lean_ctor_get(x_57, 7);
lean_inc(x_69);
lean_dec(x_57);
x_70 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_70, 0, x_60);
lean_ctor_set(x_70, 1, x_61);
lean_ctor_set(x_70, 2, x_62);
lean_ctor_set(x_70, 3, x_63);
lean_ctor_set(x_70, 4, x_66);
lean_ctor_set(x_70, 5, x_67);
lean_ctor_set(x_70, 6, x_68);
lean_ctor_set(x_70, 7, x_69);
x_71 = lean_st_ref_set(x_6, x_70, x_58);
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
lean_dec(x_71);
x_20 = x_5;
x_21 = x_6;
x_22 = x_72;
goto block_39;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lam__0(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore_spec__0_spec__0___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_3, x_2);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_array_uget(x_1, x_3);
x_13 = l_Lean_MVarId_getType(x_12, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_instantiateMVars___at___Lean_Elab_Tactic_getMainTarget_spec__0___redArg(x_14, x_6, x_15);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
x_20 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_ppExpr), 6, 1);
lean_closure_set(x_20, 0, x_18);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_21 = l_Lean_Meta_withExposedNames___redArg(x_20, x_5, x_6, x_7, x_8, x_19);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; size_t x_31; size_t x_32; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_mk_string_unchecked("\n⊢ ", 5, 3);
x_25 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set_tag(x_16, 5);
lean_ctor_set(x_16, 1, x_22);
lean_ctor_set(x_16, 0, x_25);
x_26 = lean_unsigned_to_nat(120u);
x_27 = lean_unsigned_to_nat(0u);
x_28 = lean_format_pretty(x_16, x_26, x_27, x_27);
x_29 = lean_string_append(x_4, x_28);
lean_dec(x_28);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_usize_of_nat(x_30);
x_32 = lean_usize_add(x_3, x_31);
x_3 = x_32;
x_4 = x_29;
x_9 = x_23;
goto _start;
}
else
{
uint8_t x_34; 
lean_free_object(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_34 = !lean_is_exclusive(x_21);
if (x_34 == 0)
{
return x_21;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_21, 0);
x_36 = lean_ctor_get(x_21, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_21);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_16, 0);
x_39 = lean_ctor_get(x_16, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_16);
x_40 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_ppExpr), 6, 1);
lean_closure_set(x_40, 0, x_38);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_41 = l_Lean_Meta_withExposedNames___redArg(x_40, x_5, x_6, x_7, x_8, x_39);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; size_t x_52; size_t x_53; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_mk_string_unchecked("\n⊢ ", 5, 3);
x_45 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_45, 0, x_44);
x_46 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_42);
x_47 = lean_unsigned_to_nat(120u);
x_48 = lean_unsigned_to_nat(0u);
x_49 = lean_format_pretty(x_46, x_47, x_48, x_48);
x_50 = lean_string_append(x_4, x_49);
lean_dec(x_49);
x_51 = lean_unsigned_to_nat(1u);
x_52 = lean_usize_of_nat(x_51);
x_53 = lean_usize_add(x_3, x_52);
x_3 = x_53;
x_4 = x_50;
x_9 = x_43;
goto _start;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_55 = lean_ctor_get(x_41, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_41, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_57 = x_41;
} else {
 lean_dec_ref(x_41);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(1, 2, 0);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_56);
return x_58;
}
}
}
else
{
uint8_t x_59; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_59 = !lean_is_exclusive(x_13);
if (x_59 == 0)
{
return x_13;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_13, 0);
x_61 = lean_ctor_get(x_13, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_13);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore_spec__0_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_9, x_10, x_11, x_12, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
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
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_array_uget(x_1, x_3);
x_17 = l_Lean_MVarId_getType(x_16, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_instantiateMVars___at___Lean_Elab_Tactic_getMainTarget_spec__0___redArg(x_18, x_10, x_19);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
x_24 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_ppExpr), 6, 1);
lean_closure_set(x_24, 0, x_22);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_25 = l_Lean_Meta_withExposedNames___redArg(x_24, x_9, x_10, x_11, x_12, x_23);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; size_t x_35; size_t x_36; lean_object* x_37; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_mk_string_unchecked("\n⊢ ", 5, 3);
x_29 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set_tag(x_20, 5);
lean_ctor_set(x_20, 1, x_26);
lean_ctor_set(x_20, 0, x_29);
x_30 = lean_unsigned_to_nat(120u);
x_31 = lean_unsigned_to_nat(0u);
x_32 = lean_format_pretty(x_20, x_30, x_31, x_31);
x_33 = lean_string_append(x_4, x_32);
lean_dec(x_32);
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_usize_of_nat(x_34);
x_36 = lean_usize_add(x_3, x_35);
x_37 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore_spec__0_spec__0___redArg(x_1, x_2, x_36, x_33, x_9, x_10, x_11, x_12, x_27);
return x_37;
}
else
{
uint8_t x_38; 
lean_free_object(x_20);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_38 = !lean_is_exclusive(x_25);
if (x_38 == 0)
{
return x_25;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_25, 0);
x_40 = lean_ctor_get(x_25, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_25);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_20, 0);
x_43 = lean_ctor_get(x_20, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_20);
x_44 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_ppExpr), 6, 1);
lean_closure_set(x_44, 0, x_42);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_45 = l_Lean_Meta_withExposedNames___redArg(x_44, x_9, x_10, x_11, x_12, x_43);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; size_t x_56; size_t x_57; lean_object* x_58; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_mk_string_unchecked("\n⊢ ", 5, 3);
x_49 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_49, 0, x_48);
x_50 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_46);
x_51 = lean_unsigned_to_nat(120u);
x_52 = lean_unsigned_to_nat(0u);
x_53 = lean_format_pretty(x_50, x_51, x_52, x_52);
x_54 = lean_string_append(x_4, x_53);
lean_dec(x_53);
x_55 = lean_unsigned_to_nat(1u);
x_56 = lean_usize_of_nat(x_55);
x_57 = lean_usize_add(x_3, x_56);
x_58 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore_spec__0_spec__0___redArg(x_1, x_2, x_57, x_54, x_9, x_10, x_11, x_12, x_47);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_59 = lean_ctor_get(x_45, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_45, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_61 = x_45;
} else {
 lean_dec_ref(x_45);
 x_61 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(1, 2, 0);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
}
}
else
{
uint8_t x_63; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_63 = !lean_is_exclusive(x_17);
if (x_63 == 0)
{
return x_17;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_17, 0);
x_65 = lean_ctor_get(x_17, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_17);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; uint8_t x_51; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; uint8_t x_226; lean_object* x_227; uint8_t x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_289; uint8_t x_290; 
x_219 = lean_st_ref_get(x_11, x_12);
x_220 = lean_ctor_get(x_219, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_219, 1);
lean_inc(x_221);
lean_dec(x_219);
x_222 = lean_ctor_get(x_10, 2);
lean_inc(x_222);
x_223 = l_Lean_pp_mvars;
x_224 = lean_box(0);
x_225 = l_Lean_diagnostics;
x_226 = lean_unbox(x_224);
x_227 = l_Lean_Option_set___at___Lean_Environment_realizeConst_spec__2(x_222, x_223, x_226);
x_228 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_227, x_225);
x_289 = lean_ctor_get(x_220, 0);
lean_inc(x_289);
lean_dec(x_220);
x_290 = l_Lean_Kernel_isDiagnosticsEnabled(x_289);
lean_dec(x_289);
if (x_290 == 0)
{
if (x_228 == 0)
{
x_229 = x_10;
x_230 = x_11;
x_231 = x_221;
goto block_254;
}
else
{
goto block_288;
}
}
else
{
if (x_228 == 0)
{
goto block_288;
}
else
{
x_229 = x_10;
x_230 = x_11;
x_231 = x_221;
goto block_254;
}
}
block_25:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_17 = l_Lean_stringToMessageData(x_16);
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_mk_string_unchecked("proof", 5, 5);
x_20 = l_Lean_stringToMessageData(x_19);
lean_dec(x_19);
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
x_22 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg(x_21, x_14);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_13);
return x_24;
}
block_40:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_30 = lean_mk_string_unchecked("tactic", 6, 6);
x_31 = l_Lean_Name_mkStr1(x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_27);
x_33 = lean_box(0);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_26);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_37, 0, x_32);
lean_ctor_set(x_37, 1, x_33);
lean_ctor_set(x_37, 2, x_28);
lean_ctor_set(x_37, 3, x_34);
lean_ctor_set(x_37, 4, x_35);
lean_ctor_set(x_37, 5, x_36);
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_29);
return x_39;
}
block_45:
{
lean_object* x_44; 
x_44 = lean_box(0);
x_26 = x_41;
x_27 = x_43;
x_28 = x_44;
x_29 = x_42;
goto block_40;
}
block_218:
{
lean_object* x_52; 
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_9);
lean_inc(x_8);
x_52 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax(x_3, x_51, x_8, x_9, x_46, x_47, x_50);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_54; 
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_54 = !lean_is_exclusive(x_52);
if (x_54 == 0)
{
lean_object* x_55; uint8_t x_56; 
x_55 = lean_ctor_get(x_52, 0);
lean_dec(x_55);
x_56 = !lean_is_exclusive(x_53);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_57 = lean_ctor_get(x_53, 0);
x_58 = lean_ctor_get(x_53, 1);
lean_dec(x_58);
x_59 = lean_mk_string_unchecked("tactic", 6, 6);
x_60 = l_Lean_Name_mkStr1(x_59);
lean_ctor_set(x_53, 1, x_57);
lean_ctor_set(x_53, 0, x_60);
x_61 = lean_box(0);
x_62 = lean_box(0);
x_63 = lean_box(0);
x_64 = lean_box(0);
x_65 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_65, 0, x_53);
lean_ctor_set(x_65, 1, x_61);
lean_ctor_set(x_65, 2, x_61);
lean_ctor_set(x_65, 3, x_62);
lean_ctor_set(x_65, 4, x_63);
lean_ctor_set(x_65, 5, x_64);
x_66 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_52, 0, x_66);
return x_52;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_67 = lean_ctor_get(x_53, 0);
lean_inc(x_67);
lean_dec(x_53);
x_68 = lean_mk_string_unchecked("tactic", 6, 6);
x_69 = l_Lean_Name_mkStr1(x_68);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_67);
x_71 = lean_box(0);
x_72 = lean_box(0);
x_73 = lean_box(0);
x_74 = lean_box(0);
x_75 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_75, 0, x_70);
lean_ctor_set(x_75, 1, x_71);
lean_ctor_set(x_75, 2, x_71);
lean_ctor_set(x_75, 3, x_72);
lean_ctor_set(x_75, 4, x_73);
lean_ctor_set(x_75, 5, x_74);
x_76 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_52, 0, x_76);
return x_52;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_77 = lean_ctor_get(x_52, 1);
lean_inc(x_77);
lean_dec(x_52);
x_78 = lean_ctor_get(x_53, 0);
lean_inc(x_78);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_79 = x_53;
} else {
 lean_dec_ref(x_53);
 x_79 = lean_box(0);
}
x_80 = lean_mk_string_unchecked("tactic", 6, 6);
x_81 = l_Lean_Name_mkStr1(x_80);
if (lean_is_scalar(x_79)) {
 x_82 = lean_alloc_ctor(0, 2, 0);
} else {
 x_82 = x_79;
}
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_78);
x_83 = lean_box(0);
x_84 = lean_box(0);
x_85 = lean_box(0);
x_86 = lean_box(0);
x_87 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_87, 0, x_82);
lean_ctor_set(x_87, 1, x_83);
lean_ctor_set(x_87, 2, x_83);
lean_ctor_set(x_87, 3, x_84);
lean_ctor_set(x_87, 4, x_85);
lean_ctor_set(x_87, 5, x_86);
x_88 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_88, 0, x_87);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_77);
return x_89;
}
}
else
{
lean_object* x_90; uint8_t x_91; 
x_90 = lean_ctor_get(x_52, 1);
lean_inc(x_90);
lean_dec(x_52);
x_91 = !lean_is_exclusive(x_53);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_92 = lean_ctor_get(x_53, 0);
x_93 = lean_ctor_get(x_53, 1);
x_94 = lean_ctor_get(x_2, 0);
lean_inc(x_94);
lean_dec(x_2);
x_95 = lean_box(0);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_93);
x_96 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic(x_92, x_93, x_94, x_95, x_4, x_5, x_6, x_7, x_8, x_9, x_46, x_47, x_90);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
lean_dec(x_96);
x_99 = lean_mk_string_unchecked("(expose_names; ", 15, 15);
x_100 = l_Lean_stringToMessageData(x_99);
lean_dec(x_99);
lean_ctor_set_tag(x_53, 7);
lean_ctor_set(x_53, 0, x_100);
x_101 = lean_mk_string_unchecked(")", 1, 1);
x_102 = l_Lean_stringToMessageData(x_101);
lean_dec(x_101);
x_103 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_103, 0, x_53);
lean_ctor_set(x_103, 1, x_102);
x_104 = lean_mk_string_unchecked("a ", 2, 2);
x_105 = l_Lean_stringToMessageData(x_104);
lean_dec(x_104);
if (x_51 == 0)
{
lean_object* x_106; 
x_106 = lean_mk_string_unchecked("", 0, 0);
x_13 = x_98;
x_14 = x_103;
x_15 = x_105;
x_16 = x_106;
goto block_25;
}
else
{
lean_object* x_107; 
x_107 = lean_mk_string_unchecked("partial ", 8, 8);
x_13 = x_98;
x_14 = x_103;
x_15 = x_105;
x_16 = x_107;
goto block_25;
}
}
else
{
uint8_t x_108; 
lean_free_object(x_53);
lean_dec(x_93);
x_108 = !lean_is_exclusive(x_97);
if (x_108 == 0)
{
if (x_1 == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_109 = lean_ctor_get(x_97, 0);
lean_free_object(x_97);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_110 = lean_ctor_get(x_96, 1);
lean_inc(x_110);
lean_dec(x_96);
x_111 = lean_ctor_get(x_109, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_109, 1);
lean_inc(x_112);
lean_dec(x_109);
x_41 = x_112;
x_42 = x_110;
x_43 = x_111;
goto block_45;
}
else
{
if (x_49 == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; size_t x_118; lean_object* x_119; size_t x_120; lean_object* x_121; 
x_113 = lean_ctor_get(x_97, 0);
x_114 = lean_ctor_get(x_96, 1);
lean_inc(x_114);
lean_dec(x_96);
x_115 = lean_ctor_get(x_113, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_113, 1);
lean_inc(x_116);
lean_dec(x_113);
x_117 = lean_mk_string_unchecked("\nRemaining subgoals:", 20, 20);
x_118 = lean_array_size(x_48);
x_119 = lean_unsigned_to_nat(0u);
x_120 = lean_usize_of_nat(x_119);
x_121 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore_spec__0(x_48, x_118, x_120, x_117, x_4, x_5, x_6, x_7, x_8, x_9, x_46, x_47, x_114);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_48);
if (lean_obj_tag(x_121) == 0)
{
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
lean_dec(x_121);
lean_ctor_set(x_97, 0, x_122);
x_26 = x_116;
x_27 = x_115;
x_28 = x_97;
x_29 = x_123;
goto block_40;
}
else
{
uint8_t x_124; 
lean_dec(x_116);
lean_dec(x_115);
lean_free_object(x_97);
x_124 = !lean_is_exclusive(x_121);
if (x_124 == 0)
{
lean_ctor_set_tag(x_121, 1);
return x_121;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_121, 0);
x_126 = lean_ctor_get(x_121, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_121);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
return x_127;
}
}
}
else
{
uint8_t x_128; 
lean_dec(x_116);
lean_dec(x_115);
lean_free_object(x_97);
x_128 = !lean_is_exclusive(x_121);
if (x_128 == 0)
{
return x_121;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_121, 0);
x_130 = lean_ctor_get(x_121, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_121);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
return x_131;
}
}
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_132 = lean_ctor_get(x_97, 0);
lean_free_object(x_97);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_133 = lean_ctor_get(x_96, 1);
lean_inc(x_133);
lean_dec(x_96);
x_134 = lean_ctor_get(x_132, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_132, 1);
lean_inc(x_135);
lean_dec(x_132);
x_41 = x_135;
x_42 = x_133;
x_43 = x_134;
goto block_45;
}
}
}
else
{
lean_object* x_136; 
x_136 = lean_ctor_get(x_97, 0);
lean_inc(x_136);
lean_dec(x_97);
if (x_1 == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_137 = lean_ctor_get(x_96, 1);
lean_inc(x_137);
lean_dec(x_96);
x_138 = lean_ctor_get(x_136, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_136, 1);
lean_inc(x_139);
lean_dec(x_136);
x_41 = x_139;
x_42 = x_137;
x_43 = x_138;
goto block_45;
}
else
{
if (x_49 == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; size_t x_144; lean_object* x_145; size_t x_146; lean_object* x_147; 
x_140 = lean_ctor_get(x_96, 1);
lean_inc(x_140);
lean_dec(x_96);
x_141 = lean_ctor_get(x_136, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_136, 1);
lean_inc(x_142);
lean_dec(x_136);
x_143 = lean_mk_string_unchecked("\nRemaining subgoals:", 20, 20);
x_144 = lean_array_size(x_48);
x_145 = lean_unsigned_to_nat(0u);
x_146 = lean_usize_of_nat(x_145);
x_147 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore_spec__0(x_48, x_144, x_146, x_143, x_4, x_5, x_6, x_7, x_8, x_9, x_46, x_47, x_140);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_48);
if (lean_obj_tag(x_147) == 0)
{
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_147, 1);
lean_inc(x_149);
lean_dec(x_147);
x_150 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_150, 0, x_148);
x_26 = x_142;
x_27 = x_141;
x_28 = x_150;
x_29 = x_149;
goto block_40;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
lean_dec(x_142);
lean_dec(x_141);
x_151 = lean_ctor_get(x_147, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_147, 1);
lean_inc(x_152);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 lean_ctor_release(x_147, 1);
 x_153 = x_147;
} else {
 lean_dec_ref(x_147);
 x_153 = lean_box(0);
}
if (lean_is_scalar(x_153)) {
 x_154 = lean_alloc_ctor(1, 2, 0);
} else {
 x_154 = x_153;
 lean_ctor_set_tag(x_154, 1);
}
lean_ctor_set(x_154, 0, x_151);
lean_ctor_set(x_154, 1, x_152);
return x_154;
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
lean_dec(x_142);
lean_dec(x_141);
x_155 = lean_ctor_get(x_147, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_147, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 lean_ctor_release(x_147, 1);
 x_157 = x_147;
} else {
 lean_dec_ref(x_147);
 x_157 = lean_box(0);
}
if (lean_is_scalar(x_157)) {
 x_158 = lean_alloc_ctor(1, 2, 0);
} else {
 x_158 = x_157;
}
lean_ctor_set(x_158, 0, x_155);
lean_ctor_set(x_158, 1, x_156);
return x_158;
}
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; 
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_159 = lean_ctor_get(x_96, 1);
lean_inc(x_159);
lean_dec(x_96);
x_160 = lean_ctor_get(x_136, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_136, 1);
lean_inc(x_161);
lean_dec(x_136);
x_41 = x_161;
x_42 = x_159;
x_43 = x_160;
goto block_45;
}
}
}
}
}
else
{
uint8_t x_162; 
lean_free_object(x_53);
lean_dec(x_93);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_162 = !lean_is_exclusive(x_96);
if (x_162 == 0)
{
return x_96;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_ctor_get(x_96, 0);
x_164 = lean_ctor_get(x_96, 1);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_96);
x_165 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_165, 0, x_163);
lean_ctor_set(x_165, 1, x_164);
return x_165;
}
}
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_166 = lean_ctor_get(x_53, 0);
x_167 = lean_ctor_get(x_53, 1);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_53);
x_168 = lean_ctor_get(x_2, 0);
lean_inc(x_168);
lean_dec(x_2);
x_169 = lean_box(0);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_167);
x_170 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic(x_166, x_167, x_168, x_169, x_4, x_5, x_6, x_7, x_8, x_9, x_46, x_47, x_90);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; 
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
lean_dec(x_170);
x_173 = lean_mk_string_unchecked("(expose_names; ", 15, 15);
x_174 = l_Lean_stringToMessageData(x_173);
lean_dec(x_173);
x_175 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_167);
x_176 = lean_mk_string_unchecked(")", 1, 1);
x_177 = l_Lean_stringToMessageData(x_176);
lean_dec(x_176);
x_178 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_178, 0, x_175);
lean_ctor_set(x_178, 1, x_177);
x_179 = lean_mk_string_unchecked("a ", 2, 2);
x_180 = l_Lean_stringToMessageData(x_179);
lean_dec(x_179);
if (x_51 == 0)
{
lean_object* x_181; 
x_181 = lean_mk_string_unchecked("", 0, 0);
x_13 = x_172;
x_14 = x_178;
x_15 = x_180;
x_16 = x_181;
goto block_25;
}
else
{
lean_object* x_182; 
x_182 = lean_mk_string_unchecked("partial ", 8, 8);
x_13 = x_172;
x_14 = x_178;
x_15 = x_180;
x_16 = x_182;
goto block_25;
}
}
else
{
lean_object* x_183; lean_object* x_184; 
lean_dec(x_167);
x_183 = lean_ctor_get(x_171, 0);
lean_inc(x_183);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 x_184 = x_171;
} else {
 lean_dec_ref(x_171);
 x_184 = lean_box(0);
}
if (x_1 == 0)
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; 
lean_dec(x_184);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_185 = lean_ctor_get(x_170, 1);
lean_inc(x_185);
lean_dec(x_170);
x_186 = lean_ctor_get(x_183, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_183, 1);
lean_inc(x_187);
lean_dec(x_183);
x_41 = x_187;
x_42 = x_185;
x_43 = x_186;
goto block_45;
}
else
{
if (x_49 == 0)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; size_t x_192; lean_object* x_193; size_t x_194; lean_object* x_195; 
x_188 = lean_ctor_get(x_170, 1);
lean_inc(x_188);
lean_dec(x_170);
x_189 = lean_ctor_get(x_183, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_183, 1);
lean_inc(x_190);
lean_dec(x_183);
x_191 = lean_mk_string_unchecked("\nRemaining subgoals:", 20, 20);
x_192 = lean_array_size(x_48);
x_193 = lean_unsigned_to_nat(0u);
x_194 = lean_usize_of_nat(x_193);
x_195 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore_spec__0(x_48, x_192, x_194, x_191, x_4, x_5, x_6, x_7, x_8, x_9, x_46, x_47, x_188);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_48);
if (lean_obj_tag(x_195) == 0)
{
if (lean_obj_tag(x_195) == 0)
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_195, 1);
lean_inc(x_197);
lean_dec(x_195);
if (lean_is_scalar(x_184)) {
 x_198 = lean_alloc_ctor(1, 1, 0);
} else {
 x_198 = x_184;
}
lean_ctor_set(x_198, 0, x_196);
x_26 = x_190;
x_27 = x_189;
x_28 = x_198;
x_29 = x_197;
goto block_40;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
lean_dec(x_190);
lean_dec(x_189);
lean_dec(x_184);
x_199 = lean_ctor_get(x_195, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_195, 1);
lean_inc(x_200);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 x_201 = x_195;
} else {
 lean_dec_ref(x_195);
 x_201 = lean_box(0);
}
if (lean_is_scalar(x_201)) {
 x_202 = lean_alloc_ctor(1, 2, 0);
} else {
 x_202 = x_201;
 lean_ctor_set_tag(x_202, 1);
}
lean_ctor_set(x_202, 0, x_199);
lean_ctor_set(x_202, 1, x_200);
return x_202;
}
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
lean_dec(x_190);
lean_dec(x_189);
lean_dec(x_184);
x_203 = lean_ctor_get(x_195, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_195, 1);
lean_inc(x_204);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 x_205 = x_195;
} else {
 lean_dec_ref(x_195);
 x_205 = lean_box(0);
}
if (lean_is_scalar(x_205)) {
 x_206 = lean_alloc_ctor(1, 2, 0);
} else {
 x_206 = x_205;
}
lean_ctor_set(x_206, 0, x_203);
lean_ctor_set(x_206, 1, x_204);
return x_206;
}
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; 
lean_dec(x_184);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_207 = lean_ctor_get(x_170, 1);
lean_inc(x_207);
lean_dec(x_170);
x_208 = lean_ctor_get(x_183, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_183, 1);
lean_inc(x_209);
lean_dec(x_183);
x_41 = x_209;
x_42 = x_207;
x_43 = x_208;
goto block_45;
}
}
}
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
lean_dec(x_167);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_210 = lean_ctor_get(x_170, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_170, 1);
lean_inc(x_211);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 x_212 = x_170;
} else {
 lean_dec_ref(x_170);
 x_212 = lean_box(0);
}
if (lean_is_scalar(x_212)) {
 x_213 = lean_alloc_ctor(1, 2, 0);
} else {
 x_213 = x_212;
}
lean_ctor_set(x_213, 0, x_210);
lean_ctor_set(x_213, 1, x_211);
return x_213;
}
}
}
}
else
{
uint8_t x_214; 
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_214 = !lean_is_exclusive(x_52);
if (x_214 == 0)
{
return x_52;
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_215 = lean_ctor_get(x_52, 0);
x_216 = lean_ctor_get(x_52, 1);
lean_inc(x_216);
lean_inc(x_215);
lean_dec(x_52);
x_217 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_217, 0, x_215);
lean_ctor_set(x_217, 1, x_216);
return x_217;
}
}
}
block_254:
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; uint8_t x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; uint8_t x_250; 
x_232 = lean_ctor_get(x_229, 0);
lean_inc(x_232);
x_233 = lean_ctor_get(x_229, 1);
lean_inc(x_233);
x_234 = lean_ctor_get(x_229, 3);
lean_inc(x_234);
x_235 = l_Lean_maxRecDepth;
x_236 = l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(x_227, x_235);
x_237 = lean_ctor_get(x_229, 5);
lean_inc(x_237);
x_238 = lean_ctor_get(x_229, 6);
lean_inc(x_238);
x_239 = lean_ctor_get(x_229, 7);
lean_inc(x_239);
x_240 = lean_ctor_get(x_229, 8);
lean_inc(x_240);
x_241 = lean_ctor_get(x_229, 9);
lean_inc(x_241);
x_242 = lean_ctor_get(x_229, 10);
lean_inc(x_242);
x_243 = lean_ctor_get(x_229, 11);
lean_inc(x_243);
x_244 = lean_ctor_get_uint8(x_229, sizeof(void*)*13 + 1);
x_245 = lean_ctor_get(x_229, 12);
lean_inc(x_245);
lean_dec(x_229);
x_246 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_246, 0, x_232);
lean_ctor_set(x_246, 1, x_233);
lean_ctor_set(x_246, 2, x_227);
lean_ctor_set(x_246, 3, x_234);
lean_ctor_set(x_246, 4, x_236);
lean_ctor_set(x_246, 5, x_237);
lean_ctor_set(x_246, 6, x_238);
lean_ctor_set(x_246, 7, x_239);
lean_ctor_set(x_246, 8, x_240);
lean_ctor_set(x_246, 9, x_241);
lean_ctor_set(x_246, 10, x_242);
lean_ctor_set(x_246, 11, x_243);
lean_ctor_set(x_246, 12, x_245);
lean_ctor_set_uint8(x_246, sizeof(void*)*13, x_228);
lean_ctor_set_uint8(x_246, sizeof(void*)*13 + 1, x_244);
lean_inc(x_3);
x_247 = l_Lean_Meta_getMVars(x_3, x_8, x_9, x_246, x_230, x_231);
x_248 = lean_ctor_get(x_247, 0);
lean_inc(x_248);
x_249 = lean_ctor_get(x_247, 1);
lean_inc(x_249);
lean_dec(x_247);
x_250 = l_Array_isEmpty___redArg(x_248);
if (x_250 == 0)
{
lean_object* x_251; uint8_t x_252; 
x_251 = lean_box(1);
x_252 = lean_unbox(x_251);
x_46 = x_246;
x_47 = x_230;
x_48 = x_248;
x_49 = x_250;
x_50 = x_249;
x_51 = x_252;
goto block_218;
}
else
{
uint8_t x_253; 
x_253 = lean_unbox(x_224);
x_46 = x_246;
x_47 = x_230;
x_48 = x_248;
x_49 = x_250;
x_50 = x_249;
x_51 = x_253;
goto block_218;
}
}
block_288:
{
lean_object* x_255; uint8_t x_256; 
x_255 = lean_st_ref_take(x_11, x_221);
x_256 = !lean_is_exclusive(x_255);
if (x_256 == 0)
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; 
x_257 = lean_ctor_get(x_255, 0);
x_258 = lean_ctor_get(x_255, 1);
x_259 = lean_ctor_get(x_257, 0);
lean_inc(x_259);
x_260 = l_Lean_Kernel_enableDiag(x_259, x_228);
x_261 = lean_ctor_get(x_257, 1);
lean_inc(x_261);
x_262 = lean_ctor_get(x_257, 2);
lean_inc(x_262);
x_263 = lean_ctor_get(x_257, 3);
lean_inc(x_263);
x_264 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_265 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_265, 0, x_264);
lean_inc(x_265);
lean_ctor_set(x_255, 1, x_265);
lean_ctor_set(x_255, 0, x_265);
x_266 = lean_ctor_get(x_257, 5);
lean_inc(x_266);
x_267 = lean_ctor_get(x_257, 6);
lean_inc(x_267);
x_268 = lean_ctor_get(x_257, 7);
lean_inc(x_268);
lean_dec(x_257);
x_269 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_269, 0, x_260);
lean_ctor_set(x_269, 1, x_261);
lean_ctor_set(x_269, 2, x_262);
lean_ctor_set(x_269, 3, x_263);
lean_ctor_set(x_269, 4, x_255);
lean_ctor_set(x_269, 5, x_266);
lean_ctor_set(x_269, 6, x_267);
lean_ctor_set(x_269, 7, x_268);
x_270 = lean_st_ref_set(x_11, x_269, x_258);
x_271 = lean_ctor_get(x_270, 1);
lean_inc(x_271);
lean_dec(x_270);
x_229 = x_10;
x_230 = x_11;
x_231 = x_271;
goto block_254;
}
else
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; 
x_272 = lean_ctor_get(x_255, 0);
x_273 = lean_ctor_get(x_255, 1);
lean_inc(x_273);
lean_inc(x_272);
lean_dec(x_255);
x_274 = lean_ctor_get(x_272, 0);
lean_inc(x_274);
x_275 = l_Lean_Kernel_enableDiag(x_274, x_228);
x_276 = lean_ctor_get(x_272, 1);
lean_inc(x_276);
x_277 = lean_ctor_get(x_272, 2);
lean_inc(x_277);
x_278 = lean_ctor_get(x_272, 3);
lean_inc(x_278);
x_279 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_280 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_280, 0, x_279);
lean_inc(x_280);
x_281 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_281, 0, x_280);
lean_ctor_set(x_281, 1, x_280);
x_282 = lean_ctor_get(x_272, 5);
lean_inc(x_282);
x_283 = lean_ctor_get(x_272, 6);
lean_inc(x_283);
x_284 = lean_ctor_get(x_272, 7);
lean_inc(x_284);
lean_dec(x_272);
x_285 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_285, 0, x_275);
lean_ctor_set(x_285, 1, x_276);
lean_ctor_set(x_285, 2, x_277);
lean_ctor_set(x_285, 3, x_278);
lean_ctor_set(x_285, 4, x_281);
lean_ctor_set(x_285, 5, x_282);
lean_ctor_set(x_285, 6, x_283);
lean_ctor_set(x_285, 7, x_284);
x_286 = lean_st_ref_set(x_11, x_285, x_273);
x_287 = lean_ctor_get(x_286, 1);
lean_inc(x_287);
lean_dec(x_286);
x_229 = x_10;
x_230 = x_11;
x_231 = x_287;
goto block_254;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore_spec__0_spec__0___redArg(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_15 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_16 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore_spec__0_spec__0(x_1, x_14, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_15 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_16 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore_spec__0(x_1, x_14, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_1);
lean_dec(x_1);
x_14 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_6);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_box(0);
x_12 = lean_unbox(x_11);
x_13 = l_Lean_log___at___Lean_logError___at___Lean_Elab_logException___at___Lean_Elab_Tactic_closeUsingOrAdmit_spec__0_spec__2_spec__2(x_1, x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addExactSuggestion(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_9);
lean_inc(x_8);
x_17 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore(x_4, x_6, x_2, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_mk_string_unchecked("Try this: ", 10, 10);
x_22 = l_Lean_Meta_Tactic_TryThis_addSuggestion(x_1, x_20, x_3, x_21, x_5, x_12, x_13, x_14, x_15, x_19);
lean_dec(x_13);
lean_dec(x_12);
return x_22;
}
else
{
lean_dec(x_5);
if (x_7 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_dec(x_17);
x_24 = lean_ctor_get(x_18, 0);
lean_inc(x_24);
lean_dec(x_18);
x_25 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(x_24, x_12, x_13, x_14, x_15, x_23);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_17, 1);
lean_inc(x_26);
lean_dec(x_17);
x_27 = lean_ctor_get(x_18, 0);
lean_inc(x_27);
lean_dec(x_18);
x_28 = l_Lean_logInfo___at___Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0(x_27, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_26);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
return x_28;
}
}
}
else
{
uint8_t x_29; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
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
LEAN_EXPORT lean_object* l_Lean_logInfo___at___Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_logInfo___at___Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addExactSuggestion___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_17 = lean_unbox(x_4);
lean_dec(x_4);
x_18 = lean_unbox(x_7);
lean_dec(x_7);
x_19 = l_Lean_Meta_Tactic_TryThis_addExactSuggestion(x_1, x_2, x_3, x_17, x_5, x_6, x_18, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_1);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__0(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = lean_usize_dec_lt(x_4, x_3);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_5);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_array_uget(x_5, x_4);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_2);
x_18 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore(x_1, x_2, x_17, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; lean_object* x_26; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_box(0);
x_22 = lean_array_uset(x_5, x_4, x_21);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_usize_of_nat(x_23);
x_25 = lean_usize_add(x_4, x_24);
x_26 = lean_array_uset(x_22, x_4, x_19);
x_4 = x_25;
x_5 = x_26;
x_14 = x_20;
goto _start;
}
else
{
uint8_t x_28; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_28 = !lean_is_exclusive(x_18);
if (x_28 == 0)
{
return x_18;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_18, 0);
x_30 = lean_ctor_get(x_18, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_18);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__1_spec__1___redArg(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_18; 
x_18 = lean_usize_dec_lt(x_4, x_3);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_5);
lean_ctor_set(x_19, 1, x_10);
return x_19;
}
else
{
lean_object* x_20; 
x_20 = lean_array_uget(x_2, x_4);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_5, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_5, 1);
lean_inc(x_22);
lean_dec(x_5);
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_array_push(x_22, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_21);
lean_ctor_set(x_25, 1, x_24);
x_11 = x_25;
x_12 = x_10;
goto block_17;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_5, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_5, 1);
lean_inc(x_27);
lean_dec(x_5);
x_28 = lean_ctor_get(x_20, 0);
lean_inc(x_28);
lean_dec(x_20);
if (x_1 == 0)
{
lean_object* x_34; uint8_t x_35; 
lean_dec(x_27);
lean_dec(x_26);
x_34 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(x_28, x_6, x_7, x_8, x_9, x_10);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
return x_34;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_34, 0);
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_34);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
else
{
x_29 = x_26;
x_30 = x_10;
goto block_33;
}
block_33:
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_array_push(x_29, x_28);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_27);
x_11 = x_32;
x_12 = x_30;
goto block_17;
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
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__1_spec__1(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__1_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_10, x_11, x_12, x_13, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__1(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; uint8_t x_22; 
x_22 = lean_usize_dec_lt(x_4, x_3);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_5);
lean_ctor_set(x_23, 1, x_14);
return x_23;
}
else
{
lean_object* x_24; 
x_24 = lean_array_uget(x_2, x_4);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_5, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_5, 1);
lean_inc(x_26);
lean_dec(x_5);
x_27 = lean_ctor_get(x_24, 0);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_array_push(x_26, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_25);
lean_ctor_set(x_29, 1, x_28);
x_15 = x_29;
x_16 = x_14;
goto block_21;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_5, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_5, 1);
lean_inc(x_31);
lean_dec(x_5);
x_32 = lean_ctor_get(x_24, 0);
lean_inc(x_32);
lean_dec(x_24);
if (x_1 == 0)
{
lean_object* x_38; uint8_t x_39; 
lean_dec(x_31);
lean_dec(x_30);
x_38 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(x_32, x_10, x_11, x_12, x_13, x_14);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
return x_38;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_38, 0);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_38);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
else
{
x_33 = x_30;
x_34 = x_14;
goto block_37;
}
block_37:
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_array_push(x_33, x_32);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_31);
x_15 = x_36;
x_16 = x_34;
goto block_21;
}
}
}
block_21:
{
lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_usize_of_nat(x_17);
x_19 = lean_usize_add(x_4, x_18);
x_20 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__1_spec__1___redArg(x_1, x_2, x_3, x_19, x_15, x_10, x_11, x_12, x_13, x_16);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_3, x_2);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; 
lean_dec(x_4);
x_16 = lean_array_uget(x_1, x_3);
lean_inc(x_11);
x_17 = l_Lean_logInfo___at___Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0(x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_box(0);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_usize_of_nat(x_20);
x_22 = lean_usize_add(x_3, x_21);
x_3 = x_22;
x_4 = x_19;
x_13 = x_18;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addExactSuggestions(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
size_t x_17; lean_object* x_18; size_t x_19; lean_object* x_20; 
x_17 = lean_array_size(x_2);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_usize_of_nat(x_18);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_9);
lean_inc(x_8);
x_20 = l_Array_mapMUnsafe_map___at___Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__0(x_4, x_6, x_17, x_19, x_2, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_mk_empty_array_with_capacity(x_18);
lean_inc(x_23);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_array_size(x_21);
x_26 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__1(x_7, x_21, x_25, x_19, x_24, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_22);
lean_dec(x_21);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_mk_string_unchecked("Try these:", 10, 10);
x_32 = lean_box(0);
lean_inc(x_15);
lean_inc(x_14);
x_33 = l_Lean_Meta_Tactic_TryThis_addSuggestions(x_1, x_30, x_3, x_31, x_32, x_5, x_12, x_13, x_14, x_15, x_28);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; size_t x_36; lean_object* x_37; uint8_t x_38; 
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_box(0);
x_36 = lean_array_size(x_29);
x_37 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__3(x_29, x_36, x_19, x_35, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_34);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_29);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_37, 0);
lean_dec(x_39);
lean_ctor_set(x_37, 0, x_35);
return x_37;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_35);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
else
{
lean_dec(x_29);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
return x_33;
}
}
else
{
uint8_t x_42; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
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
else
{
uint8_t x_46; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
x_46 = !lean_is_exclusive(x_20);
if (x_46 == 0)
{
return x_20;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_20, 0);
x_48 = lean_ctor_get(x_20, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_20);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_15 = lean_unbox(x_1);
lean_dec(x_1);
x_16 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_17 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_18 = l_Array_mapMUnsafe_map___at___Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__0(x_15, x_2, x_16, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_8);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__1_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__1_spec__1___redArg(x_11, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_15 = lean_unbox(x_1);
lean_dec(x_1);
x_16 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_17 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_18 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__1_spec__1(x_15, x_2, x_16, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_15 = lean_unbox(x_1);
lean_dec(x_1);
x_16 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_17 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_18 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__1(x_15, x_2, x_16, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_15 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_16 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Tactic_TryThis_addExactSuggestions_spec__3(x_1, x_14, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addExactSuggestions___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_17 = lean_unbox(x_4);
lean_dec(x_4);
x_18 = lean_unbox(x_7);
lean_dec(x_7);
x_19 = l_Lean_Meta_Tactic_TryThis_addExactSuggestions(x_1, x_2, x_3, x_17, x_5, x_6, x_18, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_1);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addTermSuggestion(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_11 = l_Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion(x_2, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Meta_Tactic_TryThis_addSuggestion(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
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
lean_dec(x_5);
lean_dec(x_4);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addTermSuggestion___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Tactic_TryThis_addTermSuggestion(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_Tactic_TryThis_addTermSuggestions_spec__0(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_12 = l_Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion(x_11, x_4, x_5, x_6, x_7, x_8);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addTermSuggestions(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; lean_object* x_12; size_t x_13; lean_object* x_14; 
x_11 = lean_array_size(x_2);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_usize_of_nat(x_12);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_14 = l_Array_mapMUnsafe_map___at___Lean_Meta_Tactic_TryThis_addTermSuggestions_spec__0(x_11, x_13, x_2, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_box(0);
x_18 = l_Lean_Meta_Tactic_TryThis_addSuggestions(x_1, x_15, x_3, x_4, x_17, x_5, x_6, x_7, x_8, x_9, x_16);
lean_dec(x_7);
lean_dec(x_6);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_Tactic_TryThis_addTermSuggestions_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = l_Array_mapMUnsafe_map___at___Lean_Meta_Tactic_TryThis_addTermSuggestions_spec__0(x_9, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addTermSuggestions___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Tactic_TryThis_addTermSuggestions(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_26; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_26 = l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax(x_1, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
if (lean_obj_tag(x_2) == 0)
{
if (x_3 == 0)
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_107; lean_object* x_108; 
x_107 = lean_mk_string_unchecked("_", 1, 1);
x_108 = l_Lean_Name_mkStr1(x_107);
x_29 = x_108;
goto block_106;
}
else
{
lean_object* x_109; 
x_109 = lean_ctor_get(x_4, 0);
lean_inc(x_109);
lean_dec(x_4);
x_29 = x_109;
goto block_106;
}
}
else
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_110; uint8_t x_111; 
x_110 = lean_st_ref_get(x_8, x_28);
x_111 = !lean_is_exclusive(x_110);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_112 = lean_ctor_get(x_110, 0);
x_113 = lean_ctor_get(x_110, 1);
x_114 = lean_ctor_get(x_7, 5);
lean_inc(x_114);
x_115 = lean_box(0);
x_116 = lean_unbox(x_115);
x_117 = l_Lean_SourceInfo_fromRef(x_114, x_116);
lean_dec(x_114);
x_118 = lean_ctor_get(x_7, 10);
lean_inc(x_118);
x_119 = lean_ctor_get(x_112, 0);
lean_inc(x_119);
lean_dec(x_112);
x_120 = l_Lean_Environment_mainModule(x_119);
lean_dec(x_119);
x_121 = lean_mk_string_unchecked("Lean", 4, 4);
x_122 = lean_mk_string_unchecked("Parser", 6, 6);
x_123 = lean_mk_string_unchecked("Tactic", 6, 6);
x_124 = lean_mk_string_unchecked("tacticHave_", 11, 11);
lean_inc(x_123);
lean_inc(x_122);
lean_inc(x_121);
x_125 = l_Lean_Name_mkStr4(x_121, x_122, x_123, x_124);
x_126 = lean_mk_string_unchecked("have", 4, 4);
lean_inc(x_117);
lean_ctor_set_tag(x_110, 2);
lean_ctor_set(x_110, 1, x_126);
lean_ctor_set(x_110, 0, x_117);
x_127 = lean_mk_string_unchecked("Term", 4, 4);
x_128 = lean_mk_string_unchecked("haveDecl", 8, 8);
lean_inc(x_127);
lean_inc(x_122);
lean_inc(x_121);
x_129 = l_Lean_Name_mkStr4(x_121, x_122, x_127, x_128);
x_130 = lean_mk_string_unchecked("haveIdDecl", 10, 10);
lean_inc(x_127);
lean_inc(x_122);
lean_inc(x_121);
x_131 = l_Lean_Name_mkStr4(x_121, x_122, x_127, x_130);
x_132 = lean_mk_string_unchecked("haveId", 6, 6);
lean_inc(x_121);
x_133 = l_Lean_Name_mkStr4(x_121, x_122, x_127, x_132);
x_134 = lean_mk_string_unchecked("hygieneInfo", 11, 11);
x_135 = l_Lean_Name_mkStr1(x_134);
x_136 = lean_mk_string_unchecked("", 0, 0);
lean_inc(x_136);
x_137 = l_String_toSubstring_x27(x_136);
x_138 = lean_box(0);
x_139 = l_Lean_addMacroScope(x_120, x_138, x_118);
x_140 = lean_mk_string_unchecked("Meta", 4, 4);
x_141 = lean_mk_string_unchecked("TryThis", 7, 7);
lean_inc(x_123);
lean_inc(x_140);
lean_inc(x_121);
x_142 = l_Lean_Name_mkStr4(x_121, x_140, x_123, x_141);
x_143 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_143, 0, x_142);
lean_inc(x_140);
lean_inc(x_121);
x_144 = l_Lean_Name_mkStr2(x_121, x_140);
x_145 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_145, 0, x_144);
x_146 = lean_mk_string_unchecked("PrettyPrinter", 13, 13);
lean_inc(x_121);
x_147 = l_Lean_Name_mkStr2(x_121, x_146);
x_148 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_148, 0, x_147);
x_149 = lean_mk_string_unchecked("Elab", 4, 4);
lean_inc(x_123);
lean_inc(x_149);
lean_inc(x_121);
x_150 = l_Lean_Name_mkStr3(x_121, x_149, x_123);
x_151 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_151, 0, x_150);
lean_inc(x_121);
x_152 = l_Lean_Name_mkStr2(x_121, x_149);
x_153 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_153, 0, x_152);
lean_inc(x_121);
x_154 = l_Lean_Name_mkStr1(x_121);
x_155 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_155, 0, x_154);
x_156 = lean_mk_string_unchecked("Server", 6, 6);
x_157 = lean_mk_string_unchecked("RequestM", 8, 8);
lean_inc(x_156);
lean_inc(x_121);
x_158 = l_Lean_Name_mkStr3(x_121, x_156, x_157);
x_159 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_159, 0, x_158);
lean_inc(x_121);
x_160 = l_Lean_Name_mkStr2(x_121, x_156);
x_161 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_161, 0, x_160);
x_162 = l_Lean_Name_mkStr3(x_121, x_140, x_123);
x_163 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_163, 0, x_162);
x_164 = lean_box(0);
lean_inc(x_155);
x_165 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_165, 0, x_155);
lean_ctor_set(x_165, 1, x_164);
lean_inc(x_153);
x_166 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_166, 0, x_153);
lean_ctor_set(x_166, 1, x_165);
lean_inc(x_153);
x_167 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_167, 0, x_153);
lean_ctor_set(x_167, 1, x_166);
x_168 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_168, 0, x_163);
lean_ctor_set(x_168, 1, x_167);
lean_inc(x_151);
x_169 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_169, 0, x_151);
lean_ctor_set(x_169, 1, x_168);
lean_inc(x_151);
x_170 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_170, 0, x_151);
lean_ctor_set(x_170, 1, x_169);
lean_inc(x_148);
x_171 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_171, 0, x_148);
lean_ctor_set(x_171, 1, x_170);
lean_inc(x_148);
x_172 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_172, 0, x_148);
lean_ctor_set(x_172, 1, x_171);
lean_inc(x_145);
x_173 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_173, 0, x_145);
lean_ctor_set(x_173, 1, x_172);
lean_inc(x_145);
x_174 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_174, 0, x_145);
lean_ctor_set(x_174, 1, x_173);
lean_inc(x_161);
x_175 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_175, 0, x_161);
lean_ctor_set(x_175, 1, x_174);
x_176 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_176, 0, x_161);
lean_ctor_set(x_176, 1, x_175);
lean_inc(x_159);
x_177 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_177, 0, x_159);
lean_ctor_set(x_177, 1, x_176);
x_178 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_178, 0, x_159);
lean_ctor_set(x_178, 1, x_177);
x_179 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_179, 0, x_155);
lean_ctor_set(x_179, 1, x_178);
lean_inc(x_153);
x_180 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_180, 0, x_153);
lean_ctor_set(x_180, 1, x_179);
lean_inc(x_153);
x_181 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_181, 0, x_153);
lean_ctor_set(x_181, 1, x_180);
x_182 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_182, 0, x_153);
lean_ctor_set(x_182, 1, x_181);
lean_inc(x_151);
x_183 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_183, 0, x_151);
lean_ctor_set(x_183, 1, x_182);
lean_inc(x_151);
x_184 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_184, 0, x_151);
lean_ctor_set(x_184, 1, x_183);
x_185 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_185, 0, x_151);
lean_ctor_set(x_185, 1, x_184);
lean_inc(x_148);
x_186 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_186, 0, x_148);
lean_ctor_set(x_186, 1, x_185);
lean_inc(x_148);
x_187 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_187, 0, x_148);
lean_ctor_set(x_187, 1, x_186);
x_188 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_188, 0, x_148);
lean_ctor_set(x_188, 1, x_187);
lean_inc(x_145);
x_189 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_189, 0, x_145);
lean_ctor_set(x_189, 1, x_188);
lean_inc(x_145);
x_190 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_190, 0, x_145);
lean_ctor_set(x_190, 1, x_189);
x_191 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_191, 0, x_145);
lean_ctor_set(x_191, 1, x_190);
x_192 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_192, 0, x_143);
lean_ctor_set(x_192, 1, x_191);
lean_inc(x_117);
x_193 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_193, 0, x_117);
lean_ctor_set(x_193, 1, x_137);
lean_ctor_set(x_193, 2, x_139);
lean_ctor_set(x_193, 3, x_192);
lean_inc(x_117);
x_194 = l_Lean_Syntax_node1(x_117, x_135, x_193);
lean_inc(x_117);
x_195 = l_Lean_Syntax_node1(x_117, x_133, x_194);
x_196 = lean_mk_string_unchecked("null", 4, 4);
x_197 = l_Lean_Name_mkStr1(x_196);
x_198 = l_Array_mkArray0(lean_box(0));
lean_inc(x_117);
x_199 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_199, 0, x_117);
lean_ctor_set(x_199, 1, x_197);
lean_ctor_set(x_199, 2, x_198);
x_200 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_117);
x_201 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_201, 0, x_117);
lean_ctor_set(x_201, 1, x_200);
lean_inc(x_199);
lean_inc(x_117);
x_202 = l_Lean_Syntax_node5(x_117, x_131, x_195, x_199, x_199, x_201, x_27);
lean_inc(x_117);
x_203 = l_Lean_Syntax_node1(x_117, x_129, x_202);
x_204 = l_Lean_Syntax_node2(x_117, x_125, x_110, x_203);
x_205 = lean_mk_string_unchecked("have := ", 8, 8);
x_206 = l_Lean_stringToMessageData(x_205);
lean_dec(x_205);
x_207 = l_Lean_MessageData_ofExpr(x_1);
x_208 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_208, 0, x_206);
lean_ctor_set(x_208, 1, x_207);
x_209 = l_Lean_stringToMessageData(x_136);
lean_dec(x_136);
x_210 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_210, 0, x_208);
lean_ctor_set(x_210, 1, x_209);
x_10 = x_204;
x_11 = x_210;
x_12 = x_5;
x_13 = x_6;
x_14 = x_7;
x_15 = x_8;
x_16 = x_113;
goto block_25;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; uint8_t x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; 
x_211 = lean_ctor_get(x_110, 0);
x_212 = lean_ctor_get(x_110, 1);
lean_inc(x_212);
lean_inc(x_211);
lean_dec(x_110);
x_213 = lean_ctor_get(x_7, 5);
lean_inc(x_213);
x_214 = lean_box(0);
x_215 = lean_unbox(x_214);
x_216 = l_Lean_SourceInfo_fromRef(x_213, x_215);
lean_dec(x_213);
x_217 = lean_ctor_get(x_7, 10);
lean_inc(x_217);
x_218 = lean_ctor_get(x_211, 0);
lean_inc(x_218);
lean_dec(x_211);
x_219 = l_Lean_Environment_mainModule(x_218);
lean_dec(x_218);
x_220 = lean_mk_string_unchecked("Lean", 4, 4);
x_221 = lean_mk_string_unchecked("Parser", 6, 6);
x_222 = lean_mk_string_unchecked("Tactic", 6, 6);
x_223 = lean_mk_string_unchecked("tacticHave_", 11, 11);
lean_inc(x_222);
lean_inc(x_221);
lean_inc(x_220);
x_224 = l_Lean_Name_mkStr4(x_220, x_221, x_222, x_223);
x_225 = lean_mk_string_unchecked("have", 4, 4);
lean_inc(x_216);
x_226 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_226, 0, x_216);
lean_ctor_set(x_226, 1, x_225);
x_227 = lean_mk_string_unchecked("Term", 4, 4);
x_228 = lean_mk_string_unchecked("haveDecl", 8, 8);
lean_inc(x_227);
lean_inc(x_221);
lean_inc(x_220);
x_229 = l_Lean_Name_mkStr4(x_220, x_221, x_227, x_228);
x_230 = lean_mk_string_unchecked("haveIdDecl", 10, 10);
lean_inc(x_227);
lean_inc(x_221);
lean_inc(x_220);
x_231 = l_Lean_Name_mkStr4(x_220, x_221, x_227, x_230);
x_232 = lean_mk_string_unchecked("haveId", 6, 6);
lean_inc(x_220);
x_233 = l_Lean_Name_mkStr4(x_220, x_221, x_227, x_232);
x_234 = lean_mk_string_unchecked("hygieneInfo", 11, 11);
x_235 = l_Lean_Name_mkStr1(x_234);
x_236 = lean_mk_string_unchecked("", 0, 0);
lean_inc(x_236);
x_237 = l_String_toSubstring_x27(x_236);
x_238 = lean_box(0);
x_239 = l_Lean_addMacroScope(x_219, x_238, x_217);
x_240 = lean_mk_string_unchecked("Meta", 4, 4);
x_241 = lean_mk_string_unchecked("TryThis", 7, 7);
lean_inc(x_222);
lean_inc(x_240);
lean_inc(x_220);
x_242 = l_Lean_Name_mkStr4(x_220, x_240, x_222, x_241);
x_243 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_243, 0, x_242);
lean_inc(x_240);
lean_inc(x_220);
x_244 = l_Lean_Name_mkStr2(x_220, x_240);
x_245 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_245, 0, x_244);
x_246 = lean_mk_string_unchecked("PrettyPrinter", 13, 13);
lean_inc(x_220);
x_247 = l_Lean_Name_mkStr2(x_220, x_246);
x_248 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_248, 0, x_247);
x_249 = lean_mk_string_unchecked("Elab", 4, 4);
lean_inc(x_222);
lean_inc(x_249);
lean_inc(x_220);
x_250 = l_Lean_Name_mkStr3(x_220, x_249, x_222);
x_251 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_251, 0, x_250);
lean_inc(x_220);
x_252 = l_Lean_Name_mkStr2(x_220, x_249);
x_253 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_253, 0, x_252);
lean_inc(x_220);
x_254 = l_Lean_Name_mkStr1(x_220);
x_255 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_255, 0, x_254);
x_256 = lean_mk_string_unchecked("Server", 6, 6);
x_257 = lean_mk_string_unchecked("RequestM", 8, 8);
lean_inc(x_256);
lean_inc(x_220);
x_258 = l_Lean_Name_mkStr3(x_220, x_256, x_257);
x_259 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_259, 0, x_258);
lean_inc(x_220);
x_260 = l_Lean_Name_mkStr2(x_220, x_256);
x_261 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_261, 0, x_260);
x_262 = l_Lean_Name_mkStr3(x_220, x_240, x_222);
x_263 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_263, 0, x_262);
x_264 = lean_box(0);
lean_inc(x_255);
x_265 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_265, 0, x_255);
lean_ctor_set(x_265, 1, x_264);
lean_inc(x_253);
x_266 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_266, 0, x_253);
lean_ctor_set(x_266, 1, x_265);
lean_inc(x_253);
x_267 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_267, 0, x_253);
lean_ctor_set(x_267, 1, x_266);
x_268 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_268, 0, x_263);
lean_ctor_set(x_268, 1, x_267);
lean_inc(x_251);
x_269 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_269, 0, x_251);
lean_ctor_set(x_269, 1, x_268);
lean_inc(x_251);
x_270 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_270, 0, x_251);
lean_ctor_set(x_270, 1, x_269);
lean_inc(x_248);
x_271 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_271, 0, x_248);
lean_ctor_set(x_271, 1, x_270);
lean_inc(x_248);
x_272 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_272, 0, x_248);
lean_ctor_set(x_272, 1, x_271);
lean_inc(x_245);
x_273 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_273, 0, x_245);
lean_ctor_set(x_273, 1, x_272);
lean_inc(x_245);
x_274 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_274, 0, x_245);
lean_ctor_set(x_274, 1, x_273);
lean_inc(x_261);
x_275 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_275, 0, x_261);
lean_ctor_set(x_275, 1, x_274);
x_276 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_276, 0, x_261);
lean_ctor_set(x_276, 1, x_275);
lean_inc(x_259);
x_277 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_277, 0, x_259);
lean_ctor_set(x_277, 1, x_276);
x_278 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_278, 0, x_259);
lean_ctor_set(x_278, 1, x_277);
x_279 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_279, 0, x_255);
lean_ctor_set(x_279, 1, x_278);
lean_inc(x_253);
x_280 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_280, 0, x_253);
lean_ctor_set(x_280, 1, x_279);
lean_inc(x_253);
x_281 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_281, 0, x_253);
lean_ctor_set(x_281, 1, x_280);
x_282 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_282, 0, x_253);
lean_ctor_set(x_282, 1, x_281);
lean_inc(x_251);
x_283 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_283, 0, x_251);
lean_ctor_set(x_283, 1, x_282);
lean_inc(x_251);
x_284 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_284, 0, x_251);
lean_ctor_set(x_284, 1, x_283);
x_285 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_285, 0, x_251);
lean_ctor_set(x_285, 1, x_284);
lean_inc(x_248);
x_286 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_286, 0, x_248);
lean_ctor_set(x_286, 1, x_285);
lean_inc(x_248);
x_287 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_287, 0, x_248);
lean_ctor_set(x_287, 1, x_286);
x_288 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_288, 0, x_248);
lean_ctor_set(x_288, 1, x_287);
lean_inc(x_245);
x_289 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_289, 0, x_245);
lean_ctor_set(x_289, 1, x_288);
lean_inc(x_245);
x_290 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_290, 0, x_245);
lean_ctor_set(x_290, 1, x_289);
x_291 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_291, 0, x_245);
lean_ctor_set(x_291, 1, x_290);
x_292 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_292, 0, x_243);
lean_ctor_set(x_292, 1, x_291);
lean_inc(x_216);
x_293 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_293, 0, x_216);
lean_ctor_set(x_293, 1, x_237);
lean_ctor_set(x_293, 2, x_239);
lean_ctor_set(x_293, 3, x_292);
lean_inc(x_216);
x_294 = l_Lean_Syntax_node1(x_216, x_235, x_293);
lean_inc(x_216);
x_295 = l_Lean_Syntax_node1(x_216, x_233, x_294);
x_296 = lean_mk_string_unchecked("null", 4, 4);
x_297 = l_Lean_Name_mkStr1(x_296);
x_298 = l_Array_mkArray0(lean_box(0));
lean_inc(x_216);
x_299 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_299, 0, x_216);
lean_ctor_set(x_299, 1, x_297);
lean_ctor_set(x_299, 2, x_298);
x_300 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_216);
x_301 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_301, 0, x_216);
lean_ctor_set(x_301, 1, x_300);
lean_inc(x_299);
lean_inc(x_216);
x_302 = l_Lean_Syntax_node5(x_216, x_231, x_295, x_299, x_299, x_301, x_27);
lean_inc(x_216);
x_303 = l_Lean_Syntax_node1(x_216, x_229, x_302);
x_304 = l_Lean_Syntax_node2(x_216, x_224, x_226, x_303);
x_305 = lean_mk_string_unchecked("have := ", 8, 8);
x_306 = l_Lean_stringToMessageData(x_305);
lean_dec(x_305);
x_307 = l_Lean_MessageData_ofExpr(x_1);
x_308 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_308, 0, x_306);
lean_ctor_set(x_308, 1, x_307);
x_309 = l_Lean_stringToMessageData(x_236);
lean_dec(x_236);
x_310 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_310, 0, x_308);
lean_ctor_set(x_310, 1, x_309);
x_10 = x_304;
x_11 = x_310;
x_12 = x_5;
x_13 = x_6;
x_14 = x_7;
x_15 = x_8;
x_16 = x_212;
goto block_25;
}
}
else
{
lean_object* x_311; lean_object* x_312; uint8_t x_313; 
x_311 = lean_ctor_get(x_4, 0);
lean_inc(x_311);
lean_dec(x_4);
x_312 = lean_st_ref_get(x_8, x_28);
x_313 = !lean_is_exclusive(x_312);
if (x_313 == 0)
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; uint8_t x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; 
x_314 = lean_ctor_get(x_312, 1);
x_315 = lean_ctor_get(x_312, 0);
lean_dec(x_315);
x_316 = lean_ctor_get(x_7, 5);
lean_inc(x_316);
x_317 = lean_box(0);
x_318 = lean_unbox(x_317);
x_319 = l_Lean_SourceInfo_fromRef(x_316, x_318);
lean_dec(x_316);
x_320 = lean_mk_string_unchecked("Lean", 4, 4);
x_321 = lean_mk_string_unchecked("Parser", 6, 6);
x_322 = lean_mk_string_unchecked("Tactic", 6, 6);
x_323 = lean_mk_string_unchecked("tacticHave_", 11, 11);
lean_inc(x_321);
lean_inc(x_320);
x_324 = l_Lean_Name_mkStr4(x_320, x_321, x_322, x_323);
x_325 = lean_mk_string_unchecked("have", 4, 4);
lean_inc(x_319);
lean_ctor_set_tag(x_312, 2);
lean_ctor_set(x_312, 1, x_325);
lean_ctor_set(x_312, 0, x_319);
x_326 = lean_mk_string_unchecked("Term", 4, 4);
x_327 = lean_mk_string_unchecked("haveDecl", 8, 8);
lean_inc(x_326);
lean_inc(x_321);
lean_inc(x_320);
x_328 = l_Lean_Name_mkStr4(x_320, x_321, x_326, x_327);
x_329 = lean_mk_string_unchecked("haveIdDecl", 10, 10);
lean_inc(x_326);
lean_inc(x_321);
lean_inc(x_320);
x_330 = l_Lean_Name_mkStr4(x_320, x_321, x_326, x_329);
x_331 = lean_mk_string_unchecked("haveId", 6, 6);
x_332 = l_Lean_Name_mkStr4(x_320, x_321, x_326, x_331);
lean_inc(x_311);
x_333 = lean_mk_syntax_ident(x_311);
lean_inc(x_319);
x_334 = l_Lean_Syntax_node1(x_319, x_332, x_333);
x_335 = lean_mk_string_unchecked("null", 4, 4);
x_336 = l_Lean_Name_mkStr1(x_335);
x_337 = l_Array_mkArray0(lean_box(0));
lean_inc(x_319);
x_338 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_338, 0, x_319);
lean_ctor_set(x_338, 1, x_336);
lean_ctor_set(x_338, 2, x_337);
x_339 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_319);
x_340 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_340, 0, x_319);
lean_ctor_set(x_340, 1, x_339);
lean_inc(x_338);
lean_inc(x_319);
x_341 = l_Lean_Syntax_node5(x_319, x_330, x_334, x_338, x_338, x_340, x_27);
lean_inc(x_319);
x_342 = l_Lean_Syntax_node1(x_319, x_328, x_341);
x_343 = l_Lean_Syntax_node2(x_319, x_324, x_312, x_342);
x_344 = lean_mk_string_unchecked("have ", 5, 5);
x_345 = l_Lean_stringToMessageData(x_344);
lean_dec(x_344);
x_346 = l_Lean_MessageData_ofName(x_311);
x_347 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_347, 0, x_345);
lean_ctor_set(x_347, 1, x_346);
x_348 = lean_mk_string_unchecked(" := ", 4, 4);
x_349 = l_Lean_stringToMessageData(x_348);
lean_dec(x_348);
x_350 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_350, 0, x_347);
lean_ctor_set(x_350, 1, x_349);
x_351 = l_Lean_MessageData_ofExpr(x_1);
x_352 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_352, 0, x_350);
lean_ctor_set(x_352, 1, x_351);
x_353 = lean_mk_string_unchecked("", 0, 0);
x_354 = l_Lean_stringToMessageData(x_353);
lean_dec(x_353);
x_355 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_355, 0, x_352);
lean_ctor_set(x_355, 1, x_354);
x_10 = x_343;
x_11 = x_355;
x_12 = x_5;
x_13 = x_6;
x_14 = x_7;
x_15 = x_8;
x_16 = x_314;
goto block_25;
}
else
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; uint8_t x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; 
x_356 = lean_ctor_get(x_312, 1);
lean_inc(x_356);
lean_dec(x_312);
x_357 = lean_ctor_get(x_7, 5);
lean_inc(x_357);
x_358 = lean_box(0);
x_359 = lean_unbox(x_358);
x_360 = l_Lean_SourceInfo_fromRef(x_357, x_359);
lean_dec(x_357);
x_361 = lean_mk_string_unchecked("Lean", 4, 4);
x_362 = lean_mk_string_unchecked("Parser", 6, 6);
x_363 = lean_mk_string_unchecked("Tactic", 6, 6);
x_364 = lean_mk_string_unchecked("tacticHave_", 11, 11);
lean_inc(x_362);
lean_inc(x_361);
x_365 = l_Lean_Name_mkStr4(x_361, x_362, x_363, x_364);
x_366 = lean_mk_string_unchecked("have", 4, 4);
lean_inc(x_360);
x_367 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_367, 0, x_360);
lean_ctor_set(x_367, 1, x_366);
x_368 = lean_mk_string_unchecked("Term", 4, 4);
x_369 = lean_mk_string_unchecked("haveDecl", 8, 8);
lean_inc(x_368);
lean_inc(x_362);
lean_inc(x_361);
x_370 = l_Lean_Name_mkStr4(x_361, x_362, x_368, x_369);
x_371 = lean_mk_string_unchecked("haveIdDecl", 10, 10);
lean_inc(x_368);
lean_inc(x_362);
lean_inc(x_361);
x_372 = l_Lean_Name_mkStr4(x_361, x_362, x_368, x_371);
x_373 = lean_mk_string_unchecked("haveId", 6, 6);
x_374 = l_Lean_Name_mkStr4(x_361, x_362, x_368, x_373);
lean_inc(x_311);
x_375 = lean_mk_syntax_ident(x_311);
lean_inc(x_360);
x_376 = l_Lean_Syntax_node1(x_360, x_374, x_375);
x_377 = lean_mk_string_unchecked("null", 4, 4);
x_378 = l_Lean_Name_mkStr1(x_377);
x_379 = l_Array_mkArray0(lean_box(0));
lean_inc(x_360);
x_380 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_380, 0, x_360);
lean_ctor_set(x_380, 1, x_378);
lean_ctor_set(x_380, 2, x_379);
x_381 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_360);
x_382 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_382, 0, x_360);
lean_ctor_set(x_382, 1, x_381);
lean_inc(x_380);
lean_inc(x_360);
x_383 = l_Lean_Syntax_node5(x_360, x_372, x_376, x_380, x_380, x_382, x_27);
lean_inc(x_360);
x_384 = l_Lean_Syntax_node1(x_360, x_370, x_383);
x_385 = l_Lean_Syntax_node2(x_360, x_365, x_367, x_384);
x_386 = lean_mk_string_unchecked("have ", 5, 5);
x_387 = l_Lean_stringToMessageData(x_386);
lean_dec(x_386);
x_388 = l_Lean_MessageData_ofName(x_311);
x_389 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_389, 0, x_387);
lean_ctor_set(x_389, 1, x_388);
x_390 = lean_mk_string_unchecked(" := ", 4, 4);
x_391 = l_Lean_stringToMessageData(x_390);
lean_dec(x_390);
x_392 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_392, 0, x_389);
lean_ctor_set(x_392, 1, x_391);
x_393 = l_Lean_MessageData_ofExpr(x_1);
x_394 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_394, 0, x_392);
lean_ctor_set(x_394, 1, x_393);
x_395 = lean_mk_string_unchecked("", 0, 0);
x_396 = l_Lean_stringToMessageData(x_395);
lean_dec(x_395);
x_397 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_397, 0, x_394);
lean_ctor_set(x_397, 1, x_396);
x_10 = x_385;
x_11 = x_397;
x_12 = x_5;
x_13 = x_6;
x_14 = x_7;
x_15 = x_8;
x_16 = x_356;
goto block_25;
}
}
}
}
else
{
uint8_t x_398; 
x_398 = !lean_is_exclusive(x_2);
if (x_398 == 0)
{
lean_object* x_399; lean_object* x_400; 
x_399 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_399);
x_400 = l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax(x_399, x_5, x_6, x_7, x_8, x_28);
if (lean_obj_tag(x_400) == 0)
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; 
x_401 = lean_ctor_get(x_400, 0);
lean_inc(x_401);
x_402 = lean_ctor_get(x_400, 1);
lean_inc(x_402);
lean_dec(x_400);
if (x_3 == 0)
{
lean_free_object(x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_503; lean_object* x_504; 
x_503 = lean_mk_string_unchecked("_", 1, 1);
x_504 = l_Lean_Name_mkStr1(x_503);
x_403 = x_504;
goto block_502;
}
else
{
lean_object* x_505; 
x_505 = lean_ctor_get(x_4, 0);
lean_inc(x_505);
lean_dec(x_4);
x_403 = x_505;
goto block_502;
}
}
else
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_506; uint8_t x_507; 
x_506 = lean_st_ref_get(x_8, x_402);
x_507 = !lean_is_exclusive(x_506);
if (x_507 == 0)
{
lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; uint8_t x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; 
x_508 = lean_ctor_get(x_506, 0);
x_509 = lean_ctor_get(x_506, 1);
x_510 = lean_ctor_get(x_7, 5);
lean_inc(x_510);
x_511 = lean_box(0);
x_512 = lean_unbox(x_511);
x_513 = l_Lean_SourceInfo_fromRef(x_510, x_512);
lean_dec(x_510);
x_514 = lean_ctor_get(x_7, 10);
lean_inc(x_514);
x_515 = lean_ctor_get(x_508, 0);
lean_inc(x_515);
lean_dec(x_508);
x_516 = l_Lean_Environment_mainModule(x_515);
lean_dec(x_515);
x_517 = lean_mk_string_unchecked("Lean", 4, 4);
x_518 = lean_mk_string_unchecked("Parser", 6, 6);
x_519 = lean_mk_string_unchecked("Tactic", 6, 6);
x_520 = lean_mk_string_unchecked("tacticHave_", 11, 11);
lean_inc(x_519);
lean_inc(x_518);
lean_inc(x_517);
x_521 = l_Lean_Name_mkStr4(x_517, x_518, x_519, x_520);
x_522 = lean_mk_string_unchecked("have", 4, 4);
lean_inc(x_513);
lean_ctor_set_tag(x_506, 2);
lean_ctor_set(x_506, 1, x_522);
lean_ctor_set(x_506, 0, x_513);
x_523 = lean_mk_string_unchecked("Term", 4, 4);
x_524 = lean_mk_string_unchecked("haveDecl", 8, 8);
lean_inc(x_523);
lean_inc(x_518);
lean_inc(x_517);
x_525 = l_Lean_Name_mkStr4(x_517, x_518, x_523, x_524);
x_526 = lean_mk_string_unchecked("haveIdDecl", 10, 10);
lean_inc(x_523);
lean_inc(x_518);
lean_inc(x_517);
x_527 = l_Lean_Name_mkStr4(x_517, x_518, x_523, x_526);
x_528 = lean_mk_string_unchecked("haveId", 6, 6);
lean_inc(x_523);
lean_inc(x_518);
lean_inc(x_517);
x_529 = l_Lean_Name_mkStr4(x_517, x_518, x_523, x_528);
x_530 = lean_mk_string_unchecked("hygieneInfo", 11, 11);
x_531 = l_Lean_Name_mkStr1(x_530);
x_532 = lean_mk_string_unchecked("", 0, 0);
lean_inc(x_532);
x_533 = l_String_toSubstring_x27(x_532);
x_534 = lean_box(0);
x_535 = l_Lean_addMacroScope(x_516, x_534, x_514);
x_536 = lean_mk_string_unchecked("Meta", 4, 4);
x_537 = lean_mk_string_unchecked("TryThis", 7, 7);
lean_inc(x_519);
lean_inc(x_536);
lean_inc(x_517);
x_538 = l_Lean_Name_mkStr4(x_517, x_536, x_519, x_537);
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 0, x_538);
lean_inc(x_536);
lean_inc(x_517);
x_539 = l_Lean_Name_mkStr2(x_517, x_536);
x_540 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_540, 0, x_539);
x_541 = lean_mk_string_unchecked("PrettyPrinter", 13, 13);
lean_inc(x_517);
x_542 = l_Lean_Name_mkStr2(x_517, x_541);
x_543 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_543, 0, x_542);
x_544 = lean_mk_string_unchecked("Elab", 4, 4);
lean_inc(x_519);
lean_inc(x_544);
lean_inc(x_517);
x_545 = l_Lean_Name_mkStr3(x_517, x_544, x_519);
x_546 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_546, 0, x_545);
lean_inc(x_517);
x_547 = l_Lean_Name_mkStr2(x_517, x_544);
x_548 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_548, 0, x_547);
lean_inc(x_517);
x_549 = l_Lean_Name_mkStr1(x_517);
x_550 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_550, 0, x_549);
x_551 = lean_mk_string_unchecked("Server", 6, 6);
x_552 = lean_mk_string_unchecked("RequestM", 8, 8);
lean_inc(x_551);
lean_inc(x_517);
x_553 = l_Lean_Name_mkStr3(x_517, x_551, x_552);
x_554 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_554, 0, x_553);
lean_inc(x_517);
x_555 = l_Lean_Name_mkStr2(x_517, x_551);
x_556 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_556, 0, x_555);
lean_inc(x_517);
x_557 = l_Lean_Name_mkStr3(x_517, x_536, x_519);
x_558 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_558, 0, x_557);
x_559 = lean_box(0);
lean_inc(x_550);
x_560 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_560, 0, x_550);
lean_ctor_set(x_560, 1, x_559);
lean_inc(x_548);
x_561 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_561, 0, x_548);
lean_ctor_set(x_561, 1, x_560);
lean_inc(x_548);
x_562 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_562, 0, x_548);
lean_ctor_set(x_562, 1, x_561);
x_563 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_563, 0, x_558);
lean_ctor_set(x_563, 1, x_562);
lean_inc(x_546);
x_564 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_564, 0, x_546);
lean_ctor_set(x_564, 1, x_563);
lean_inc(x_546);
x_565 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_565, 0, x_546);
lean_ctor_set(x_565, 1, x_564);
lean_inc(x_543);
x_566 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_566, 0, x_543);
lean_ctor_set(x_566, 1, x_565);
lean_inc(x_543);
x_567 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_567, 0, x_543);
lean_ctor_set(x_567, 1, x_566);
lean_inc(x_540);
x_568 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_568, 0, x_540);
lean_ctor_set(x_568, 1, x_567);
lean_inc(x_540);
x_569 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_569, 0, x_540);
lean_ctor_set(x_569, 1, x_568);
lean_inc(x_556);
x_570 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_570, 0, x_556);
lean_ctor_set(x_570, 1, x_569);
x_571 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_571, 0, x_556);
lean_ctor_set(x_571, 1, x_570);
lean_inc(x_554);
x_572 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_572, 0, x_554);
lean_ctor_set(x_572, 1, x_571);
x_573 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_573, 0, x_554);
lean_ctor_set(x_573, 1, x_572);
x_574 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_574, 0, x_550);
lean_ctor_set(x_574, 1, x_573);
lean_inc(x_548);
x_575 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_575, 0, x_548);
lean_ctor_set(x_575, 1, x_574);
lean_inc(x_548);
x_576 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_576, 0, x_548);
lean_ctor_set(x_576, 1, x_575);
x_577 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_577, 0, x_548);
lean_ctor_set(x_577, 1, x_576);
lean_inc(x_546);
x_578 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_578, 0, x_546);
lean_ctor_set(x_578, 1, x_577);
lean_inc(x_546);
x_579 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_579, 0, x_546);
lean_ctor_set(x_579, 1, x_578);
x_580 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_580, 0, x_546);
lean_ctor_set(x_580, 1, x_579);
lean_inc(x_543);
x_581 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_581, 0, x_543);
lean_ctor_set(x_581, 1, x_580);
lean_inc(x_543);
x_582 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_582, 0, x_543);
lean_ctor_set(x_582, 1, x_581);
x_583 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_583, 0, x_543);
lean_ctor_set(x_583, 1, x_582);
lean_inc(x_540);
x_584 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_584, 0, x_540);
lean_ctor_set(x_584, 1, x_583);
lean_inc(x_540);
x_585 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_585, 0, x_540);
lean_ctor_set(x_585, 1, x_584);
x_586 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_586, 0, x_540);
lean_ctor_set(x_586, 1, x_585);
x_587 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_587, 0, x_2);
lean_ctor_set(x_587, 1, x_586);
lean_inc(x_513);
x_588 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_588, 0, x_513);
lean_ctor_set(x_588, 1, x_533);
lean_ctor_set(x_588, 2, x_535);
lean_ctor_set(x_588, 3, x_587);
lean_inc(x_513);
x_589 = l_Lean_Syntax_node1(x_513, x_531, x_588);
lean_inc(x_513);
x_590 = l_Lean_Syntax_node1(x_513, x_529, x_589);
x_591 = lean_mk_string_unchecked("null", 4, 4);
x_592 = l_Lean_Name_mkStr1(x_591);
x_593 = l_Array_mkArray0(lean_box(0));
lean_inc(x_592);
lean_inc(x_513);
x_594 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_594, 0, x_513);
lean_ctor_set(x_594, 1, x_592);
lean_ctor_set(x_594, 2, x_593);
x_595 = lean_mk_string_unchecked("typeSpec", 8, 8);
x_596 = l_Lean_Name_mkStr4(x_517, x_518, x_523, x_595);
x_597 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_513);
x_598 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_598, 0, x_513);
lean_ctor_set(x_598, 1, x_597);
lean_inc(x_513);
x_599 = l_Lean_Syntax_node2(x_513, x_596, x_598, x_401);
lean_inc(x_513);
x_600 = l_Lean_Syntax_node1(x_513, x_592, x_599);
x_601 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_513);
x_602 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_602, 0, x_513);
lean_ctor_set(x_602, 1, x_601);
lean_inc(x_513);
x_603 = l_Lean_Syntax_node5(x_513, x_527, x_590, x_594, x_600, x_602, x_27);
lean_inc(x_513);
x_604 = l_Lean_Syntax_node1(x_513, x_525, x_603);
x_605 = l_Lean_Syntax_node2(x_513, x_521, x_506, x_604);
x_606 = lean_mk_string_unchecked("have : ", 7, 7);
x_607 = l_Lean_stringToMessageData(x_606);
lean_dec(x_606);
x_608 = l_Lean_MessageData_ofExpr(x_399);
x_609 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_609, 0, x_607);
lean_ctor_set(x_609, 1, x_608);
x_610 = lean_mk_string_unchecked(" := ", 4, 4);
x_611 = l_Lean_stringToMessageData(x_610);
lean_dec(x_610);
x_612 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_612, 0, x_609);
lean_ctor_set(x_612, 1, x_611);
x_613 = l_Lean_MessageData_ofExpr(x_1);
x_614 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_614, 0, x_612);
lean_ctor_set(x_614, 1, x_613);
x_615 = l_Lean_stringToMessageData(x_532);
lean_dec(x_532);
x_616 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_616, 0, x_614);
lean_ctor_set(x_616, 1, x_615);
x_10 = x_605;
x_11 = x_616;
x_12 = x_5;
x_13 = x_6;
x_14 = x_7;
x_15 = x_8;
x_16 = x_509;
goto block_25;
}
else
{
lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; uint8_t x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; 
x_617 = lean_ctor_get(x_506, 0);
x_618 = lean_ctor_get(x_506, 1);
lean_inc(x_618);
lean_inc(x_617);
lean_dec(x_506);
x_619 = lean_ctor_get(x_7, 5);
lean_inc(x_619);
x_620 = lean_box(0);
x_621 = lean_unbox(x_620);
x_622 = l_Lean_SourceInfo_fromRef(x_619, x_621);
lean_dec(x_619);
x_623 = lean_ctor_get(x_7, 10);
lean_inc(x_623);
x_624 = lean_ctor_get(x_617, 0);
lean_inc(x_624);
lean_dec(x_617);
x_625 = l_Lean_Environment_mainModule(x_624);
lean_dec(x_624);
x_626 = lean_mk_string_unchecked("Lean", 4, 4);
x_627 = lean_mk_string_unchecked("Parser", 6, 6);
x_628 = lean_mk_string_unchecked("Tactic", 6, 6);
x_629 = lean_mk_string_unchecked("tacticHave_", 11, 11);
lean_inc(x_628);
lean_inc(x_627);
lean_inc(x_626);
x_630 = l_Lean_Name_mkStr4(x_626, x_627, x_628, x_629);
x_631 = lean_mk_string_unchecked("have", 4, 4);
lean_inc(x_622);
x_632 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_632, 0, x_622);
lean_ctor_set(x_632, 1, x_631);
x_633 = lean_mk_string_unchecked("Term", 4, 4);
x_634 = lean_mk_string_unchecked("haveDecl", 8, 8);
lean_inc(x_633);
lean_inc(x_627);
lean_inc(x_626);
x_635 = l_Lean_Name_mkStr4(x_626, x_627, x_633, x_634);
x_636 = lean_mk_string_unchecked("haveIdDecl", 10, 10);
lean_inc(x_633);
lean_inc(x_627);
lean_inc(x_626);
x_637 = l_Lean_Name_mkStr4(x_626, x_627, x_633, x_636);
x_638 = lean_mk_string_unchecked("haveId", 6, 6);
lean_inc(x_633);
lean_inc(x_627);
lean_inc(x_626);
x_639 = l_Lean_Name_mkStr4(x_626, x_627, x_633, x_638);
x_640 = lean_mk_string_unchecked("hygieneInfo", 11, 11);
x_641 = l_Lean_Name_mkStr1(x_640);
x_642 = lean_mk_string_unchecked("", 0, 0);
lean_inc(x_642);
x_643 = l_String_toSubstring_x27(x_642);
x_644 = lean_box(0);
x_645 = l_Lean_addMacroScope(x_625, x_644, x_623);
x_646 = lean_mk_string_unchecked("Meta", 4, 4);
x_647 = lean_mk_string_unchecked("TryThis", 7, 7);
lean_inc(x_628);
lean_inc(x_646);
lean_inc(x_626);
x_648 = l_Lean_Name_mkStr4(x_626, x_646, x_628, x_647);
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 0, x_648);
lean_inc(x_646);
lean_inc(x_626);
x_649 = l_Lean_Name_mkStr2(x_626, x_646);
x_650 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_650, 0, x_649);
x_651 = lean_mk_string_unchecked("PrettyPrinter", 13, 13);
lean_inc(x_626);
x_652 = l_Lean_Name_mkStr2(x_626, x_651);
x_653 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_653, 0, x_652);
x_654 = lean_mk_string_unchecked("Elab", 4, 4);
lean_inc(x_628);
lean_inc(x_654);
lean_inc(x_626);
x_655 = l_Lean_Name_mkStr3(x_626, x_654, x_628);
x_656 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_656, 0, x_655);
lean_inc(x_626);
x_657 = l_Lean_Name_mkStr2(x_626, x_654);
x_658 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_658, 0, x_657);
lean_inc(x_626);
x_659 = l_Lean_Name_mkStr1(x_626);
x_660 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_660, 0, x_659);
x_661 = lean_mk_string_unchecked("Server", 6, 6);
x_662 = lean_mk_string_unchecked("RequestM", 8, 8);
lean_inc(x_661);
lean_inc(x_626);
x_663 = l_Lean_Name_mkStr3(x_626, x_661, x_662);
x_664 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_664, 0, x_663);
lean_inc(x_626);
x_665 = l_Lean_Name_mkStr2(x_626, x_661);
x_666 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_666, 0, x_665);
lean_inc(x_626);
x_667 = l_Lean_Name_mkStr3(x_626, x_646, x_628);
x_668 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_668, 0, x_667);
x_669 = lean_box(0);
lean_inc(x_660);
x_670 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_670, 0, x_660);
lean_ctor_set(x_670, 1, x_669);
lean_inc(x_658);
x_671 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_671, 0, x_658);
lean_ctor_set(x_671, 1, x_670);
lean_inc(x_658);
x_672 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_672, 0, x_658);
lean_ctor_set(x_672, 1, x_671);
x_673 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_673, 0, x_668);
lean_ctor_set(x_673, 1, x_672);
lean_inc(x_656);
x_674 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_674, 0, x_656);
lean_ctor_set(x_674, 1, x_673);
lean_inc(x_656);
x_675 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_675, 0, x_656);
lean_ctor_set(x_675, 1, x_674);
lean_inc(x_653);
x_676 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_676, 0, x_653);
lean_ctor_set(x_676, 1, x_675);
lean_inc(x_653);
x_677 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_677, 0, x_653);
lean_ctor_set(x_677, 1, x_676);
lean_inc(x_650);
x_678 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_678, 0, x_650);
lean_ctor_set(x_678, 1, x_677);
lean_inc(x_650);
x_679 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_679, 0, x_650);
lean_ctor_set(x_679, 1, x_678);
lean_inc(x_666);
x_680 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_680, 0, x_666);
lean_ctor_set(x_680, 1, x_679);
x_681 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_681, 0, x_666);
lean_ctor_set(x_681, 1, x_680);
lean_inc(x_664);
x_682 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_682, 0, x_664);
lean_ctor_set(x_682, 1, x_681);
x_683 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_683, 0, x_664);
lean_ctor_set(x_683, 1, x_682);
x_684 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_684, 0, x_660);
lean_ctor_set(x_684, 1, x_683);
lean_inc(x_658);
x_685 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_685, 0, x_658);
lean_ctor_set(x_685, 1, x_684);
lean_inc(x_658);
x_686 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_686, 0, x_658);
lean_ctor_set(x_686, 1, x_685);
x_687 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_687, 0, x_658);
lean_ctor_set(x_687, 1, x_686);
lean_inc(x_656);
x_688 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_688, 0, x_656);
lean_ctor_set(x_688, 1, x_687);
lean_inc(x_656);
x_689 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_689, 0, x_656);
lean_ctor_set(x_689, 1, x_688);
x_690 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_690, 0, x_656);
lean_ctor_set(x_690, 1, x_689);
lean_inc(x_653);
x_691 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_691, 0, x_653);
lean_ctor_set(x_691, 1, x_690);
lean_inc(x_653);
x_692 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_692, 0, x_653);
lean_ctor_set(x_692, 1, x_691);
x_693 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_693, 0, x_653);
lean_ctor_set(x_693, 1, x_692);
lean_inc(x_650);
x_694 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_694, 0, x_650);
lean_ctor_set(x_694, 1, x_693);
lean_inc(x_650);
x_695 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_695, 0, x_650);
lean_ctor_set(x_695, 1, x_694);
x_696 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_696, 0, x_650);
lean_ctor_set(x_696, 1, x_695);
x_697 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_697, 0, x_2);
lean_ctor_set(x_697, 1, x_696);
lean_inc(x_622);
x_698 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_698, 0, x_622);
lean_ctor_set(x_698, 1, x_643);
lean_ctor_set(x_698, 2, x_645);
lean_ctor_set(x_698, 3, x_697);
lean_inc(x_622);
x_699 = l_Lean_Syntax_node1(x_622, x_641, x_698);
lean_inc(x_622);
x_700 = l_Lean_Syntax_node1(x_622, x_639, x_699);
x_701 = lean_mk_string_unchecked("null", 4, 4);
x_702 = l_Lean_Name_mkStr1(x_701);
x_703 = l_Array_mkArray0(lean_box(0));
lean_inc(x_702);
lean_inc(x_622);
x_704 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_704, 0, x_622);
lean_ctor_set(x_704, 1, x_702);
lean_ctor_set(x_704, 2, x_703);
x_705 = lean_mk_string_unchecked("typeSpec", 8, 8);
x_706 = l_Lean_Name_mkStr4(x_626, x_627, x_633, x_705);
x_707 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_622);
x_708 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_708, 0, x_622);
lean_ctor_set(x_708, 1, x_707);
lean_inc(x_622);
x_709 = l_Lean_Syntax_node2(x_622, x_706, x_708, x_401);
lean_inc(x_622);
x_710 = l_Lean_Syntax_node1(x_622, x_702, x_709);
x_711 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_622);
x_712 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_712, 0, x_622);
lean_ctor_set(x_712, 1, x_711);
lean_inc(x_622);
x_713 = l_Lean_Syntax_node5(x_622, x_637, x_700, x_704, x_710, x_712, x_27);
lean_inc(x_622);
x_714 = l_Lean_Syntax_node1(x_622, x_635, x_713);
x_715 = l_Lean_Syntax_node2(x_622, x_630, x_632, x_714);
x_716 = lean_mk_string_unchecked("have : ", 7, 7);
x_717 = l_Lean_stringToMessageData(x_716);
lean_dec(x_716);
x_718 = l_Lean_MessageData_ofExpr(x_399);
x_719 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_719, 0, x_717);
lean_ctor_set(x_719, 1, x_718);
x_720 = lean_mk_string_unchecked(" := ", 4, 4);
x_721 = l_Lean_stringToMessageData(x_720);
lean_dec(x_720);
x_722 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_722, 0, x_719);
lean_ctor_set(x_722, 1, x_721);
x_723 = l_Lean_MessageData_ofExpr(x_1);
x_724 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_724, 0, x_722);
lean_ctor_set(x_724, 1, x_723);
x_725 = l_Lean_stringToMessageData(x_642);
lean_dec(x_642);
x_726 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_726, 0, x_724);
lean_ctor_set(x_726, 1, x_725);
x_10 = x_715;
x_11 = x_726;
x_12 = x_5;
x_13 = x_6;
x_14 = x_7;
x_15 = x_8;
x_16 = x_618;
goto block_25;
}
}
else
{
lean_object* x_727; lean_object* x_728; uint8_t x_729; 
lean_free_object(x_2);
x_727 = lean_ctor_get(x_4, 0);
lean_inc(x_727);
lean_dec(x_4);
x_728 = lean_st_ref_get(x_8, x_402);
x_729 = !lean_is_exclusive(x_728);
if (x_729 == 0)
{
lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; uint8_t x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; 
x_730 = lean_ctor_get(x_728, 1);
x_731 = lean_ctor_get(x_728, 0);
lean_dec(x_731);
x_732 = lean_ctor_get(x_7, 5);
lean_inc(x_732);
x_733 = lean_box(0);
x_734 = lean_unbox(x_733);
x_735 = l_Lean_SourceInfo_fromRef(x_732, x_734);
lean_dec(x_732);
x_736 = lean_mk_string_unchecked("Lean", 4, 4);
x_737 = lean_mk_string_unchecked("Parser", 6, 6);
x_738 = lean_mk_string_unchecked("Tactic", 6, 6);
x_739 = lean_mk_string_unchecked("tacticHave_", 11, 11);
lean_inc(x_737);
lean_inc(x_736);
x_740 = l_Lean_Name_mkStr4(x_736, x_737, x_738, x_739);
x_741 = lean_mk_string_unchecked("have", 4, 4);
lean_inc(x_735);
lean_ctor_set_tag(x_728, 2);
lean_ctor_set(x_728, 1, x_741);
lean_ctor_set(x_728, 0, x_735);
x_742 = lean_mk_string_unchecked("Term", 4, 4);
x_743 = lean_mk_string_unchecked("haveDecl", 8, 8);
lean_inc(x_742);
lean_inc(x_737);
lean_inc(x_736);
x_744 = l_Lean_Name_mkStr4(x_736, x_737, x_742, x_743);
x_745 = lean_mk_string_unchecked("haveIdDecl", 10, 10);
lean_inc(x_742);
lean_inc(x_737);
lean_inc(x_736);
x_746 = l_Lean_Name_mkStr4(x_736, x_737, x_742, x_745);
x_747 = lean_mk_string_unchecked("haveId", 6, 6);
lean_inc(x_742);
lean_inc(x_737);
lean_inc(x_736);
x_748 = l_Lean_Name_mkStr4(x_736, x_737, x_742, x_747);
lean_inc(x_727);
x_749 = lean_mk_syntax_ident(x_727);
lean_inc(x_735);
x_750 = l_Lean_Syntax_node1(x_735, x_748, x_749);
x_751 = lean_mk_string_unchecked("null", 4, 4);
x_752 = l_Lean_Name_mkStr1(x_751);
x_753 = l_Array_mkArray0(lean_box(0));
lean_inc(x_752);
lean_inc(x_735);
x_754 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_754, 0, x_735);
lean_ctor_set(x_754, 1, x_752);
lean_ctor_set(x_754, 2, x_753);
x_755 = lean_mk_string_unchecked("typeSpec", 8, 8);
x_756 = l_Lean_Name_mkStr4(x_736, x_737, x_742, x_755);
x_757 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_735);
x_758 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_758, 0, x_735);
lean_ctor_set(x_758, 1, x_757);
lean_inc(x_735);
x_759 = l_Lean_Syntax_node2(x_735, x_756, x_758, x_401);
lean_inc(x_735);
x_760 = l_Lean_Syntax_node1(x_735, x_752, x_759);
x_761 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_735);
x_762 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_762, 0, x_735);
lean_ctor_set(x_762, 1, x_761);
lean_inc(x_735);
x_763 = l_Lean_Syntax_node5(x_735, x_746, x_750, x_754, x_760, x_762, x_27);
lean_inc(x_735);
x_764 = l_Lean_Syntax_node1(x_735, x_744, x_763);
x_765 = l_Lean_Syntax_node2(x_735, x_740, x_728, x_764);
x_766 = lean_mk_string_unchecked("have ", 5, 5);
x_767 = l_Lean_stringToMessageData(x_766);
lean_dec(x_766);
x_768 = l_Lean_MessageData_ofName(x_727);
x_769 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_769, 0, x_767);
lean_ctor_set(x_769, 1, x_768);
x_770 = lean_mk_string_unchecked(" : ", 3, 3);
x_771 = l_Lean_stringToMessageData(x_770);
lean_dec(x_770);
x_772 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_772, 0, x_769);
lean_ctor_set(x_772, 1, x_771);
x_773 = l_Lean_MessageData_ofExpr(x_399);
x_774 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_774, 0, x_772);
lean_ctor_set(x_774, 1, x_773);
x_775 = lean_mk_string_unchecked(" := ", 4, 4);
x_776 = l_Lean_stringToMessageData(x_775);
lean_dec(x_775);
x_777 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_777, 0, x_774);
lean_ctor_set(x_777, 1, x_776);
x_778 = l_Lean_MessageData_ofExpr(x_1);
x_779 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_779, 0, x_777);
lean_ctor_set(x_779, 1, x_778);
x_780 = lean_mk_string_unchecked("", 0, 0);
x_781 = l_Lean_stringToMessageData(x_780);
lean_dec(x_780);
x_782 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_782, 0, x_779);
lean_ctor_set(x_782, 1, x_781);
x_10 = x_765;
x_11 = x_782;
x_12 = x_5;
x_13 = x_6;
x_14 = x_7;
x_15 = x_8;
x_16 = x_730;
goto block_25;
}
else
{
lean_object* x_783; lean_object* x_784; lean_object* x_785; uint8_t x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; lean_object* x_822; lean_object* x_823; lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; lean_object* x_834; lean_object* x_835; 
x_783 = lean_ctor_get(x_728, 1);
lean_inc(x_783);
lean_dec(x_728);
x_784 = lean_ctor_get(x_7, 5);
lean_inc(x_784);
x_785 = lean_box(0);
x_786 = lean_unbox(x_785);
x_787 = l_Lean_SourceInfo_fromRef(x_784, x_786);
lean_dec(x_784);
x_788 = lean_mk_string_unchecked("Lean", 4, 4);
x_789 = lean_mk_string_unchecked("Parser", 6, 6);
x_790 = lean_mk_string_unchecked("Tactic", 6, 6);
x_791 = lean_mk_string_unchecked("tacticHave_", 11, 11);
lean_inc(x_789);
lean_inc(x_788);
x_792 = l_Lean_Name_mkStr4(x_788, x_789, x_790, x_791);
x_793 = lean_mk_string_unchecked("have", 4, 4);
lean_inc(x_787);
x_794 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_794, 0, x_787);
lean_ctor_set(x_794, 1, x_793);
x_795 = lean_mk_string_unchecked("Term", 4, 4);
x_796 = lean_mk_string_unchecked("haveDecl", 8, 8);
lean_inc(x_795);
lean_inc(x_789);
lean_inc(x_788);
x_797 = l_Lean_Name_mkStr4(x_788, x_789, x_795, x_796);
x_798 = lean_mk_string_unchecked("haveIdDecl", 10, 10);
lean_inc(x_795);
lean_inc(x_789);
lean_inc(x_788);
x_799 = l_Lean_Name_mkStr4(x_788, x_789, x_795, x_798);
x_800 = lean_mk_string_unchecked("haveId", 6, 6);
lean_inc(x_795);
lean_inc(x_789);
lean_inc(x_788);
x_801 = l_Lean_Name_mkStr4(x_788, x_789, x_795, x_800);
lean_inc(x_727);
x_802 = lean_mk_syntax_ident(x_727);
lean_inc(x_787);
x_803 = l_Lean_Syntax_node1(x_787, x_801, x_802);
x_804 = lean_mk_string_unchecked("null", 4, 4);
x_805 = l_Lean_Name_mkStr1(x_804);
x_806 = l_Array_mkArray0(lean_box(0));
lean_inc(x_805);
lean_inc(x_787);
x_807 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_807, 0, x_787);
lean_ctor_set(x_807, 1, x_805);
lean_ctor_set(x_807, 2, x_806);
x_808 = lean_mk_string_unchecked("typeSpec", 8, 8);
x_809 = l_Lean_Name_mkStr4(x_788, x_789, x_795, x_808);
x_810 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_787);
x_811 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_811, 0, x_787);
lean_ctor_set(x_811, 1, x_810);
lean_inc(x_787);
x_812 = l_Lean_Syntax_node2(x_787, x_809, x_811, x_401);
lean_inc(x_787);
x_813 = l_Lean_Syntax_node1(x_787, x_805, x_812);
x_814 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_787);
x_815 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_815, 0, x_787);
lean_ctor_set(x_815, 1, x_814);
lean_inc(x_787);
x_816 = l_Lean_Syntax_node5(x_787, x_799, x_803, x_807, x_813, x_815, x_27);
lean_inc(x_787);
x_817 = l_Lean_Syntax_node1(x_787, x_797, x_816);
x_818 = l_Lean_Syntax_node2(x_787, x_792, x_794, x_817);
x_819 = lean_mk_string_unchecked("have ", 5, 5);
x_820 = l_Lean_stringToMessageData(x_819);
lean_dec(x_819);
x_821 = l_Lean_MessageData_ofName(x_727);
x_822 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_822, 0, x_820);
lean_ctor_set(x_822, 1, x_821);
x_823 = lean_mk_string_unchecked(" : ", 3, 3);
x_824 = l_Lean_stringToMessageData(x_823);
lean_dec(x_823);
x_825 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_825, 0, x_822);
lean_ctor_set(x_825, 1, x_824);
x_826 = l_Lean_MessageData_ofExpr(x_399);
x_827 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_827, 0, x_825);
lean_ctor_set(x_827, 1, x_826);
x_828 = lean_mk_string_unchecked(" := ", 4, 4);
x_829 = l_Lean_stringToMessageData(x_828);
lean_dec(x_828);
x_830 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_830, 0, x_827);
lean_ctor_set(x_830, 1, x_829);
x_831 = l_Lean_MessageData_ofExpr(x_1);
x_832 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_832, 0, x_830);
lean_ctor_set(x_832, 1, x_831);
x_833 = lean_mk_string_unchecked("", 0, 0);
x_834 = l_Lean_stringToMessageData(x_833);
lean_dec(x_833);
x_835 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_835, 0, x_832);
lean_ctor_set(x_835, 1, x_834);
x_10 = x_818;
x_11 = x_835;
x_12 = x_5;
x_13 = x_6;
x_14 = x_7;
x_15 = x_8;
x_16 = x_783;
goto block_25;
}
}
}
block_502:
{
lean_object* x_404; uint8_t x_405; 
x_404 = lean_st_ref_get(x_8, x_402);
x_405 = !lean_is_exclusive(x_404);
if (x_405 == 0)
{
lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; 
x_406 = lean_ctor_get(x_404, 1);
x_407 = lean_ctor_get(x_404, 0);
lean_dec(x_407);
x_408 = lean_ctor_get(x_7, 5);
lean_inc(x_408);
x_409 = l_Lean_SourceInfo_fromRef(x_408, x_3);
lean_dec(x_408);
x_410 = lean_mk_string_unchecked("Lean", 4, 4);
x_411 = lean_mk_string_unchecked("Parser", 6, 6);
x_412 = lean_mk_string_unchecked("Tactic", 6, 6);
x_413 = lean_mk_string_unchecked("tacticLet_", 10, 10);
lean_inc(x_411);
lean_inc(x_410);
x_414 = l_Lean_Name_mkStr4(x_410, x_411, x_412, x_413);
x_415 = lean_mk_string_unchecked("let", 3, 3);
lean_inc(x_409);
lean_ctor_set_tag(x_404, 2);
lean_ctor_set(x_404, 1, x_415);
lean_ctor_set(x_404, 0, x_409);
x_416 = lean_mk_string_unchecked("Term", 4, 4);
x_417 = lean_mk_string_unchecked("letDecl", 7, 7);
lean_inc(x_416);
lean_inc(x_411);
lean_inc(x_410);
x_418 = l_Lean_Name_mkStr4(x_410, x_411, x_416, x_417);
x_419 = lean_mk_string_unchecked("letIdDecl", 9, 9);
lean_inc(x_416);
lean_inc(x_411);
lean_inc(x_410);
x_420 = l_Lean_Name_mkStr4(x_410, x_411, x_416, x_419);
lean_inc(x_403);
x_421 = lean_mk_syntax_ident(x_403);
x_422 = lean_mk_string_unchecked("null", 4, 4);
x_423 = l_Lean_Name_mkStr1(x_422);
x_424 = l_Array_mkArray0(lean_box(0));
lean_inc(x_423);
lean_inc(x_409);
x_425 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_425, 0, x_409);
lean_ctor_set(x_425, 1, x_423);
lean_ctor_set(x_425, 2, x_424);
x_426 = lean_mk_string_unchecked("typeSpec", 8, 8);
x_427 = l_Lean_Name_mkStr4(x_410, x_411, x_416, x_426);
x_428 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_409);
x_429 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_429, 0, x_409);
lean_ctor_set(x_429, 1, x_428);
lean_inc(x_409);
x_430 = l_Lean_Syntax_node2(x_409, x_427, x_429, x_401);
lean_inc(x_409);
x_431 = l_Lean_Syntax_node1(x_409, x_423, x_430);
x_432 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_409);
x_433 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_433, 0, x_409);
lean_ctor_set(x_433, 1, x_432);
lean_inc(x_409);
x_434 = l_Lean_Syntax_node5(x_409, x_420, x_421, x_425, x_431, x_433, x_27);
lean_inc(x_409);
x_435 = l_Lean_Syntax_node1(x_409, x_418, x_434);
x_436 = l_Lean_Syntax_node2(x_409, x_414, x_404, x_435);
x_437 = lean_mk_string_unchecked("let ", 4, 4);
x_438 = l_Lean_stringToMessageData(x_437);
lean_dec(x_437);
x_439 = l_Lean_MessageData_ofName(x_403);
x_440 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_440, 0, x_438);
lean_ctor_set(x_440, 1, x_439);
x_441 = lean_mk_string_unchecked(" : ", 3, 3);
x_442 = l_Lean_stringToMessageData(x_441);
lean_dec(x_441);
x_443 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_443, 0, x_440);
lean_ctor_set(x_443, 1, x_442);
x_444 = l_Lean_MessageData_ofExpr(x_399);
x_445 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_445, 0, x_443);
lean_ctor_set(x_445, 1, x_444);
x_446 = lean_mk_string_unchecked(" := ", 4, 4);
x_447 = l_Lean_stringToMessageData(x_446);
lean_dec(x_446);
x_448 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_448, 0, x_445);
lean_ctor_set(x_448, 1, x_447);
x_449 = l_Lean_MessageData_ofExpr(x_1);
x_450 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_450, 0, x_448);
lean_ctor_set(x_450, 1, x_449);
x_451 = lean_mk_string_unchecked("", 0, 0);
x_452 = l_Lean_stringToMessageData(x_451);
lean_dec(x_451);
x_453 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_453, 0, x_450);
lean_ctor_set(x_453, 1, x_452);
x_10 = x_436;
x_11 = x_453;
x_12 = x_5;
x_13 = x_6;
x_14 = x_7;
x_15 = x_8;
x_16 = x_406;
goto block_25;
}
else
{
lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; 
x_454 = lean_ctor_get(x_404, 1);
lean_inc(x_454);
lean_dec(x_404);
x_455 = lean_ctor_get(x_7, 5);
lean_inc(x_455);
x_456 = l_Lean_SourceInfo_fromRef(x_455, x_3);
lean_dec(x_455);
x_457 = lean_mk_string_unchecked("Lean", 4, 4);
x_458 = lean_mk_string_unchecked("Parser", 6, 6);
x_459 = lean_mk_string_unchecked("Tactic", 6, 6);
x_460 = lean_mk_string_unchecked("tacticLet_", 10, 10);
lean_inc(x_458);
lean_inc(x_457);
x_461 = l_Lean_Name_mkStr4(x_457, x_458, x_459, x_460);
x_462 = lean_mk_string_unchecked("let", 3, 3);
lean_inc(x_456);
x_463 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_463, 0, x_456);
lean_ctor_set(x_463, 1, x_462);
x_464 = lean_mk_string_unchecked("Term", 4, 4);
x_465 = lean_mk_string_unchecked("letDecl", 7, 7);
lean_inc(x_464);
lean_inc(x_458);
lean_inc(x_457);
x_466 = l_Lean_Name_mkStr4(x_457, x_458, x_464, x_465);
x_467 = lean_mk_string_unchecked("letIdDecl", 9, 9);
lean_inc(x_464);
lean_inc(x_458);
lean_inc(x_457);
x_468 = l_Lean_Name_mkStr4(x_457, x_458, x_464, x_467);
lean_inc(x_403);
x_469 = lean_mk_syntax_ident(x_403);
x_470 = lean_mk_string_unchecked("null", 4, 4);
x_471 = l_Lean_Name_mkStr1(x_470);
x_472 = l_Array_mkArray0(lean_box(0));
lean_inc(x_471);
lean_inc(x_456);
x_473 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_473, 0, x_456);
lean_ctor_set(x_473, 1, x_471);
lean_ctor_set(x_473, 2, x_472);
x_474 = lean_mk_string_unchecked("typeSpec", 8, 8);
x_475 = l_Lean_Name_mkStr4(x_457, x_458, x_464, x_474);
x_476 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_456);
x_477 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_477, 0, x_456);
lean_ctor_set(x_477, 1, x_476);
lean_inc(x_456);
x_478 = l_Lean_Syntax_node2(x_456, x_475, x_477, x_401);
lean_inc(x_456);
x_479 = l_Lean_Syntax_node1(x_456, x_471, x_478);
x_480 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_456);
x_481 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_481, 0, x_456);
lean_ctor_set(x_481, 1, x_480);
lean_inc(x_456);
x_482 = l_Lean_Syntax_node5(x_456, x_468, x_469, x_473, x_479, x_481, x_27);
lean_inc(x_456);
x_483 = l_Lean_Syntax_node1(x_456, x_466, x_482);
x_484 = l_Lean_Syntax_node2(x_456, x_461, x_463, x_483);
x_485 = lean_mk_string_unchecked("let ", 4, 4);
x_486 = l_Lean_stringToMessageData(x_485);
lean_dec(x_485);
x_487 = l_Lean_MessageData_ofName(x_403);
x_488 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_488, 0, x_486);
lean_ctor_set(x_488, 1, x_487);
x_489 = lean_mk_string_unchecked(" : ", 3, 3);
x_490 = l_Lean_stringToMessageData(x_489);
lean_dec(x_489);
x_491 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_491, 0, x_488);
lean_ctor_set(x_491, 1, x_490);
x_492 = l_Lean_MessageData_ofExpr(x_399);
x_493 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_493, 0, x_491);
lean_ctor_set(x_493, 1, x_492);
x_494 = lean_mk_string_unchecked(" := ", 4, 4);
x_495 = l_Lean_stringToMessageData(x_494);
lean_dec(x_494);
x_496 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_496, 0, x_493);
lean_ctor_set(x_496, 1, x_495);
x_497 = l_Lean_MessageData_ofExpr(x_1);
x_498 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_498, 0, x_496);
lean_ctor_set(x_498, 1, x_497);
x_499 = lean_mk_string_unchecked("", 0, 0);
x_500 = l_Lean_stringToMessageData(x_499);
lean_dec(x_499);
x_501 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_501, 0, x_498);
lean_ctor_set(x_501, 1, x_500);
x_10 = x_484;
x_11 = x_501;
x_12 = x_5;
x_13 = x_6;
x_14 = x_7;
x_15 = x_8;
x_16 = x_454;
goto block_25;
}
}
}
else
{
uint8_t x_836; 
lean_free_object(x_2);
lean_dec(x_399);
lean_dec(x_27);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_836 = !lean_is_exclusive(x_400);
if (x_836 == 0)
{
return x_400;
}
else
{
lean_object* x_837; lean_object* x_838; lean_object* x_839; 
x_837 = lean_ctor_get(x_400, 0);
x_838 = lean_ctor_get(x_400, 1);
lean_inc(x_838);
lean_inc(x_837);
lean_dec(x_400);
x_839 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_839, 0, x_837);
lean_ctor_set(x_839, 1, x_838);
return x_839;
}
}
}
else
{
lean_object* x_840; lean_object* x_841; 
x_840 = lean_ctor_get(x_2, 0);
lean_inc(x_840);
lean_dec(x_2);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_840);
x_841 = l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax(x_840, x_5, x_6, x_7, x_8, x_28);
if (lean_obj_tag(x_841) == 0)
{
lean_object* x_842; lean_object* x_843; lean_object* x_844; 
x_842 = lean_ctor_get(x_841, 0);
lean_inc(x_842);
x_843 = lean_ctor_get(x_841, 1);
lean_inc(x_843);
lean_dec(x_841);
if (x_3 == 0)
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_896; lean_object* x_897; 
x_896 = lean_mk_string_unchecked("_", 1, 1);
x_897 = l_Lean_Name_mkStr1(x_896);
x_844 = x_897;
goto block_895;
}
else
{
lean_object* x_898; 
x_898 = lean_ctor_get(x_4, 0);
lean_inc(x_898);
lean_dec(x_4);
x_844 = x_898;
goto block_895;
}
}
else
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_899; lean_object* x_900; lean_object* x_901; lean_object* x_902; lean_object* x_903; lean_object* x_904; uint8_t x_905; lean_object* x_906; lean_object* x_907; lean_object* x_908; lean_object* x_909; lean_object* x_910; lean_object* x_911; lean_object* x_912; lean_object* x_913; lean_object* x_914; lean_object* x_915; lean_object* x_916; lean_object* x_917; lean_object* x_918; lean_object* x_919; lean_object* x_920; lean_object* x_921; lean_object* x_922; lean_object* x_923; lean_object* x_924; lean_object* x_925; lean_object* x_926; lean_object* x_927; lean_object* x_928; lean_object* x_929; lean_object* x_930; lean_object* x_931; lean_object* x_932; lean_object* x_933; lean_object* x_934; lean_object* x_935; lean_object* x_936; lean_object* x_937; lean_object* x_938; lean_object* x_939; lean_object* x_940; lean_object* x_941; lean_object* x_942; lean_object* x_943; lean_object* x_944; lean_object* x_945; lean_object* x_946; lean_object* x_947; lean_object* x_948; lean_object* x_949; lean_object* x_950; lean_object* x_951; lean_object* x_952; lean_object* x_953; lean_object* x_954; lean_object* x_955; lean_object* x_956; lean_object* x_957; lean_object* x_958; lean_object* x_959; lean_object* x_960; lean_object* x_961; lean_object* x_962; lean_object* x_963; lean_object* x_964; lean_object* x_965; lean_object* x_966; lean_object* x_967; lean_object* x_968; lean_object* x_969; lean_object* x_970; lean_object* x_971; lean_object* x_972; lean_object* x_973; lean_object* x_974; lean_object* x_975; lean_object* x_976; lean_object* x_977; lean_object* x_978; lean_object* x_979; lean_object* x_980; lean_object* x_981; lean_object* x_982; lean_object* x_983; lean_object* x_984; lean_object* x_985; lean_object* x_986; lean_object* x_987; lean_object* x_988; lean_object* x_989; lean_object* x_990; lean_object* x_991; lean_object* x_992; lean_object* x_993; lean_object* x_994; lean_object* x_995; lean_object* x_996; lean_object* x_997; lean_object* x_998; lean_object* x_999; lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; lean_object* x_1003; lean_object* x_1004; lean_object* x_1005; lean_object* x_1006; lean_object* x_1007; lean_object* x_1008; lean_object* x_1009; lean_object* x_1010; lean_object* x_1011; 
x_899 = lean_st_ref_get(x_8, x_843);
x_900 = lean_ctor_get(x_899, 0);
lean_inc(x_900);
x_901 = lean_ctor_get(x_899, 1);
lean_inc(x_901);
if (lean_is_exclusive(x_899)) {
 lean_ctor_release(x_899, 0);
 lean_ctor_release(x_899, 1);
 x_902 = x_899;
} else {
 lean_dec_ref(x_899);
 x_902 = lean_box(0);
}
x_903 = lean_ctor_get(x_7, 5);
lean_inc(x_903);
x_904 = lean_box(0);
x_905 = lean_unbox(x_904);
x_906 = l_Lean_SourceInfo_fromRef(x_903, x_905);
lean_dec(x_903);
x_907 = lean_ctor_get(x_7, 10);
lean_inc(x_907);
x_908 = lean_ctor_get(x_900, 0);
lean_inc(x_908);
lean_dec(x_900);
x_909 = l_Lean_Environment_mainModule(x_908);
lean_dec(x_908);
x_910 = lean_mk_string_unchecked("Lean", 4, 4);
x_911 = lean_mk_string_unchecked("Parser", 6, 6);
x_912 = lean_mk_string_unchecked("Tactic", 6, 6);
x_913 = lean_mk_string_unchecked("tacticHave_", 11, 11);
lean_inc(x_912);
lean_inc(x_911);
lean_inc(x_910);
x_914 = l_Lean_Name_mkStr4(x_910, x_911, x_912, x_913);
x_915 = lean_mk_string_unchecked("have", 4, 4);
lean_inc(x_906);
if (lean_is_scalar(x_902)) {
 x_916 = lean_alloc_ctor(2, 2, 0);
} else {
 x_916 = x_902;
 lean_ctor_set_tag(x_916, 2);
}
lean_ctor_set(x_916, 0, x_906);
lean_ctor_set(x_916, 1, x_915);
x_917 = lean_mk_string_unchecked("Term", 4, 4);
x_918 = lean_mk_string_unchecked("haveDecl", 8, 8);
lean_inc(x_917);
lean_inc(x_911);
lean_inc(x_910);
x_919 = l_Lean_Name_mkStr4(x_910, x_911, x_917, x_918);
x_920 = lean_mk_string_unchecked("haveIdDecl", 10, 10);
lean_inc(x_917);
lean_inc(x_911);
lean_inc(x_910);
x_921 = l_Lean_Name_mkStr4(x_910, x_911, x_917, x_920);
x_922 = lean_mk_string_unchecked("haveId", 6, 6);
lean_inc(x_917);
lean_inc(x_911);
lean_inc(x_910);
x_923 = l_Lean_Name_mkStr4(x_910, x_911, x_917, x_922);
x_924 = lean_mk_string_unchecked("hygieneInfo", 11, 11);
x_925 = l_Lean_Name_mkStr1(x_924);
x_926 = lean_mk_string_unchecked("", 0, 0);
lean_inc(x_926);
x_927 = l_String_toSubstring_x27(x_926);
x_928 = lean_box(0);
x_929 = l_Lean_addMacroScope(x_909, x_928, x_907);
x_930 = lean_mk_string_unchecked("Meta", 4, 4);
x_931 = lean_mk_string_unchecked("TryThis", 7, 7);
lean_inc(x_912);
lean_inc(x_930);
lean_inc(x_910);
x_932 = l_Lean_Name_mkStr4(x_910, x_930, x_912, x_931);
x_933 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_933, 0, x_932);
lean_inc(x_930);
lean_inc(x_910);
x_934 = l_Lean_Name_mkStr2(x_910, x_930);
x_935 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_935, 0, x_934);
x_936 = lean_mk_string_unchecked("PrettyPrinter", 13, 13);
lean_inc(x_910);
x_937 = l_Lean_Name_mkStr2(x_910, x_936);
x_938 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_938, 0, x_937);
x_939 = lean_mk_string_unchecked("Elab", 4, 4);
lean_inc(x_912);
lean_inc(x_939);
lean_inc(x_910);
x_940 = l_Lean_Name_mkStr3(x_910, x_939, x_912);
x_941 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_941, 0, x_940);
lean_inc(x_910);
x_942 = l_Lean_Name_mkStr2(x_910, x_939);
x_943 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_943, 0, x_942);
lean_inc(x_910);
x_944 = l_Lean_Name_mkStr1(x_910);
x_945 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_945, 0, x_944);
x_946 = lean_mk_string_unchecked("Server", 6, 6);
x_947 = lean_mk_string_unchecked("RequestM", 8, 8);
lean_inc(x_946);
lean_inc(x_910);
x_948 = l_Lean_Name_mkStr3(x_910, x_946, x_947);
x_949 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_949, 0, x_948);
lean_inc(x_910);
x_950 = l_Lean_Name_mkStr2(x_910, x_946);
x_951 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_951, 0, x_950);
lean_inc(x_910);
x_952 = l_Lean_Name_mkStr3(x_910, x_930, x_912);
x_953 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_953, 0, x_952);
x_954 = lean_box(0);
lean_inc(x_945);
x_955 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_955, 0, x_945);
lean_ctor_set(x_955, 1, x_954);
lean_inc(x_943);
x_956 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_956, 0, x_943);
lean_ctor_set(x_956, 1, x_955);
lean_inc(x_943);
x_957 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_957, 0, x_943);
lean_ctor_set(x_957, 1, x_956);
x_958 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_958, 0, x_953);
lean_ctor_set(x_958, 1, x_957);
lean_inc(x_941);
x_959 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_959, 0, x_941);
lean_ctor_set(x_959, 1, x_958);
lean_inc(x_941);
x_960 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_960, 0, x_941);
lean_ctor_set(x_960, 1, x_959);
lean_inc(x_938);
x_961 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_961, 0, x_938);
lean_ctor_set(x_961, 1, x_960);
lean_inc(x_938);
x_962 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_962, 0, x_938);
lean_ctor_set(x_962, 1, x_961);
lean_inc(x_935);
x_963 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_963, 0, x_935);
lean_ctor_set(x_963, 1, x_962);
lean_inc(x_935);
x_964 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_964, 0, x_935);
lean_ctor_set(x_964, 1, x_963);
lean_inc(x_951);
x_965 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_965, 0, x_951);
lean_ctor_set(x_965, 1, x_964);
x_966 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_966, 0, x_951);
lean_ctor_set(x_966, 1, x_965);
lean_inc(x_949);
x_967 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_967, 0, x_949);
lean_ctor_set(x_967, 1, x_966);
x_968 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_968, 0, x_949);
lean_ctor_set(x_968, 1, x_967);
x_969 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_969, 0, x_945);
lean_ctor_set(x_969, 1, x_968);
lean_inc(x_943);
x_970 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_970, 0, x_943);
lean_ctor_set(x_970, 1, x_969);
lean_inc(x_943);
x_971 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_971, 0, x_943);
lean_ctor_set(x_971, 1, x_970);
x_972 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_972, 0, x_943);
lean_ctor_set(x_972, 1, x_971);
lean_inc(x_941);
x_973 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_973, 0, x_941);
lean_ctor_set(x_973, 1, x_972);
lean_inc(x_941);
x_974 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_974, 0, x_941);
lean_ctor_set(x_974, 1, x_973);
x_975 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_975, 0, x_941);
lean_ctor_set(x_975, 1, x_974);
lean_inc(x_938);
x_976 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_976, 0, x_938);
lean_ctor_set(x_976, 1, x_975);
lean_inc(x_938);
x_977 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_977, 0, x_938);
lean_ctor_set(x_977, 1, x_976);
x_978 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_978, 0, x_938);
lean_ctor_set(x_978, 1, x_977);
lean_inc(x_935);
x_979 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_979, 0, x_935);
lean_ctor_set(x_979, 1, x_978);
lean_inc(x_935);
x_980 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_980, 0, x_935);
lean_ctor_set(x_980, 1, x_979);
x_981 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_981, 0, x_935);
lean_ctor_set(x_981, 1, x_980);
x_982 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_982, 0, x_933);
lean_ctor_set(x_982, 1, x_981);
lean_inc(x_906);
x_983 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_983, 0, x_906);
lean_ctor_set(x_983, 1, x_927);
lean_ctor_set(x_983, 2, x_929);
lean_ctor_set(x_983, 3, x_982);
lean_inc(x_906);
x_984 = l_Lean_Syntax_node1(x_906, x_925, x_983);
lean_inc(x_906);
x_985 = l_Lean_Syntax_node1(x_906, x_923, x_984);
x_986 = lean_mk_string_unchecked("null", 4, 4);
x_987 = l_Lean_Name_mkStr1(x_986);
x_988 = l_Array_mkArray0(lean_box(0));
lean_inc(x_987);
lean_inc(x_906);
x_989 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_989, 0, x_906);
lean_ctor_set(x_989, 1, x_987);
lean_ctor_set(x_989, 2, x_988);
x_990 = lean_mk_string_unchecked("typeSpec", 8, 8);
x_991 = l_Lean_Name_mkStr4(x_910, x_911, x_917, x_990);
x_992 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_906);
x_993 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_993, 0, x_906);
lean_ctor_set(x_993, 1, x_992);
lean_inc(x_906);
x_994 = l_Lean_Syntax_node2(x_906, x_991, x_993, x_842);
lean_inc(x_906);
x_995 = l_Lean_Syntax_node1(x_906, x_987, x_994);
x_996 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_906);
x_997 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_997, 0, x_906);
lean_ctor_set(x_997, 1, x_996);
lean_inc(x_906);
x_998 = l_Lean_Syntax_node5(x_906, x_921, x_985, x_989, x_995, x_997, x_27);
lean_inc(x_906);
x_999 = l_Lean_Syntax_node1(x_906, x_919, x_998);
x_1000 = l_Lean_Syntax_node2(x_906, x_914, x_916, x_999);
x_1001 = lean_mk_string_unchecked("have : ", 7, 7);
x_1002 = l_Lean_stringToMessageData(x_1001);
lean_dec(x_1001);
x_1003 = l_Lean_MessageData_ofExpr(x_840);
x_1004 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1004, 0, x_1002);
lean_ctor_set(x_1004, 1, x_1003);
x_1005 = lean_mk_string_unchecked(" := ", 4, 4);
x_1006 = l_Lean_stringToMessageData(x_1005);
lean_dec(x_1005);
x_1007 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1007, 0, x_1004);
lean_ctor_set(x_1007, 1, x_1006);
x_1008 = l_Lean_MessageData_ofExpr(x_1);
x_1009 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1009, 0, x_1007);
lean_ctor_set(x_1009, 1, x_1008);
x_1010 = l_Lean_stringToMessageData(x_926);
lean_dec(x_926);
x_1011 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1011, 0, x_1009);
lean_ctor_set(x_1011, 1, x_1010);
x_10 = x_1000;
x_11 = x_1011;
x_12 = x_5;
x_13 = x_6;
x_14 = x_7;
x_15 = x_8;
x_16 = x_901;
goto block_25;
}
else
{
lean_object* x_1012; lean_object* x_1013; lean_object* x_1014; lean_object* x_1015; lean_object* x_1016; lean_object* x_1017; uint8_t x_1018; lean_object* x_1019; lean_object* x_1020; lean_object* x_1021; lean_object* x_1022; lean_object* x_1023; lean_object* x_1024; lean_object* x_1025; lean_object* x_1026; lean_object* x_1027; lean_object* x_1028; lean_object* x_1029; lean_object* x_1030; lean_object* x_1031; lean_object* x_1032; lean_object* x_1033; lean_object* x_1034; lean_object* x_1035; lean_object* x_1036; lean_object* x_1037; lean_object* x_1038; lean_object* x_1039; lean_object* x_1040; lean_object* x_1041; lean_object* x_1042; lean_object* x_1043; lean_object* x_1044; lean_object* x_1045; lean_object* x_1046; lean_object* x_1047; lean_object* x_1048; lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; lean_object* x_1052; lean_object* x_1053; lean_object* x_1054; lean_object* x_1055; lean_object* x_1056; lean_object* x_1057; lean_object* x_1058; lean_object* x_1059; lean_object* x_1060; lean_object* x_1061; lean_object* x_1062; lean_object* x_1063; lean_object* x_1064; lean_object* x_1065; lean_object* x_1066; lean_object* x_1067; 
x_1012 = lean_ctor_get(x_4, 0);
lean_inc(x_1012);
lean_dec(x_4);
x_1013 = lean_st_ref_get(x_8, x_843);
x_1014 = lean_ctor_get(x_1013, 1);
lean_inc(x_1014);
if (lean_is_exclusive(x_1013)) {
 lean_ctor_release(x_1013, 0);
 lean_ctor_release(x_1013, 1);
 x_1015 = x_1013;
} else {
 lean_dec_ref(x_1013);
 x_1015 = lean_box(0);
}
x_1016 = lean_ctor_get(x_7, 5);
lean_inc(x_1016);
x_1017 = lean_box(0);
x_1018 = lean_unbox(x_1017);
x_1019 = l_Lean_SourceInfo_fromRef(x_1016, x_1018);
lean_dec(x_1016);
x_1020 = lean_mk_string_unchecked("Lean", 4, 4);
x_1021 = lean_mk_string_unchecked("Parser", 6, 6);
x_1022 = lean_mk_string_unchecked("Tactic", 6, 6);
x_1023 = lean_mk_string_unchecked("tacticHave_", 11, 11);
lean_inc(x_1021);
lean_inc(x_1020);
x_1024 = l_Lean_Name_mkStr4(x_1020, x_1021, x_1022, x_1023);
x_1025 = lean_mk_string_unchecked("have", 4, 4);
lean_inc(x_1019);
if (lean_is_scalar(x_1015)) {
 x_1026 = lean_alloc_ctor(2, 2, 0);
} else {
 x_1026 = x_1015;
 lean_ctor_set_tag(x_1026, 2);
}
lean_ctor_set(x_1026, 0, x_1019);
lean_ctor_set(x_1026, 1, x_1025);
x_1027 = lean_mk_string_unchecked("Term", 4, 4);
x_1028 = lean_mk_string_unchecked("haveDecl", 8, 8);
lean_inc(x_1027);
lean_inc(x_1021);
lean_inc(x_1020);
x_1029 = l_Lean_Name_mkStr4(x_1020, x_1021, x_1027, x_1028);
x_1030 = lean_mk_string_unchecked("haveIdDecl", 10, 10);
lean_inc(x_1027);
lean_inc(x_1021);
lean_inc(x_1020);
x_1031 = l_Lean_Name_mkStr4(x_1020, x_1021, x_1027, x_1030);
x_1032 = lean_mk_string_unchecked("haveId", 6, 6);
lean_inc(x_1027);
lean_inc(x_1021);
lean_inc(x_1020);
x_1033 = l_Lean_Name_mkStr4(x_1020, x_1021, x_1027, x_1032);
lean_inc(x_1012);
x_1034 = lean_mk_syntax_ident(x_1012);
lean_inc(x_1019);
x_1035 = l_Lean_Syntax_node1(x_1019, x_1033, x_1034);
x_1036 = lean_mk_string_unchecked("null", 4, 4);
x_1037 = l_Lean_Name_mkStr1(x_1036);
x_1038 = l_Array_mkArray0(lean_box(0));
lean_inc(x_1037);
lean_inc(x_1019);
x_1039 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1039, 0, x_1019);
lean_ctor_set(x_1039, 1, x_1037);
lean_ctor_set(x_1039, 2, x_1038);
x_1040 = lean_mk_string_unchecked("typeSpec", 8, 8);
x_1041 = l_Lean_Name_mkStr4(x_1020, x_1021, x_1027, x_1040);
x_1042 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_1019);
x_1043 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1043, 0, x_1019);
lean_ctor_set(x_1043, 1, x_1042);
lean_inc(x_1019);
x_1044 = l_Lean_Syntax_node2(x_1019, x_1041, x_1043, x_842);
lean_inc(x_1019);
x_1045 = l_Lean_Syntax_node1(x_1019, x_1037, x_1044);
x_1046 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_1019);
x_1047 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1047, 0, x_1019);
lean_ctor_set(x_1047, 1, x_1046);
lean_inc(x_1019);
x_1048 = l_Lean_Syntax_node5(x_1019, x_1031, x_1035, x_1039, x_1045, x_1047, x_27);
lean_inc(x_1019);
x_1049 = l_Lean_Syntax_node1(x_1019, x_1029, x_1048);
x_1050 = l_Lean_Syntax_node2(x_1019, x_1024, x_1026, x_1049);
x_1051 = lean_mk_string_unchecked("have ", 5, 5);
x_1052 = l_Lean_stringToMessageData(x_1051);
lean_dec(x_1051);
x_1053 = l_Lean_MessageData_ofName(x_1012);
x_1054 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1054, 0, x_1052);
lean_ctor_set(x_1054, 1, x_1053);
x_1055 = lean_mk_string_unchecked(" : ", 3, 3);
x_1056 = l_Lean_stringToMessageData(x_1055);
lean_dec(x_1055);
x_1057 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1057, 0, x_1054);
lean_ctor_set(x_1057, 1, x_1056);
x_1058 = l_Lean_MessageData_ofExpr(x_840);
x_1059 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1059, 0, x_1057);
lean_ctor_set(x_1059, 1, x_1058);
x_1060 = lean_mk_string_unchecked(" := ", 4, 4);
x_1061 = l_Lean_stringToMessageData(x_1060);
lean_dec(x_1060);
x_1062 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1062, 0, x_1059);
lean_ctor_set(x_1062, 1, x_1061);
x_1063 = l_Lean_MessageData_ofExpr(x_1);
x_1064 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1064, 0, x_1062);
lean_ctor_set(x_1064, 1, x_1063);
x_1065 = lean_mk_string_unchecked("", 0, 0);
x_1066 = l_Lean_stringToMessageData(x_1065);
lean_dec(x_1065);
x_1067 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1067, 0, x_1064);
lean_ctor_set(x_1067, 1, x_1066);
x_10 = x_1050;
x_11 = x_1067;
x_12 = x_5;
x_13 = x_6;
x_14 = x_7;
x_15 = x_8;
x_16 = x_1014;
goto block_25;
}
}
block_895:
{
lean_object* x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; lean_object* x_864; lean_object* x_865; lean_object* x_866; lean_object* x_867; lean_object* x_868; lean_object* x_869; lean_object* x_870; lean_object* x_871; lean_object* x_872; lean_object* x_873; lean_object* x_874; lean_object* x_875; lean_object* x_876; lean_object* x_877; lean_object* x_878; lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; lean_object* x_884; lean_object* x_885; lean_object* x_886; lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; lean_object* x_891; lean_object* x_892; lean_object* x_893; lean_object* x_894; 
x_845 = lean_st_ref_get(x_8, x_843);
x_846 = lean_ctor_get(x_845, 1);
lean_inc(x_846);
if (lean_is_exclusive(x_845)) {
 lean_ctor_release(x_845, 0);
 lean_ctor_release(x_845, 1);
 x_847 = x_845;
} else {
 lean_dec_ref(x_845);
 x_847 = lean_box(0);
}
x_848 = lean_ctor_get(x_7, 5);
lean_inc(x_848);
x_849 = l_Lean_SourceInfo_fromRef(x_848, x_3);
lean_dec(x_848);
x_850 = lean_mk_string_unchecked("Lean", 4, 4);
x_851 = lean_mk_string_unchecked("Parser", 6, 6);
x_852 = lean_mk_string_unchecked("Tactic", 6, 6);
x_853 = lean_mk_string_unchecked("tacticLet_", 10, 10);
lean_inc(x_851);
lean_inc(x_850);
x_854 = l_Lean_Name_mkStr4(x_850, x_851, x_852, x_853);
x_855 = lean_mk_string_unchecked("let", 3, 3);
lean_inc(x_849);
if (lean_is_scalar(x_847)) {
 x_856 = lean_alloc_ctor(2, 2, 0);
} else {
 x_856 = x_847;
 lean_ctor_set_tag(x_856, 2);
}
lean_ctor_set(x_856, 0, x_849);
lean_ctor_set(x_856, 1, x_855);
x_857 = lean_mk_string_unchecked("Term", 4, 4);
x_858 = lean_mk_string_unchecked("letDecl", 7, 7);
lean_inc(x_857);
lean_inc(x_851);
lean_inc(x_850);
x_859 = l_Lean_Name_mkStr4(x_850, x_851, x_857, x_858);
x_860 = lean_mk_string_unchecked("letIdDecl", 9, 9);
lean_inc(x_857);
lean_inc(x_851);
lean_inc(x_850);
x_861 = l_Lean_Name_mkStr4(x_850, x_851, x_857, x_860);
lean_inc(x_844);
x_862 = lean_mk_syntax_ident(x_844);
x_863 = lean_mk_string_unchecked("null", 4, 4);
x_864 = l_Lean_Name_mkStr1(x_863);
x_865 = l_Array_mkArray0(lean_box(0));
lean_inc(x_864);
lean_inc(x_849);
x_866 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_866, 0, x_849);
lean_ctor_set(x_866, 1, x_864);
lean_ctor_set(x_866, 2, x_865);
x_867 = lean_mk_string_unchecked("typeSpec", 8, 8);
x_868 = l_Lean_Name_mkStr4(x_850, x_851, x_857, x_867);
x_869 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_849);
x_870 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_870, 0, x_849);
lean_ctor_set(x_870, 1, x_869);
lean_inc(x_849);
x_871 = l_Lean_Syntax_node2(x_849, x_868, x_870, x_842);
lean_inc(x_849);
x_872 = l_Lean_Syntax_node1(x_849, x_864, x_871);
x_873 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_849);
x_874 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_874, 0, x_849);
lean_ctor_set(x_874, 1, x_873);
lean_inc(x_849);
x_875 = l_Lean_Syntax_node5(x_849, x_861, x_862, x_866, x_872, x_874, x_27);
lean_inc(x_849);
x_876 = l_Lean_Syntax_node1(x_849, x_859, x_875);
x_877 = l_Lean_Syntax_node2(x_849, x_854, x_856, x_876);
x_878 = lean_mk_string_unchecked("let ", 4, 4);
x_879 = l_Lean_stringToMessageData(x_878);
lean_dec(x_878);
x_880 = l_Lean_MessageData_ofName(x_844);
x_881 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_881, 0, x_879);
lean_ctor_set(x_881, 1, x_880);
x_882 = lean_mk_string_unchecked(" : ", 3, 3);
x_883 = l_Lean_stringToMessageData(x_882);
lean_dec(x_882);
x_884 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_884, 0, x_881);
lean_ctor_set(x_884, 1, x_883);
x_885 = l_Lean_MessageData_ofExpr(x_840);
x_886 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_886, 0, x_884);
lean_ctor_set(x_886, 1, x_885);
x_887 = lean_mk_string_unchecked(" := ", 4, 4);
x_888 = l_Lean_stringToMessageData(x_887);
lean_dec(x_887);
x_889 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_889, 0, x_886);
lean_ctor_set(x_889, 1, x_888);
x_890 = l_Lean_MessageData_ofExpr(x_1);
x_891 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_891, 0, x_889);
lean_ctor_set(x_891, 1, x_890);
x_892 = lean_mk_string_unchecked("", 0, 0);
x_893 = l_Lean_stringToMessageData(x_892);
lean_dec(x_892);
x_894 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_894, 0, x_891);
lean_ctor_set(x_894, 1, x_893);
x_10 = x_877;
x_11 = x_894;
x_12 = x_5;
x_13 = x_6;
x_14 = x_7;
x_15 = x_8;
x_16 = x_846;
goto block_25;
}
}
else
{
lean_object* x_1068; lean_object* x_1069; lean_object* x_1070; lean_object* x_1071; 
lean_dec(x_840);
lean_dec(x_27);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_1068 = lean_ctor_get(x_841, 0);
lean_inc(x_1068);
x_1069 = lean_ctor_get(x_841, 1);
lean_inc(x_1069);
if (lean_is_exclusive(x_841)) {
 lean_ctor_release(x_841, 0);
 lean_ctor_release(x_841, 1);
 x_1070 = x_841;
} else {
 lean_dec_ref(x_841);
 x_1070 = lean_box(0);
}
if (lean_is_scalar(x_1070)) {
 x_1071 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1071 = x_1070;
}
lean_ctor_set(x_1071, 0, x_1068);
lean_ctor_set(x_1071, 1, x_1069);
return x_1071;
}
}
}
block_106:
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_st_ref_get(x_8, x_28);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_32 = lean_ctor_get(x_30, 1);
x_33 = lean_ctor_get(x_30, 0);
lean_dec(x_33);
x_34 = lean_ctor_get(x_7, 5);
lean_inc(x_34);
x_35 = l_Lean_SourceInfo_fromRef(x_34, x_3);
lean_dec(x_34);
x_36 = lean_mk_string_unchecked("Lean", 4, 4);
x_37 = lean_mk_string_unchecked("Parser", 6, 6);
x_38 = lean_mk_string_unchecked("Tactic", 6, 6);
x_39 = lean_mk_string_unchecked("tacticLet_", 10, 10);
lean_inc(x_37);
lean_inc(x_36);
x_40 = l_Lean_Name_mkStr4(x_36, x_37, x_38, x_39);
x_41 = lean_mk_string_unchecked("let", 3, 3);
lean_inc(x_35);
lean_ctor_set_tag(x_30, 2);
lean_ctor_set(x_30, 1, x_41);
lean_ctor_set(x_30, 0, x_35);
x_42 = lean_mk_string_unchecked("Term", 4, 4);
x_43 = lean_mk_string_unchecked("letDecl", 7, 7);
lean_inc(x_42);
lean_inc(x_37);
lean_inc(x_36);
x_44 = l_Lean_Name_mkStr4(x_36, x_37, x_42, x_43);
x_45 = lean_mk_string_unchecked("letIdDecl", 9, 9);
x_46 = l_Lean_Name_mkStr4(x_36, x_37, x_42, x_45);
lean_inc(x_29);
x_47 = lean_mk_syntax_ident(x_29);
x_48 = lean_mk_string_unchecked("null", 4, 4);
x_49 = l_Lean_Name_mkStr1(x_48);
x_50 = l_Array_mkArray0(lean_box(0));
lean_inc(x_35);
x_51 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_51, 0, x_35);
lean_ctor_set(x_51, 1, x_49);
lean_ctor_set(x_51, 2, x_50);
x_52 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_35);
x_53 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_53, 0, x_35);
lean_ctor_set(x_53, 1, x_52);
lean_inc(x_51);
lean_inc(x_35);
x_54 = l_Lean_Syntax_node5(x_35, x_46, x_47, x_51, x_51, x_53, x_27);
lean_inc(x_35);
x_55 = l_Lean_Syntax_node1(x_35, x_44, x_54);
x_56 = l_Lean_Syntax_node2(x_35, x_40, x_30, x_55);
x_57 = lean_mk_string_unchecked("let ", 4, 4);
x_58 = l_Lean_stringToMessageData(x_57);
lean_dec(x_57);
x_59 = l_Lean_MessageData_ofName(x_29);
x_60 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_mk_string_unchecked(" := ", 4, 4);
x_62 = l_Lean_stringToMessageData(x_61);
lean_dec(x_61);
x_63 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_62);
x_64 = l_Lean_MessageData_ofExpr(x_1);
x_65 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_mk_string_unchecked("", 0, 0);
x_67 = l_Lean_stringToMessageData(x_66);
lean_dec(x_66);
x_68 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_67);
x_10 = x_56;
x_11 = x_68;
x_12 = x_5;
x_13 = x_6;
x_14 = x_7;
x_15 = x_8;
x_16 = x_32;
goto block_25;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_69 = lean_ctor_get(x_30, 1);
lean_inc(x_69);
lean_dec(x_30);
x_70 = lean_ctor_get(x_7, 5);
lean_inc(x_70);
x_71 = l_Lean_SourceInfo_fromRef(x_70, x_3);
lean_dec(x_70);
x_72 = lean_mk_string_unchecked("Lean", 4, 4);
x_73 = lean_mk_string_unchecked("Parser", 6, 6);
x_74 = lean_mk_string_unchecked("Tactic", 6, 6);
x_75 = lean_mk_string_unchecked("tacticLet_", 10, 10);
lean_inc(x_73);
lean_inc(x_72);
x_76 = l_Lean_Name_mkStr4(x_72, x_73, x_74, x_75);
x_77 = lean_mk_string_unchecked("let", 3, 3);
lean_inc(x_71);
x_78 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_78, 0, x_71);
lean_ctor_set(x_78, 1, x_77);
x_79 = lean_mk_string_unchecked("Term", 4, 4);
x_80 = lean_mk_string_unchecked("letDecl", 7, 7);
lean_inc(x_79);
lean_inc(x_73);
lean_inc(x_72);
x_81 = l_Lean_Name_mkStr4(x_72, x_73, x_79, x_80);
x_82 = lean_mk_string_unchecked("letIdDecl", 9, 9);
x_83 = l_Lean_Name_mkStr4(x_72, x_73, x_79, x_82);
lean_inc(x_29);
x_84 = lean_mk_syntax_ident(x_29);
x_85 = lean_mk_string_unchecked("null", 4, 4);
x_86 = l_Lean_Name_mkStr1(x_85);
x_87 = l_Array_mkArray0(lean_box(0));
lean_inc(x_71);
x_88 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_88, 0, x_71);
lean_ctor_set(x_88, 1, x_86);
lean_ctor_set(x_88, 2, x_87);
x_89 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_71);
x_90 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_90, 0, x_71);
lean_ctor_set(x_90, 1, x_89);
lean_inc(x_88);
lean_inc(x_71);
x_91 = l_Lean_Syntax_node5(x_71, x_83, x_84, x_88, x_88, x_90, x_27);
lean_inc(x_71);
x_92 = l_Lean_Syntax_node1(x_71, x_81, x_91);
x_93 = l_Lean_Syntax_node2(x_71, x_76, x_78, x_92);
x_94 = lean_mk_string_unchecked("let ", 4, 4);
x_95 = l_Lean_stringToMessageData(x_94);
lean_dec(x_94);
x_96 = l_Lean_MessageData_ofName(x_29);
x_97 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
x_98 = lean_mk_string_unchecked(" := ", 4, 4);
x_99 = l_Lean_stringToMessageData(x_98);
lean_dec(x_98);
x_100 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_100, 0, x_97);
lean_ctor_set(x_100, 1, x_99);
x_101 = l_Lean_MessageData_ofExpr(x_1);
x_102 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
x_103 = lean_mk_string_unchecked("", 0, 0);
x_104 = l_Lean_stringToMessageData(x_103);
lean_dec(x_103);
x_105 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_105, 0, x_102);
lean_ctor_set(x_105, 1, x_104);
x_10 = x_93;
x_11 = x_105;
x_12 = x_5;
x_13 = x_6;
x_14 = x_7;
x_15 = x_8;
x_16 = x_69;
goto block_25;
}
}
}
else
{
uint8_t x_1072; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_1072 = !lean_is_exclusive(x_26);
if (x_1072 == 0)
{
return x_26;
}
else
{
lean_object* x_1073; lean_object* x_1074; lean_object* x_1075; 
x_1073 = lean_ctor_get(x_26, 0);
x_1074 = lean_ctor_get(x_26, 1);
lean_inc(x_1074);
lean_inc(x_1073);
lean_dec(x_26);
x_1075 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1075, 0, x_1073);
lean_ctor_set(x_1075, 1, x_1074);
return x_1075;
}
}
block_25:
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_Lean_addMessageContextFull___at___Lean_Meta_recordSynthPendingFailure_spec__3(x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_10);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_17, 0, x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_17, 0);
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_17);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_10);
lean_ctor_set(x_23, 1, x_21);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_34; 
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_4);
x_34 = lean_infer_type(x_4, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_37 = l_Lean_Meta_isProp(x_35, x_11, x_12, x_13, x_14, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___boxed), 9, 4);
lean_closure_set(x_40, 0, x_4);
lean_closure_set(x_40, 1, x_3);
lean_closure_set(x_40, 2, x_38);
lean_closure_set(x_40, 3, x_2);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_41 = l_Lean_Meta_withExposedNames___redArg(x_40, x_11, x_12, x_13, x_14, x_39);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_ctor_get(x_42, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_dec(x_42);
x_16 = x_45;
x_17 = x_44;
x_18 = x_11;
x_19 = x_12;
x_20 = x_13;
x_21 = x_14;
x_22 = x_43;
goto block_33;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_46 = lean_ctor_get(x_41, 1);
lean_inc(x_46);
lean_dec(x_41);
x_47 = lean_ctor_get(x_42, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_42, 1);
lean_inc(x_48);
lean_dec(x_42);
x_49 = !lean_is_exclusive(x_6);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_6, 0);
x_51 = lean_box(0);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_48);
x_52 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic(x_47, x_48, x_50, x_51, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_46);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_mk_string_unchecked("a proof", 7, 7);
lean_ctor_set_tag(x_6, 3);
lean_ctor_set(x_6, 0, x_55);
x_56 = l_Lean_MessageData_ofFormat(x_6);
x_57 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg(x_56, x_48);
x_58 = l_Lean_logInfo___at___Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0(x_57, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_54);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
x_59 = !lean_is_exclusive(x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_58, 0);
lean_dec(x_60);
x_61 = lean_box(0);
lean_ctor_set(x_58, 0, x_61);
return x_58;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_58, 1);
lean_inc(x_62);
lean_dec(x_58);
x_63 = lean_box(0);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_free_object(x_6);
lean_dec(x_48);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
x_65 = lean_ctor_get(x_53, 0);
lean_inc(x_65);
lean_dec(x_53);
x_66 = lean_ctor_get(x_52, 1);
lean_inc(x_66);
lean_dec(x_52);
x_67 = lean_ctor_get(x_65, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_65, 1);
lean_inc(x_68);
lean_dec(x_65);
x_16 = x_68;
x_17 = x_67;
x_18 = x_11;
x_19 = x_12;
x_20 = x_13;
x_21 = x_14;
x_22 = x_66;
goto block_33;
}
}
else
{
uint8_t x_69; 
lean_free_object(x_6);
lean_dec(x_48);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
x_69 = !lean_is_exclusive(x_52);
if (x_69 == 0)
{
return x_52;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_52, 0);
x_71 = lean_ctor_get(x_52, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_52);
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
x_73 = lean_ctor_get(x_6, 0);
lean_inc(x_73);
lean_dec(x_6);
x_74 = lean_box(0);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_48);
x_75 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic(x_47, x_48, x_73, x_74, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_46);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_78 = lean_mk_string_unchecked("a proof", 7, 7);
x_79 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_79, 0, x_78);
x_80 = l_Lean_MessageData_ofFormat(x_79);
x_81 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg(x_80, x_48);
x_82 = l_Lean_logInfo___at___Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0(x_81, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_77);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
x_83 = lean_ctor_get(x_82, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_84 = x_82;
} else {
 lean_dec_ref(x_82);
 x_84 = lean_box(0);
}
x_85 = lean_box(0);
if (lean_is_scalar(x_84)) {
 x_86 = lean_alloc_ctor(0, 2, 0);
} else {
 x_86 = x_84;
}
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_83);
return x_86;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_48);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
x_87 = lean_ctor_get(x_76, 0);
lean_inc(x_87);
lean_dec(x_76);
x_88 = lean_ctor_get(x_75, 1);
lean_inc(x_88);
lean_dec(x_75);
x_89 = lean_ctor_get(x_87, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_87, 1);
lean_inc(x_90);
lean_dec(x_87);
x_16 = x_90;
x_17 = x_89;
x_18 = x_11;
x_19 = x_12;
x_20 = x_13;
x_21 = x_14;
x_22 = x_88;
goto block_33;
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_48);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
x_91 = lean_ctor_get(x_75, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_75, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_93 = x_75;
} else {
 lean_dec_ref(x_75);
 x_93 = lean_box(0);
}
if (lean_is_scalar(x_93)) {
 x_94 = lean_alloc_ctor(1, 2, 0);
} else {
 x_94 = x_93;
}
lean_ctor_set(x_94, 0, x_91);
lean_ctor_set(x_94, 1, x_92);
return x_94;
}
}
}
}
else
{
uint8_t x_95; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_95 = !lean_is_exclusive(x_41);
if (x_95 == 0)
{
return x_41;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_41, 0);
x_97 = lean_ctor_get(x_41, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_41);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
else
{
uint8_t x_99; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_99 = !lean_is_exclusive(x_37);
if (x_99 == 0)
{
return x_37;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_37, 0);
x_101 = lean_ctor_get(x_37, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_37);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
else
{
uint8_t x_103; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_103 = !lean_is_exclusive(x_34);
if (x_103 == 0)
{
return x_34;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_34, 0);
x_105 = lean_ctor_get(x_34, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_34);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
return x_106;
}
}
block_33:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_23 = lean_mk_string_unchecked("tactic", 6, 6);
x_24 = l_Lean_Name_mkStr1(x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_17);
x_26 = lean_box(0);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_16);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_30, 0, x_25);
lean_ctor_set(x_30, 1, x_26);
lean_ctor_set(x_30, 2, x_26);
lean_ctor_set(x_30, 3, x_27);
lean_ctor_set(x_30, 4, x_28);
lean_ctor_set(x_30, 5, x_29);
x_31 = lean_mk_string_unchecked("Try this: ", 10, 10);
x_32 = l_Lean_Meta_Tactic_TryThis_addSuggestion(x_1, x_30, x_5, x_31, x_26, x_18, x_19, x_20, x_21, x_22);
lean_dec(x_19);
lean_dec(x_18);
return x_32;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lam__0(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__0(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_24; 
x_11 = lean_array_uget(x_3, x_2);
x_12 = lean_box(0);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_array_uset(x_3, x_2, x_12);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_24 = l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax(x_13, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = lean_unbox(x_14);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_st_ref_get(x_7, x_27);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_ctor_get(x_6, 5);
lean_inc(x_30);
x_31 = lean_unbox(x_14);
lean_dec(x_14);
x_32 = l_Lean_SourceInfo_fromRef(x_30, x_31);
lean_dec(x_30);
x_33 = lean_mk_string_unchecked("Lean", 4, 4);
x_34 = lean_mk_string_unchecked("Parser", 6, 6);
x_35 = lean_mk_string_unchecked("Tactic", 6, 6);
x_36 = lean_mk_string_unchecked("rwRule", 6, 6);
x_37 = l_Lean_Name_mkStr4(x_33, x_34, x_35, x_36);
x_38 = lean_mk_string_unchecked("null", 4, 4);
x_39 = l_Lean_Name_mkStr1(x_38);
x_40 = l_Array_mkArray0(lean_box(0));
lean_inc(x_32);
x_41 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_41, 0, x_32);
lean_ctor_set(x_41, 1, x_39);
lean_ctor_set(x_41, 2, x_40);
x_42 = l_Lean_Syntax_node2(x_32, x_37, x_41, x_26);
x_16 = x_42;
x_17 = x_29;
goto block_23;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
lean_dec(x_14);
x_43 = lean_ctor_get(x_24, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_24, 1);
lean_inc(x_44);
lean_dec(x_24);
x_45 = lean_st_ref_get(x_7, x_44);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_47 = lean_ctor_get(x_45, 1);
x_48 = lean_ctor_get(x_45, 0);
lean_dec(x_48);
x_49 = lean_ctor_get(x_6, 5);
lean_inc(x_49);
x_50 = lean_box(0);
x_51 = lean_unbox(x_50);
x_52 = l_Lean_SourceInfo_fromRef(x_49, x_51);
lean_dec(x_49);
x_53 = lean_mk_string_unchecked("Lean", 4, 4);
x_54 = lean_mk_string_unchecked("Parser", 6, 6);
x_55 = lean_mk_string_unchecked("Tactic", 6, 6);
x_56 = lean_mk_string_unchecked("rwRule", 6, 6);
x_57 = l_Lean_Name_mkStr4(x_53, x_54, x_55, x_56);
x_58 = lean_mk_string_unchecked("null", 4, 4);
x_59 = l_Lean_Name_mkStr1(x_58);
x_60 = lean_mk_string_unchecked("patternIgnore", 13, 13);
x_61 = l_Lean_Name_mkStr1(x_60);
x_62 = lean_mk_string_unchecked("token", 5, 5);
x_63 = lean_mk_string_unchecked("← ", 4, 2);
x_64 = l_Lean_Name_mkStr2(x_62, x_63);
x_65 = lean_mk_string_unchecked("←", 3, 1);
lean_inc(x_52);
lean_ctor_set_tag(x_45, 2);
lean_ctor_set(x_45, 1, x_65);
lean_ctor_set(x_45, 0, x_52);
lean_inc(x_52);
x_66 = l_Lean_Syntax_node1(x_52, x_64, x_45);
lean_inc(x_52);
x_67 = l_Lean_Syntax_node1(x_52, x_61, x_66);
lean_inc(x_52);
x_68 = l_Lean_Syntax_node1(x_52, x_59, x_67);
x_69 = l_Lean_Syntax_node2(x_52, x_57, x_68, x_43);
x_16 = x_69;
x_17 = x_47;
goto block_23;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_70 = lean_ctor_get(x_45, 1);
lean_inc(x_70);
lean_dec(x_45);
x_71 = lean_ctor_get(x_6, 5);
lean_inc(x_71);
x_72 = lean_box(0);
x_73 = lean_unbox(x_72);
x_74 = l_Lean_SourceInfo_fromRef(x_71, x_73);
lean_dec(x_71);
x_75 = lean_mk_string_unchecked("Lean", 4, 4);
x_76 = lean_mk_string_unchecked("Parser", 6, 6);
x_77 = lean_mk_string_unchecked("Tactic", 6, 6);
x_78 = lean_mk_string_unchecked("rwRule", 6, 6);
x_79 = l_Lean_Name_mkStr4(x_75, x_76, x_77, x_78);
x_80 = lean_mk_string_unchecked("null", 4, 4);
x_81 = l_Lean_Name_mkStr1(x_80);
x_82 = lean_mk_string_unchecked("patternIgnore", 13, 13);
x_83 = l_Lean_Name_mkStr1(x_82);
x_84 = lean_mk_string_unchecked("token", 5, 5);
x_85 = lean_mk_string_unchecked("← ", 4, 2);
x_86 = l_Lean_Name_mkStr2(x_84, x_85);
x_87 = lean_mk_string_unchecked("←", 3, 1);
lean_inc(x_74);
x_88 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_88, 0, x_74);
lean_ctor_set(x_88, 1, x_87);
lean_inc(x_74);
x_89 = l_Lean_Syntax_node1(x_74, x_86, x_88);
lean_inc(x_74);
x_90 = l_Lean_Syntax_node1(x_74, x_83, x_89);
lean_inc(x_74);
x_91 = l_Lean_Syntax_node1(x_74, x_81, x_90);
x_92 = l_Lean_Syntax_node2(x_74, x_79, x_91, x_43);
x_16 = x_92;
x_17 = x_70;
goto block_23;
}
}
}
else
{
lean_dec(x_14);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_24, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_24, 1);
lean_inc(x_94);
lean_dec(x_24);
x_16 = x_93;
x_17 = x_94;
goto block_23;
}
else
{
uint8_t x_95; 
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_95 = !lean_is_exclusive(x_24);
if (x_95 == 0)
{
return x_24;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_24, 0);
x_97 = lean_ctor_get(x_24, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_24);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
block_23:
{
lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_usize_of_nat(x_18);
x_20 = lean_usize_add(x_2, x_19);
x_21 = lean_array_uset(x_15, x_2, x_16);
x_2 = x_20;
x_3 = x_21;
x_8 = x_17;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__1(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_23; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_6 = x_1;
} else {
 lean_dec_ref(x_1);
 x_6 = lean_box(0);
}
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_4, 1);
lean_inc(x_12);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_13 = x_4;
} else {
 lean_dec_ref(x_4);
 x_13 = lean_box(0);
}
x_23 = lean_unbox(x_12);
lean_dec(x_12);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_mk_string_unchecked("", 0, 0);
x_14 = x_24;
goto block_22;
}
else
{
lean_object* x_25; 
x_25 = lean_mk_string_unchecked("← ", 4, 2);
x_14 = x_25;
goto block_22;
}
block_10:
{
lean_object* x_8; 
if (lean_is_scalar(x_6)) {
 x_8 = lean_alloc_ctor(1, 2, 0);
} else {
 x_8 = x_6;
}
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_2);
x_1 = x_5;
x_2 = x_8;
goto _start;
}
block_22:
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = l_Lean_MessageData_ofFormat(x_15);
x_17 = l_Lean_Expr_isConst(x_11);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = l_Lean_MessageData_ofExpr(x_11);
if (lean_is_scalar(x_13)) {
 x_19 = lean_alloc_ctor(7, 2, 0);
} else {
 x_19 = x_13;
 lean_ctor_set_tag(x_19, 7);
}
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
x_7 = x_19;
goto block_10;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = l_Lean_MessageData_ofConst(x_11);
if (lean_is_scalar(x_13)) {
 x_21 = lean_alloc_ctor(7, 2, 0);
} else {
 x_21 = x_13;
 lean_ctor_set_tag(x_21, 7);
}
lean_ctor_set(x_21, 0, x_16);
lean_ctor_set(x_21, 1, x_20);
x_7 = x_21;
goto block_10;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; size_t x_145; lean_object* x_146; 
x_18 = lean_array_size(x_1);
x_19 = lean_unsigned_to_nat(0u);
x_145 = lean_usize_of_nat(x_19);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_146 = l_Array_mapMUnsafe_map___at___Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__0(x_18, x_145, x_1, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_222; lean_object* x_223; 
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
lean_dec(x_146);
x_149 = lean_mk_string_unchecked("Lean", 4, 4);
x_150 = lean_mk_string_unchecked("Parser", 6, 6);
x_151 = lean_mk_string_unchecked("Tactic", 6, 6);
x_152 = lean_mk_string_unchecked("rwRule", 6, 6);
lean_inc(x_151);
lean_inc(x_150);
lean_inc(x_149);
x_153 = l_Lean_Name_mkStr4(x_149, x_150, x_151, x_152);
x_154 = lean_box(0);
x_155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_154);
x_156 = lean_mk_string_unchecked(",", 1, 1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_226; 
x_226 = lean_box(0);
x_157 = x_226;
x_158 = x_148;
goto block_221;
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_227 = lean_ctor_get(x_4, 0);
lean_inc(x_227);
x_228 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_229 = l_Lean_PrettyPrinter_delab(x_227, x_228, x_5, x_6, x_7, x_8, x_148);
if (lean_obj_tag(x_229) == 0)
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; uint8_t x_233; 
x_230 = lean_ctor_get(x_229, 0);
lean_inc(x_230);
x_231 = lean_ctor_get(x_229, 1);
lean_inc(x_231);
lean_dec(x_229);
x_232 = lean_st_ref_get(x_8, x_231);
x_233 = !lean_is_exclusive(x_232);
if (x_233 == 0)
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; uint8_t x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_234 = lean_ctor_get(x_232, 1);
x_235 = lean_ctor_get(x_232, 0);
lean_dec(x_235);
x_236 = lean_ctor_get(x_7, 5);
lean_inc(x_236);
x_237 = lean_box(0);
x_238 = lean_unbox(x_237);
x_239 = l_Lean_SourceInfo_fromRef(x_236, x_238);
lean_dec(x_236);
x_240 = lean_mk_string_unchecked("location", 8, 8);
lean_inc(x_151);
lean_inc(x_150);
lean_inc(x_149);
x_241 = l_Lean_Name_mkStr4(x_149, x_150, x_151, x_240);
x_242 = lean_mk_string_unchecked("at", 2, 2);
lean_inc(x_239);
lean_ctor_set_tag(x_232, 2);
lean_ctor_set(x_232, 1, x_242);
lean_ctor_set(x_232, 0, x_239);
x_243 = lean_mk_string_unchecked("locationHyp", 11, 11);
lean_inc(x_151);
lean_inc(x_150);
lean_inc(x_149);
x_244 = l_Lean_Name_mkStr4(x_149, x_150, x_151, x_243);
x_245 = lean_mk_string_unchecked("null", 4, 4);
x_246 = l_Lean_Name_mkStr1(x_245);
lean_inc(x_239);
x_247 = l_Lean_Syntax_node1(x_239, x_246, x_230);
lean_inc(x_239);
x_248 = l_Lean_Syntax_node1(x_239, x_244, x_247);
x_249 = l_Lean_Syntax_node2(x_239, x_241, x_232, x_248);
x_222 = x_249;
x_223 = x_234;
goto block_225;
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; uint8_t x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_250 = lean_ctor_get(x_232, 1);
lean_inc(x_250);
lean_dec(x_232);
x_251 = lean_ctor_get(x_7, 5);
lean_inc(x_251);
x_252 = lean_box(0);
x_253 = lean_unbox(x_252);
x_254 = l_Lean_SourceInfo_fromRef(x_251, x_253);
lean_dec(x_251);
x_255 = lean_mk_string_unchecked("location", 8, 8);
lean_inc(x_151);
lean_inc(x_150);
lean_inc(x_149);
x_256 = l_Lean_Name_mkStr4(x_149, x_150, x_151, x_255);
x_257 = lean_mk_string_unchecked("at", 2, 2);
lean_inc(x_254);
x_258 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_258, 0, x_254);
lean_ctor_set(x_258, 1, x_257);
x_259 = lean_mk_string_unchecked("locationHyp", 11, 11);
lean_inc(x_151);
lean_inc(x_150);
lean_inc(x_149);
x_260 = l_Lean_Name_mkStr4(x_149, x_150, x_151, x_259);
x_261 = lean_mk_string_unchecked("null", 4, 4);
x_262 = l_Lean_Name_mkStr1(x_261);
lean_inc(x_254);
x_263 = l_Lean_Syntax_node1(x_254, x_262, x_230);
lean_inc(x_254);
x_264 = l_Lean_Syntax_node1(x_254, x_260, x_263);
x_265 = l_Lean_Syntax_node2(x_254, x_256, x_258, x_264);
x_222 = x_265;
x_223 = x_250;
goto block_225;
}
}
else
{
if (lean_obj_tag(x_229) == 0)
{
lean_object* x_266; lean_object* x_267; 
x_266 = lean_ctor_get(x_229, 0);
lean_inc(x_266);
x_267 = lean_ctor_get(x_229, 1);
lean_inc(x_267);
lean_dec(x_229);
x_222 = x_266;
x_223 = x_267;
goto block_225;
}
else
{
uint8_t x_268; 
lean_dec(x_156);
lean_dec(x_155);
lean_dec(x_151);
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_147);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_268 = !lean_is_exclusive(x_229);
if (x_268 == 0)
{
return x_229;
}
else
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; 
x_269 = lean_ctor_get(x_229, 0);
x_270 = lean_ctor_get(x_229, 1);
lean_inc(x_270);
lean_inc(x_269);
lean_dec(x_229);
x_271 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_271, 0, x_269);
lean_ctor_set(x_271, 1, x_270);
return x_271;
}
}
}
}
block_221:
{
lean_object* x_159; uint8_t x_160; 
x_159 = lean_st_ref_get(x_8, x_158);
x_160 = !lean_is_exclusive(x_159);
if (x_160 == 0)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; uint8_t x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_161 = lean_ctor_get(x_159, 1);
x_162 = lean_ctor_get(x_159, 0);
lean_dec(x_162);
x_163 = lean_ctor_get(x_7, 5);
lean_inc(x_163);
x_164 = lean_box(0);
x_165 = lean_unbox(x_164);
x_166 = l_Lean_SourceInfo_fromRef(x_163, x_165);
lean_dec(x_163);
x_167 = lean_mk_string_unchecked("rwSeq", 5, 5);
lean_inc(x_151);
lean_inc(x_150);
lean_inc(x_149);
x_168 = l_Lean_Name_mkStr4(x_149, x_150, x_151, x_167);
x_169 = lean_mk_string_unchecked("rw", 2, 2);
lean_inc(x_166);
lean_ctor_set_tag(x_159, 2);
lean_ctor_set(x_159, 1, x_169);
lean_ctor_set(x_159, 0, x_166);
x_170 = lean_mk_string_unchecked("optConfig", 9, 9);
lean_inc(x_151);
lean_inc(x_150);
lean_inc(x_149);
x_171 = l_Lean_Name_mkStr4(x_149, x_150, x_151, x_170);
x_172 = lean_mk_string_unchecked("null", 4, 4);
x_173 = l_Lean_Name_mkStr1(x_172);
x_174 = l_Array_mkArray0(lean_box(0));
lean_inc(x_174);
lean_inc(x_173);
lean_inc(x_166);
x_175 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_175, 0, x_166);
lean_ctor_set(x_175, 1, x_173);
lean_ctor_set(x_175, 2, x_174);
lean_inc(x_166);
x_176 = l_Lean_Syntax_node1(x_166, x_171, x_175);
x_177 = lean_mk_string_unchecked("rwRuleSeq", 9, 9);
x_178 = l_Lean_Name_mkStr4(x_149, x_150, x_151, x_177);
x_179 = lean_mk_string_unchecked("[", 1, 1);
lean_inc(x_166);
x_180 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_180, 0, x_166);
lean_ctor_set(x_180, 1, x_179);
x_181 = l_Lean_Syntax_TSepArray_ofElems(x_155, x_156, x_147);
lean_dec(x_147);
lean_dec(x_155);
lean_inc(x_174);
x_182 = l_Array_append(lean_box(0), x_174, x_181);
lean_dec(x_181);
lean_inc(x_173);
lean_inc(x_166);
x_183 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_183, 0, x_166);
lean_ctor_set(x_183, 1, x_173);
lean_ctor_set(x_183, 2, x_182);
x_184 = lean_mk_string_unchecked("]", 1, 1);
lean_inc(x_166);
x_185 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_185, 0, x_166);
lean_ctor_set(x_185, 1, x_184);
lean_inc(x_166);
x_186 = l_Lean_Syntax_node3(x_166, x_178, x_180, x_183, x_185);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_187; 
x_187 = l_Array_empty(lean_box(0));
x_107 = x_186;
x_108 = x_173;
x_109 = x_168;
x_110 = x_166;
x_111 = x_161;
x_112 = x_176;
x_113 = x_159;
x_114 = x_174;
x_115 = x_187;
goto block_144;
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_188 = lean_ctor_get(x_157, 0);
lean_inc(x_188);
lean_dec(x_157);
x_189 = l_Array_empty(lean_box(0));
x_190 = lean_array_push(x_189, x_188);
x_107 = x_186;
x_108 = x_173;
x_109 = x_168;
x_110 = x_166;
x_111 = x_161;
x_112 = x_176;
x_113 = x_159;
x_114 = x_174;
x_115 = x_190;
goto block_144;
}
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; uint8_t x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_191 = lean_ctor_get(x_159, 1);
lean_inc(x_191);
lean_dec(x_159);
x_192 = lean_ctor_get(x_7, 5);
lean_inc(x_192);
x_193 = lean_box(0);
x_194 = lean_unbox(x_193);
x_195 = l_Lean_SourceInfo_fromRef(x_192, x_194);
lean_dec(x_192);
x_196 = lean_mk_string_unchecked("rwSeq", 5, 5);
lean_inc(x_151);
lean_inc(x_150);
lean_inc(x_149);
x_197 = l_Lean_Name_mkStr4(x_149, x_150, x_151, x_196);
x_198 = lean_mk_string_unchecked("rw", 2, 2);
lean_inc(x_195);
x_199 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_199, 0, x_195);
lean_ctor_set(x_199, 1, x_198);
x_200 = lean_mk_string_unchecked("optConfig", 9, 9);
lean_inc(x_151);
lean_inc(x_150);
lean_inc(x_149);
x_201 = l_Lean_Name_mkStr4(x_149, x_150, x_151, x_200);
x_202 = lean_mk_string_unchecked("null", 4, 4);
x_203 = l_Lean_Name_mkStr1(x_202);
x_204 = l_Array_mkArray0(lean_box(0));
lean_inc(x_204);
lean_inc(x_203);
lean_inc(x_195);
x_205 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_205, 0, x_195);
lean_ctor_set(x_205, 1, x_203);
lean_ctor_set(x_205, 2, x_204);
lean_inc(x_195);
x_206 = l_Lean_Syntax_node1(x_195, x_201, x_205);
x_207 = lean_mk_string_unchecked("rwRuleSeq", 9, 9);
x_208 = l_Lean_Name_mkStr4(x_149, x_150, x_151, x_207);
x_209 = lean_mk_string_unchecked("[", 1, 1);
lean_inc(x_195);
x_210 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_210, 0, x_195);
lean_ctor_set(x_210, 1, x_209);
x_211 = l_Lean_Syntax_TSepArray_ofElems(x_155, x_156, x_147);
lean_dec(x_147);
lean_dec(x_155);
lean_inc(x_204);
x_212 = l_Array_append(lean_box(0), x_204, x_211);
lean_dec(x_211);
lean_inc(x_203);
lean_inc(x_195);
x_213 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_213, 0, x_195);
lean_ctor_set(x_213, 1, x_203);
lean_ctor_set(x_213, 2, x_212);
x_214 = lean_mk_string_unchecked("]", 1, 1);
lean_inc(x_195);
x_215 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_215, 0, x_195);
lean_ctor_set(x_215, 1, x_214);
lean_inc(x_195);
x_216 = l_Lean_Syntax_node3(x_195, x_208, x_210, x_213, x_215);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_217; 
x_217 = l_Array_empty(lean_box(0));
x_107 = x_216;
x_108 = x_203;
x_109 = x_197;
x_110 = x_195;
x_111 = x_191;
x_112 = x_206;
x_113 = x_199;
x_114 = x_204;
x_115 = x_217;
goto block_144;
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_218 = lean_ctor_get(x_157, 0);
lean_inc(x_218);
lean_dec(x_157);
x_219 = l_Array_empty(lean_box(0));
x_220 = lean_array_push(x_219, x_218);
x_107 = x_216;
x_108 = x_203;
x_109 = x_197;
x_110 = x_195;
x_111 = x_191;
x_112 = x_206;
x_113 = x_199;
x_114 = x_204;
x_115 = x_220;
goto block_144;
}
}
}
block_225:
{
lean_object* x_224; 
x_224 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_224, 0, x_222);
x_157 = x_224;
x_158 = x_223;
goto block_221;
}
}
else
{
uint8_t x_272; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_272 = !lean_is_exclusive(x_146);
if (x_272 == 0)
{
return x_146;
}
else
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; 
x_273 = lean_ctor_get(x_146, 0);
x_274 = lean_ctor_get(x_146, 1);
lean_inc(x_274);
lean_inc(x_273);
lean_dec(x_146);
x_275 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_275, 0, x_273);
lean_ctor_set(x_275, 1, x_274);
return x_275;
}
}
block_17:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
block_106:
{
lean_object* x_23; 
x_23 = l_Lean_addMessageContextFull___at___Lean_Meta_recordSynthPendingFailure_spec__3(x_22, x_5, x_6, x_7, x_8, x_20);
switch (lean_obj_tag(x_2)) {
case 0:
{
uint8_t x_24; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_23, 1);
x_27 = lean_mk_string_unchecked("\n-- no goals", 12, 12);
x_28 = l_Lean_stringToMessageData(x_27);
lean_ctor_set(x_23, 1, x_27);
lean_ctor_set(x_23, 0, x_28);
x_10 = x_21;
x_11 = x_25;
x_12 = x_23;
x_13 = x_26;
goto block_17;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_23, 0);
x_30 = lean_ctor_get(x_23, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_23);
x_31 = lean_mk_string_unchecked("\n-- no goals", 12, 12);
x_32 = l_Lean_stringToMessageData(x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
x_10 = x_21;
x_11 = x_29;
x_12 = x_33;
x_13 = x_30;
goto block_17;
}
}
case 1:
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_23);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_35 = lean_ctor_get(x_23, 0);
x_36 = lean_ctor_get(x_23, 1);
x_37 = lean_ctor_get(x_2, 0);
lean_inc(x_37);
lean_dec(x_2);
x_38 = lean_mk_string_unchecked("\n-- ", 4, 4);
x_39 = l_Lean_stringToMessageData(x_38);
lean_inc(x_37);
x_40 = l_Lean_MessageData_ofExpr(x_37);
lean_ctor_set_tag(x_23, 7);
lean_ctor_set(x_23, 1, x_40);
lean_ctor_set(x_23, 0, x_39);
x_41 = lean_mk_string_unchecked("", 0, 0);
x_42 = l_Lean_stringToMessageData(x_41);
lean_dec(x_41);
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_23);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Lean_addMessageContextFull___at___Lean_Meta_recordSynthPendingFailure_spec__3(x_43, x_5, x_6, x_7, x_8, x_36);
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_44, 0);
x_47 = lean_ctor_get(x_44, 1);
x_48 = l_Lean_PrettyPrinter_ppExpr(x_37, x_5, x_6, x_7, x_8, x_47);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_unsigned_to_nat(120u);
x_52 = lean_format_pretty(x_49, x_51, x_19, x_19);
x_53 = lean_string_append(x_38, x_52);
lean_dec(x_52);
lean_ctor_set(x_44, 1, x_53);
x_10 = x_21;
x_11 = x_35;
x_12 = x_44;
x_13 = x_50;
goto block_17;
}
else
{
uint8_t x_54; 
lean_free_object(x_44);
lean_dec(x_46);
lean_dec(x_38);
lean_dec(x_35);
lean_dec(x_21);
x_54 = !lean_is_exclusive(x_48);
if (x_54 == 0)
{
return x_48;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_48, 0);
x_56 = lean_ctor_get(x_48, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_48);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_44, 0);
x_59 = lean_ctor_get(x_44, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_44);
x_60 = l_Lean_PrettyPrinter_ppExpr(x_37, x_5, x_6, x_7, x_8, x_59);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = lean_unsigned_to_nat(120u);
x_64 = lean_format_pretty(x_61, x_63, x_19, x_19);
x_65 = lean_string_append(x_38, x_64);
lean_dec(x_64);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_58);
lean_ctor_set(x_66, 1, x_65);
x_10 = x_21;
x_11 = x_35;
x_12 = x_66;
x_13 = x_62;
goto block_17;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_58);
lean_dec(x_38);
lean_dec(x_35);
lean_dec(x_21);
x_67 = lean_ctor_get(x_60, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_60, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_69 = x_60;
} else {
 lean_dec_ref(x_60);
 x_69 = lean_box(0);
}
if (lean_is_scalar(x_69)) {
 x_70 = lean_alloc_ctor(1, 2, 0);
} else {
 x_70 = x_69;
}
lean_ctor_set(x_70, 0, x_67);
lean_ctor_set(x_70, 1, x_68);
return x_70;
}
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_71 = lean_ctor_get(x_23, 0);
x_72 = lean_ctor_get(x_23, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_23);
x_73 = lean_ctor_get(x_2, 0);
lean_inc(x_73);
lean_dec(x_2);
x_74 = lean_mk_string_unchecked("\n-- ", 4, 4);
x_75 = l_Lean_stringToMessageData(x_74);
lean_inc(x_73);
x_76 = l_Lean_MessageData_ofExpr(x_73);
x_77 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
x_78 = lean_mk_string_unchecked("", 0, 0);
x_79 = l_Lean_stringToMessageData(x_78);
lean_dec(x_78);
x_80 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_79);
x_81 = l_Lean_addMessageContextFull___at___Lean_Meta_recordSynthPendingFailure_spec__3(x_80, x_5, x_6, x_7, x_8, x_72);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_84 = x_81;
} else {
 lean_dec_ref(x_81);
 x_84 = lean_box(0);
}
x_85 = l_Lean_PrettyPrinter_ppExpr(x_73, x_5, x_6, x_7, x_8, x_83);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
x_88 = lean_unsigned_to_nat(120u);
x_89 = lean_format_pretty(x_86, x_88, x_19, x_19);
x_90 = lean_string_append(x_74, x_89);
lean_dec(x_89);
if (lean_is_scalar(x_84)) {
 x_91 = lean_alloc_ctor(0, 2, 0);
} else {
 x_91 = x_84;
}
lean_ctor_set(x_91, 0, x_82);
lean_ctor_set(x_91, 1, x_90);
x_10 = x_21;
x_11 = x_71;
x_12 = x_91;
x_13 = x_87;
goto block_17;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_84);
lean_dec(x_82);
lean_dec(x_74);
lean_dec(x_71);
lean_dec(x_21);
x_92 = lean_ctor_get(x_85, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_85, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_94 = x_85;
} else {
 lean_dec_ref(x_85);
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
default: 
{
uint8_t x_96; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_96 = !lean_is_exclusive(x_23);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_97 = lean_ctor_get(x_23, 0);
x_98 = lean_ctor_get(x_23, 1);
x_99 = lean_mk_string_unchecked("", 0, 0);
x_100 = l_Lean_stringToMessageData(x_99);
lean_ctor_set(x_23, 1, x_99);
lean_ctor_set(x_23, 0, x_100);
x_10 = x_21;
x_11 = x_97;
x_12 = x_23;
x_13 = x_98;
goto block_17;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_101 = lean_ctor_get(x_23, 0);
x_102 = lean_ctor_get(x_23, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_23);
x_103 = lean_mk_string_unchecked("", 0, 0);
x_104 = l_Lean_stringToMessageData(x_103);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_103);
x_10 = x_21;
x_11 = x_101;
x_12 = x_105;
x_13 = x_102;
goto block_17;
}
}
}
}
block_144:
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_116 = l_Array_append(lean_box(0), x_114, x_115);
lean_dec(x_115);
lean_inc(x_110);
x_117 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_117, 0, x_110);
lean_ctor_set(x_117, 1, x_108);
lean_ctor_set(x_117, 2, x_116);
x_118 = l_Lean_Syntax_node4(x_110, x_109, x_113, x_112, x_107, x_117);
x_119 = lean_box(0);
x_120 = l_List_mapTR_loop___at___Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__1(x_3, x_119);
x_121 = lean_mk_string_unchecked(", ", 2, 2);
x_122 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_122, 0, x_121);
x_123 = l_Lean_MessageData_ofFormat(x_122);
x_124 = l_Lean_MessageData_joinSep(x_120, x_123);
x_125 = l_Lean_MessageData_sbracket(x_124);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_126 = lean_mk_string_unchecked("rw ", 3, 3);
x_127 = l_Lean_stringToMessageData(x_126);
lean_dec(x_126);
x_128 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_125);
x_129 = lean_mk_string_unchecked("", 0, 0);
x_130 = l_Lean_stringToMessageData(x_129);
lean_dec(x_129);
x_131 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_131, 0, x_128);
lean_ctor_set(x_131, 1, x_130);
x_20 = x_111;
x_21 = x_118;
x_22 = x_131;
goto block_106;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_132 = lean_ctor_get(x_4, 0);
lean_inc(x_132);
lean_dec(x_4);
x_133 = lean_mk_string_unchecked("rw ", 3, 3);
x_134 = l_Lean_stringToMessageData(x_133);
lean_dec(x_133);
x_135 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_125);
x_136 = lean_mk_string_unchecked(" at ", 4, 4);
x_137 = l_Lean_stringToMessageData(x_136);
lean_dec(x_136);
x_138 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_138, 0, x_135);
lean_ctor_set(x_138, 1, x_137);
x_139 = l_Lean_MessageData_ofExpr(x_132);
x_140 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
x_141 = lean_mk_string_unchecked("", 0, 0);
x_142 = l_Lean_stringToMessageData(x_141);
lean_dec(x_141);
x_143 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_143, 0, x_140);
lean_ctor_set(x_143, 1, x_142);
x_20 = x_111;
x_21 = x_118;
x_22 = x_143;
goto block_106;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_inc(x_2);
x_16 = lean_array_mk(x_2);
lean_inc(x_3);
x_17 = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lam__0), 9, 4);
lean_closure_set(x_17, 0, x_16);
lean_closure_set(x_17, 1, x_3);
lean_closure_set(x_17, 2, x_2);
lean_closure_set(x_17, 3, x_4);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_18 = l_Lean_Meta_withExposedNames___redArg(x_17, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_dec(x_18);
x_23 = lean_ctor_get(x_19, 0);
lean_inc(x_23);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_24 = x_19;
} else {
 lean_dec_ref(x_19);
 x_24 = lean_box(0);
}
x_25 = lean_ctor_get(x_20, 0);
lean_inc(x_25);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_26 = x_20;
} else {
 lean_dec_ref(x_20);
 x_26 = lean_box(0);
}
x_27 = lean_ctor_get(x_21, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_21, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_29 = x_21;
} else {
 lean_dec_ref(x_21);
 x_29 = lean_box(0);
}
if (lean_obj_tag(x_6) == 0)
{
lean_dec(x_24);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
x_30 = x_23;
x_31 = x_25;
x_32 = x_11;
x_33 = x_12;
x_34 = x_13;
x_35 = x_14;
x_36 = x_22;
goto block_49;
}
else
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_6);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_6, 0);
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_83; 
x_83 = lean_ctor_get(x_3, 0);
lean_inc(x_83);
lean_dec(x_3);
lean_ctor_set(x_6, 0, x_83);
x_52 = x_6;
goto block_82;
}
else
{
lean_object* x_84; 
lean_free_object(x_6);
lean_dec(x_3);
x_84 = lean_box(0);
x_52 = x_84;
goto block_82;
}
block_82:
{
lean_object* x_53; 
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_25);
x_53 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic(x_23, x_25, x_51, x_52, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_22);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_26);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_mk_string_unchecked("(expose_names; ", 15, 15);
x_57 = l_Lean_stringToMessageData(x_56);
lean_dec(x_56);
if (lean_is_scalar(x_24)) {
 x_58 = lean_alloc_ctor(7, 2, 0);
} else {
 x_58 = x_24;
 lean_ctor_set_tag(x_58, 7);
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_25);
x_59 = lean_mk_string_unchecked(")", 1, 1);
x_60 = l_Lean_stringToMessageData(x_59);
lean_dec(x_59);
x_61 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_mk_string_unchecked("an applicable rewrite lemma", 27, 27);
x_63 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_63, 0, x_62);
x_64 = l_Lean_MessageData_ofFormat(x_63);
x_65 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_65, 0, x_61);
lean_ctor_set(x_65, 1, x_27);
x_66 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg(x_64, x_65);
x_67 = l_Lean_logInfo___at___Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0(x_66, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_55);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
x_68 = !lean_is_exclusive(x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_67, 0);
lean_dec(x_69);
x_70 = lean_box(0);
lean_ctor_set(x_67, 0, x_70);
return x_67;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_67, 1);
lean_inc(x_71);
lean_dec(x_67);
x_72 = lean_box(0);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_71);
return x_73;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
x_74 = lean_ctor_get(x_54, 0);
lean_inc(x_74);
lean_dec(x_54);
x_75 = lean_ctor_get(x_53, 1);
lean_inc(x_75);
lean_dec(x_53);
x_76 = lean_ctor_get(x_74, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_74, 1);
lean_inc(x_77);
lean_dec(x_74);
x_30 = x_76;
x_31 = x_77;
x_32 = x_11;
x_33 = x_12;
x_34 = x_13;
x_35 = x_14;
x_36 = x_75;
goto block_49;
}
}
else
{
uint8_t x_78; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
x_78 = !lean_is_exclusive(x_53);
if (x_78 == 0)
{
return x_53;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_53, 0);
x_80 = lean_ctor_get(x_53, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_53);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
}
else
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_6, 0);
lean_inc(x_85);
lean_dec(x_6);
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_115; lean_object* x_116; 
x_115 = lean_ctor_get(x_3, 0);
lean_inc(x_115);
lean_dec(x_3);
x_116 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_116, 0, x_115);
x_86 = x_116;
goto block_114;
}
else
{
lean_object* x_117; 
lean_dec(x_3);
x_117 = lean_box(0);
x_86 = x_117;
goto block_114;
}
block_114:
{
lean_object* x_87; 
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_25);
x_87 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic(x_23, x_25, x_85, x_86, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_22);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_26);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
x_90 = lean_mk_string_unchecked("(expose_names; ", 15, 15);
x_91 = l_Lean_stringToMessageData(x_90);
lean_dec(x_90);
if (lean_is_scalar(x_24)) {
 x_92 = lean_alloc_ctor(7, 2, 0);
} else {
 x_92 = x_24;
 lean_ctor_set_tag(x_92, 7);
}
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_25);
x_93 = lean_mk_string_unchecked(")", 1, 1);
x_94 = l_Lean_stringToMessageData(x_93);
lean_dec(x_93);
x_95 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_95, 0, x_92);
lean_ctor_set(x_95, 1, x_94);
x_96 = lean_mk_string_unchecked("an applicable rewrite lemma", 27, 27);
x_97 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_97, 0, x_96);
x_98 = l_Lean_MessageData_ofFormat(x_97);
x_99 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_99, 0, x_95);
lean_ctor_set(x_99, 1, x_27);
x_100 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg(x_98, x_99);
x_101 = l_Lean_logInfo___at___Lean_Meta_Tactic_TryThis_addExactSuggestion_spec__0(x_100, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_89);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
x_102 = lean_ctor_get(x_101, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_103 = x_101;
} else {
 lean_dec_ref(x_101);
 x_103 = lean_box(0);
}
x_104 = lean_box(0);
if (lean_is_scalar(x_103)) {
 x_105 = lean_alloc_ctor(0, 2, 0);
} else {
 x_105 = x_103;
}
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_102);
return x_105;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
x_106 = lean_ctor_get(x_88, 0);
lean_inc(x_106);
lean_dec(x_88);
x_107 = lean_ctor_get(x_87, 1);
lean_inc(x_107);
lean_dec(x_87);
x_108 = lean_ctor_get(x_106, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_106, 1);
lean_inc(x_109);
lean_dec(x_106);
x_30 = x_108;
x_31 = x_109;
x_32 = x_11;
x_33 = x_12;
x_34 = x_13;
x_35 = x_14;
x_36 = x_107;
goto block_49;
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
x_110 = lean_ctor_get(x_87, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_87, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_112 = x_87;
} else {
 lean_dec_ref(x_87);
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
block_49:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_37 = lean_mk_string_unchecked("tactic", 6, 6);
x_38 = l_Lean_Name_mkStr1(x_37);
if (lean_is_scalar(x_29)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_29;
}
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_30);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_28);
x_42 = lean_box(0);
if (lean_is_scalar(x_26)) {
 x_43 = lean_alloc_ctor(7, 2, 0);
} else {
 x_43 = x_26;
 lean_ctor_set_tag(x_43, 7);
}
lean_ctor_set(x_43, 0, x_31);
lean_ctor_set(x_43, 1, x_27);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_46, 0, x_39);
lean_ctor_set(x_46, 1, x_40);
lean_ctor_set(x_46, 2, x_41);
lean_ctor_set(x_46, 3, x_42);
lean_ctor_set(x_46, 4, x_44);
lean_ctor_set(x_46, 5, x_45);
x_47 = lean_mk_string_unchecked("Try this: ", 10, 10);
x_48 = l_Lean_Meta_Tactic_TryThis_addSuggestion(x_1, x_46, x_5, x_47, x_40, x_32, x_33, x_34, x_35, x_36);
lean_dec(x_33);
lean_dec(x_32);
return x_48;
}
}
else
{
uint8_t x_118; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_118 = !lean_is_exclusive(x_18);
if (x_118 == 0)
{
return x_18;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_18, 0);
x_120 = lean_ctor_get(x_18, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_18);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
return x_121;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = l_Array_mapMUnsafe_map___at___Lean_Meta_Tactic_TryThis_addRewriteSuggestion_spec__0(x_9, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
return x_16;
}
}
lean_object* initialize_Lean_Server_CodeActions(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Widget_UserWidget(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Json_Elab(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Lsp_Utf16(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_CollectFVars(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_ExposeNames(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_TryThis(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Server_CodeActions(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Widget_UserWidget(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Json_Elab(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp_Utf16(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_CollectFVars(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_ExposeNames(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Tactic_TryThis_tryThisWidget = _init_l_Lean_Meta_Tactic_TryThis_tryThisWidget();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_tryThisWidget);
if (builtin) {res = l___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisWidget__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Meta_Tactic_TryThis_instImpl____x40_Lean_Meta_Tactic_TryThis___hyg_52_ = _init_l_Lean_Meta_Tactic_TryThis_instImpl____x40_Lean_Meta_Tactic_TryThis___hyg_52_();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_instImpl____x40_Lean_Meta_Tactic_TryThis___hyg_52_);
l_Lean_Meta_Tactic_TryThis_instTypeNameTryThisInfo = _init_l_Lean_Meta_Tactic_TryThis_instTypeNameTryThisInfo();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_instTypeNameTryThisInfo);
if (builtin) {res = l___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisProvider__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}res = l_Lean_Meta_Tactic_TryThis_initFn____x40_Lean_Meta_Tactic_TryThis___hyg_609_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Tactic_TryThis_format_inputWidth = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_format_inputWidth);
lean_dec_ref(res);
l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestionText = _init_l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestionText();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestionText);
l_Lean_Meta_Tactic_TryThis_instToMessageDataSuggestionText = _init_l_Lean_Meta_Tactic_TryThis_instToMessageDataSuggestionText();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_instToMessageDataSuggestionText);
l_Lean_Meta_Tactic_TryThis_instCoeStringSuggestionText = _init_l_Lean_Meta_Tactic_TryThis_instCoeStringSuggestionText();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_instCoeStringSuggestionText);
l_Lean_Meta_Tactic_TryThis_instSuggestionStyleInhabited = _init_l_Lean_Meta_Tactic_TryThis_instSuggestionStyleInhabited();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_instSuggestionStyleInhabited);
l_Lean_Meta_Tactic_TryThis_instSuggestionStyleToJson = _init_l_Lean_Meta_Tactic_TryThis_instSuggestionStyleToJson();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_instSuggestionStyleToJson);
l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success = _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success);
l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis = _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis);
l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible = _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible);
l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestion = _init_l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestion();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestion);
l_Lean_Meta_Tactic_TryThis_instToMessageDataSuggestion = _init_l_Lean_Meta_Tactic_TryThis_instToMessageDataSuggestion();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_instToMessageDataSuggestion);
l_Lean_Meta_Tactic_TryThis_instCoeSuggestionTextSuggestion = _init_l_Lean_Meta_Tactic_TryThis_instCoeSuggestionTextSuggestion();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_instCoeSuggestionTextSuggestion);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
