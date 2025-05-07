// Lean compiler output
// Module: Lean.Elab.Syntax
// Imports: Lean.Elab.Command Lean.Parser.Syntax Lean.Elab.Util
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
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSyntax___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkNameLit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabDeclareSyntaxCat___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Command_isLocalAttrKind(lean_object*);
lean_object* l_Lean_addMessageContextFull___at___Lean_Meta_recordSynthPendingFailure_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr_processAlias(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Elab_Term_toParserDescr_processAlias_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkNameFromParserSyntax___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Command_elabSyntax_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Term_withNotFirst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_evalPrec(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandOptPrecedence(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandNoKindMacroRulesAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getQuotContent(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSyntaxAbbrev___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr_processSepBy1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getScope___redArg(lean_object*, lean_object*);
lean_object* lean_name_append_after(lean_object*, lean_object*);
uint8_t l_Array_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0_spec__5___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Command_mkNameFromParserSyntax_visit_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr_processSepBy(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getString(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Term_toParserDescr_isValidAtom(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_isAtomLikeSyntax(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Term_markAsTrailingParser(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_toParserDescr_processAlias_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Lean_Elab_Term_toParserDescr_processSeq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isStr(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___Lean_Elab_Command_resolveSyntaxKind_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_____private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_resolveSyntaxKind___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Array_eraseIdxIfInBounds___redArg(lean_object*, lean_object*);
lean_object* l_instMonadEIO___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_mapAux___at___Lean_Elab_Command_mkNameFromParserSyntax_visit_spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabCommand(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_toParserDescr_processAlias_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_getParserAliasInfo(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_inferMacroRulesAltKind(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_checkLeftRec___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSyntaxAbbrev(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Lean_Elab_Term_toParserDescr_processSeq_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_registerParserCategory(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr_ensureNoPrec___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSyntax___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_strLitToPattern___boxed(lean_object*, lean_object*, lean_object*);
extern uint32_t l_Lean_idBeginEscape;
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isTracingEnabledFor___at___Lean_withTraceNode___at___Lean_Elab_Command_runLinters_spec__6_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkNameFromParserSyntax(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_liftExcept___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_toParserDescr_processAlias_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabParserName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_String_anyAux___at___addParenHeuristic_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Elab_Term_toParserDescr_processAlias_spec__0___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_unzip___redArg(lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_instInhabitedTSyntax(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_inferMacroRulesAltKind___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getNumArgs(lean_object*);
lean_object* l_Lean_Parser_resolveParserName(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Term_withNotFirst___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_ensureUnaryOutput(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Elab_Term_toParserDescr_processAlias_spec__0___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr_processSepBy1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkNameFromParserSyntax_visit(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Array_mkArray1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Command_mkNameFromParserSyntax_visit_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr_process(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Term_toParserDescr_processAlias_spec__1(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Elab_expandMacroImpl_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Term_withNotFirst___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Lean_Elab_Term_toParserDescr_processSeq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t l_Char_toUpper(uint32_t);
lean_object* l_Lean_ResolveName_resolveNamespace(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_toParserDescr_processAlias_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Term_markAsTrailingParser___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__4___redArg(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabSyntaxAbbrev__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind___at___Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___Lean_Elab_Command_resolveSyntaxKind_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0___redArg___lam__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_initFn____x40_Lean_Elab_Syntax___hyg_11805_(lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
uint32_t lean_uint32_of_nat(lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Term_withNestedParser(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_addAliasInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkStrLit(lean_object*, lean_object*);
lean_object* l_Lean_Parser_ensureBinaryParserAlias(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr_processNonReserved___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getRef(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandNoKindMacroRulesAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_getPrefix(lean_object*);
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_quoteNameMk(lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr_processNonReserved(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_evalOptPrio___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabSyntax_declRange__1(lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_____private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isStrLit_x3f(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr_processNonReserved___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ensureConstantParserAlias(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getCurrMacroScope(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_isAtomLikeSyntax___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_toParserDescr_processAlias_spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_addMacroScopeIfLocal___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Term_withNestedParser___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSyntax(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_toParserDescr_processAlias_spec__5___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Term_withNotFirst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_resolveSyntaxKind(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabDeclareSyntaxCat(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabDeclareSyntaxCat__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___Lean_Elab_Command_resolveSyntaxKind_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_checkLeftRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_syntax_ident(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr_processAtom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSyntax___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Parser_isParserCategory(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabSyntaxAbbrev_declRange__1(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Command_expandNoKindMacroRulesAux_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_setEnv___at___Lean_withEnv___at___Lean_Elab_Command_runLintersAsync_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Term_markAsTrailingParser___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr_processParserCategory___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_addMacroScopeIfLocal___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Command_expandNoKindMacroRulesAux_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr_processParserCategory(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isLetterLike(uint32_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSyntaxAbbrev___lam__0___boxed(lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_addMacroScopeIfLocal___at___Lean_Elab_Command_elabSyntax_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkNameFromParserSyntax_appendCatName___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Macro_throwUnsupported(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_addTermInfo_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_toParserDescr_processAlias_spec__5(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isQuot(lean_object*);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr_processAtom___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Elab_Term_toParserDescr_processAlias_spec__0___lam__2(lean_object*, lean_object*);
lean_object* l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Elab_Term_toParserDescr_processAlias_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_____private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_strLitToPattern(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Environment_mainModule(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_checkRuleKind___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Command_checkRuleKind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr_ensureNoPrec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_evalPrec___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Command_elabSyntaxAbbrev___lam__0(lean_object*);
uint8_t l_String_isPrefixOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Command_expandNoKindMacroRulesAux_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Command_expandNoKindMacroRulesAux_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0_spec__6___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr_processSeq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_isLocalAttrKind___boxed(lean_object*);
lean_object* l_Array_append(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSyntax___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Elab_Command_getMainModule___redArg(lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_TSepArray_push(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_toParserDescr_processAlias_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabDeclareSyntaxCat_declRange__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Elab_Term_toParserDescr_processAlias_spec__0___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_getString_x21(lean_object*);
lean_object* l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* lean_erase_macro_scopes(lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_____private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Term_toParserDescr_processAlias_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr_processNonReserved___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Lean_Elab_Term_toParserDescr_processSeq_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_addMacroScopeIfLocal___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr_processSeq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_seqRight(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_____private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftTermElabM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr_processSepBy___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr_isValidAtom___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandOptPrecedence___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_addCategoryInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Macro_expandMacro_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0_spec__3_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Elab_mkUnusedBaseName(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkCIdent(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr_processNullaryOrCat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Command_elabSyntax_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkNameFromParserSyntax_appendCatName(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_runTermElabM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_addMacroScopeIfLocal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAtomFrom(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind___at___Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___Lean_Elab_Command_resolveSyntaxKind_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Parser_isValidSyntaxNodeKind(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSyntaxAbbrev___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabParserName_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_withMacroExpansion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabSyntax__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Term_markAsTrailingParser___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0_spec__3_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Parser_leadingIdentBehavior(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_toParserDescr_processAlias_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_instDecidableEqPos(lean_object*, lean_object*);
uint8_t l___private_Lean_Parser_Basic_0__Lean_Parser_beqLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8856_(uint8_t, uint8_t);
lean_object* l_String_toSubstring_x27(lean_object*);
uint8_t l_instDecidableEqChar(uint32_t, uint32_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Array_zip___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ensureUnaryParserAlias(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t l_Char_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_addMacroScopeIfLocal___at___Lean_Elab_Command_elabSyntax_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkNumLit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkNameFromParserSyntax_visit___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_toParserDescr_processAlias_spec__4(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandOptPrecedence(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Syntax_isNone(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
x_7 = lean_unsigned_to_nat(1u);
x_8 = l_Lean_Syntax_getArg(x_6, x_7);
lean_dec(x_6);
x_9 = l_Lean_evalPrec(x_8, x_2, x_3);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_9, 0, x_12);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_9, 0);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_9);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_13);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
return x_9;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_9);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_3);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandOptPrecedence___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_expandOptPrecedence(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_____private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq_spec__0___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_3, x_2);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_array_uget(x_10, x_3);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = lean_st_ref_get(x_6, x_7);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; size_t x_60; size_t x_61; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
x_19 = lean_ctor_get(x_5, 5);
lean_inc(x_19);
x_20 = lean_box(0);
x_21 = lean_ctor_get(x_4, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_4, 1);
lean_inc(x_22);
lean_dec(x_4);
x_23 = lean_unbox(x_20);
x_24 = l_Lean_SourceInfo_fromRef(x_19, x_23);
lean_dec(x_19);
x_25 = lean_ctor_get(x_5, 10);
lean_inc(x_25);
x_26 = lean_ctor_get(x_17, 0);
lean_inc(x_26);
lean_dec(x_17);
x_27 = l_Lean_Environment_mainModule(x_26);
lean_dec(x_26);
x_28 = lean_mk_string_unchecked("Lean", 4, 4);
x_29 = lean_mk_string_unchecked("Parser", 6, 6);
x_30 = lean_mk_string_unchecked("Term", 4, 4);
x_31 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
x_32 = l_Lean_Name_mkStr4(x_28, x_29, x_30, x_31);
x_33 = lean_mk_string_unchecked("ParserDescr.binary", 18, 18);
x_34 = l_String_toSubstring_x27(x_33);
x_35 = lean_mk_string_unchecked("ParserDescr", 11, 11);
x_36 = lean_mk_string_unchecked("binary", 6, 6);
lean_inc(x_36);
lean_inc(x_35);
x_37 = l_Lean_Name_mkStr2(x_35, x_36);
x_38 = l_Lean_addMacroScope(x_27, x_37, x_25);
lean_inc(x_28);
x_39 = l_Lean_Name_mkStr3(x_28, x_35, x_36);
x_40 = lean_box(0);
lean_inc(x_39);
lean_ctor_set_tag(x_15, 1);
lean_ctor_set(x_15, 1, x_40);
lean_ctor_set(x_15, 0, x_39);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_39);
x_42 = lean_box(0);
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 1, x_42);
lean_ctor_set(x_11, 0, x_41);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_15);
lean_ctor_set(x_43, 1, x_11);
lean_inc(x_24);
x_44 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_44, 0, x_24);
lean_ctor_set(x_44, 1, x_34);
lean_ctor_set(x_44, 2, x_38);
lean_ctor_set(x_44, 3, x_43);
x_45 = lean_mk_string_unchecked("null", 4, 4);
x_46 = l_Lean_Name_mkStr1(x_45);
x_47 = lean_mk_string_unchecked("quotedName", 10, 10);
x_48 = l_Lean_Name_mkStr4(x_28, x_29, x_30, x_47);
x_49 = lean_mk_string_unchecked("name", 4, 4);
x_50 = l_Lean_Name_mkStr1(x_49);
x_51 = lean_mk_string_unchecked("`andthen", 8, 8);
lean_inc(x_24);
x_52 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_52, 0, x_24);
lean_ctor_set(x_52, 1, x_51);
lean_inc(x_24);
x_53 = l_Lean_Syntax_node1(x_24, x_50, x_52);
lean_inc(x_24);
x_54 = l_Lean_Syntax_node1(x_24, x_48, x_53);
lean_inc(x_24);
x_55 = l_Lean_Syntax_node3(x_24, x_46, x_54, x_21, x_13);
x_56 = l_Lean_Syntax_node2(x_24, x_32, x_44, x_55);
x_57 = lean_nat_add(x_22, x_14);
lean_dec(x_14);
lean_dec(x_22);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_unsigned_to_nat(1u);
x_60 = lean_usize_of_nat(x_59);
x_61 = lean_usize_add(x_3, x_60);
x_3 = x_61;
x_4 = x_58;
x_7 = x_18;
goto _start;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; size_t x_107; size_t x_108; 
x_63 = lean_ctor_get(x_15, 0);
x_64 = lean_ctor_get(x_15, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_15);
x_65 = lean_ctor_get(x_5, 5);
lean_inc(x_65);
x_66 = lean_box(0);
x_67 = lean_ctor_get(x_4, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_4, 1);
lean_inc(x_68);
lean_dec(x_4);
x_69 = lean_unbox(x_66);
x_70 = l_Lean_SourceInfo_fromRef(x_65, x_69);
lean_dec(x_65);
x_71 = lean_ctor_get(x_5, 10);
lean_inc(x_71);
x_72 = lean_ctor_get(x_63, 0);
lean_inc(x_72);
lean_dec(x_63);
x_73 = l_Lean_Environment_mainModule(x_72);
lean_dec(x_72);
x_74 = lean_mk_string_unchecked("Lean", 4, 4);
x_75 = lean_mk_string_unchecked("Parser", 6, 6);
x_76 = lean_mk_string_unchecked("Term", 4, 4);
x_77 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_74);
x_78 = l_Lean_Name_mkStr4(x_74, x_75, x_76, x_77);
x_79 = lean_mk_string_unchecked("ParserDescr.binary", 18, 18);
x_80 = l_String_toSubstring_x27(x_79);
x_81 = lean_mk_string_unchecked("ParserDescr", 11, 11);
x_82 = lean_mk_string_unchecked("binary", 6, 6);
lean_inc(x_82);
lean_inc(x_81);
x_83 = l_Lean_Name_mkStr2(x_81, x_82);
x_84 = l_Lean_addMacroScope(x_73, x_83, x_71);
lean_inc(x_74);
x_85 = l_Lean_Name_mkStr3(x_74, x_81, x_82);
x_86 = lean_box(0);
lean_inc(x_85);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
x_88 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_88, 0, x_85);
x_89 = lean_box(0);
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 1, x_89);
lean_ctor_set(x_11, 0, x_88);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_87);
lean_ctor_set(x_90, 1, x_11);
lean_inc(x_70);
x_91 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_91, 0, x_70);
lean_ctor_set(x_91, 1, x_80);
lean_ctor_set(x_91, 2, x_84);
lean_ctor_set(x_91, 3, x_90);
x_92 = lean_mk_string_unchecked("null", 4, 4);
x_93 = l_Lean_Name_mkStr1(x_92);
x_94 = lean_mk_string_unchecked("quotedName", 10, 10);
x_95 = l_Lean_Name_mkStr4(x_74, x_75, x_76, x_94);
x_96 = lean_mk_string_unchecked("name", 4, 4);
x_97 = l_Lean_Name_mkStr1(x_96);
x_98 = lean_mk_string_unchecked("`andthen", 8, 8);
lean_inc(x_70);
x_99 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_99, 0, x_70);
lean_ctor_set(x_99, 1, x_98);
lean_inc(x_70);
x_100 = l_Lean_Syntax_node1(x_70, x_97, x_99);
lean_inc(x_70);
x_101 = l_Lean_Syntax_node1(x_70, x_95, x_100);
lean_inc(x_70);
x_102 = l_Lean_Syntax_node3(x_70, x_93, x_101, x_67, x_13);
x_103 = l_Lean_Syntax_node2(x_70, x_78, x_91, x_102);
x_104 = lean_nat_add(x_68, x_14);
lean_dec(x_14);
lean_dec(x_68);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
x_106 = lean_unsigned_to_nat(1u);
x_107 = lean_usize_of_nat(x_106);
x_108 = lean_usize_add(x_3, x_107);
x_3 = x_108;
x_4 = x_105;
x_7 = x_64;
goto _start;
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; size_t x_159; size_t x_160; 
x_110 = lean_ctor_get(x_11, 0);
x_111 = lean_ctor_get(x_11, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_11);
x_112 = lean_st_ref_get(x_6, x_7);
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 x_115 = x_112;
} else {
 lean_dec_ref(x_112);
 x_115 = lean_box(0);
}
x_116 = lean_ctor_get(x_5, 5);
lean_inc(x_116);
x_117 = lean_box(0);
x_118 = lean_ctor_get(x_4, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_4, 1);
lean_inc(x_119);
lean_dec(x_4);
x_120 = lean_unbox(x_117);
x_121 = l_Lean_SourceInfo_fromRef(x_116, x_120);
lean_dec(x_116);
x_122 = lean_ctor_get(x_5, 10);
lean_inc(x_122);
x_123 = lean_ctor_get(x_113, 0);
lean_inc(x_123);
lean_dec(x_113);
x_124 = l_Lean_Environment_mainModule(x_123);
lean_dec(x_123);
x_125 = lean_mk_string_unchecked("Lean", 4, 4);
x_126 = lean_mk_string_unchecked("Parser", 6, 6);
x_127 = lean_mk_string_unchecked("Term", 4, 4);
x_128 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_127);
lean_inc(x_126);
lean_inc(x_125);
x_129 = l_Lean_Name_mkStr4(x_125, x_126, x_127, x_128);
x_130 = lean_mk_string_unchecked("ParserDescr.binary", 18, 18);
x_131 = l_String_toSubstring_x27(x_130);
x_132 = lean_mk_string_unchecked("ParserDescr", 11, 11);
x_133 = lean_mk_string_unchecked("binary", 6, 6);
lean_inc(x_133);
lean_inc(x_132);
x_134 = l_Lean_Name_mkStr2(x_132, x_133);
x_135 = l_Lean_addMacroScope(x_124, x_134, x_122);
lean_inc(x_125);
x_136 = l_Lean_Name_mkStr3(x_125, x_132, x_133);
x_137 = lean_box(0);
lean_inc(x_136);
if (lean_is_scalar(x_115)) {
 x_138 = lean_alloc_ctor(1, 2, 0);
} else {
 x_138 = x_115;
 lean_ctor_set_tag(x_138, 1);
}
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
x_139 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_139, 0, x_136);
x_140 = lean_box(0);
x_141 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set(x_141, 1, x_140);
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_138);
lean_ctor_set(x_142, 1, x_141);
lean_inc(x_121);
x_143 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_143, 0, x_121);
lean_ctor_set(x_143, 1, x_131);
lean_ctor_set(x_143, 2, x_135);
lean_ctor_set(x_143, 3, x_142);
x_144 = lean_mk_string_unchecked("null", 4, 4);
x_145 = l_Lean_Name_mkStr1(x_144);
x_146 = lean_mk_string_unchecked("quotedName", 10, 10);
x_147 = l_Lean_Name_mkStr4(x_125, x_126, x_127, x_146);
x_148 = lean_mk_string_unchecked("name", 4, 4);
x_149 = l_Lean_Name_mkStr1(x_148);
x_150 = lean_mk_string_unchecked("`andthen", 8, 8);
lean_inc(x_121);
x_151 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_151, 0, x_121);
lean_ctor_set(x_151, 1, x_150);
lean_inc(x_121);
x_152 = l_Lean_Syntax_node1(x_121, x_149, x_151);
lean_inc(x_121);
x_153 = l_Lean_Syntax_node1(x_121, x_147, x_152);
lean_inc(x_121);
x_154 = l_Lean_Syntax_node3(x_121, x_145, x_153, x_118, x_110);
x_155 = l_Lean_Syntax_node2(x_121, x_129, x_143, x_154);
x_156 = lean_nat_add(x_119, x_111);
lean_dec(x_111);
lean_dec(x_119);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_155);
lean_ctor_set(x_157, 1, x_156);
x_158 = lean_unsigned_to_nat(1u);
x_159 = lean_usize_of_nat(x_158);
x_160 = lean_usize_add(x_3, x_159);
x_3 = x_160;
x_4 = x_157;
x_7 = x_114;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_____private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Subarray_forInUnsafe_loop___at_____private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq_spec__0___redArg(x_1, x_2, x_3, x_4, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_array_get_size(x_1);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_dec_eq(x_9, x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_array_fget(x_1, x_10);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; lean_object* x_22; size_t x_23; lean_object* x_24; uint8_t x_25; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
x_18 = l_Array_toSubarray___redArg(x_1, x_12, x_9);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_17);
x_20 = lean_ctor_get(x_18, 2);
lean_inc(x_20);
x_21 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
x_23 = lean_usize_of_nat(x_22);
lean_dec(x_22);
x_24 = l_Subarray_forInUnsafe_loop___at_____private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq_spec__0___redArg(x_18, x_21, x_23, x_19, x_6, x_7, x_8);
lean_dec(x_18);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
lean_ctor_set(x_14, 1, x_28);
lean_ctor_set(x_14, 0, x_27);
lean_ctor_set(x_24, 0, x_14);
return x_24;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_24, 0);
x_30 = lean_ctor_get(x_24, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_24);
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
lean_ctor_set(x_14, 1, x_32);
lean_ctor_set(x_14, 0, x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_14);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; size_t x_39; lean_object* x_40; size_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_34 = lean_ctor_get(x_14, 0);
x_35 = lean_ctor_get(x_14, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_14);
x_36 = l_Array_toSubarray___redArg(x_1, x_12, x_9);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_35);
x_38 = lean_ctor_get(x_36, 2);
lean_inc(x_38);
x_39 = lean_usize_of_nat(x_38);
lean_dec(x_38);
x_40 = lean_ctor_get(x_36, 1);
lean_inc(x_40);
x_41 = lean_usize_of_nat(x_40);
lean_dec(x_40);
x_42 = l_Subarray_forInUnsafe_loop___at_____private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq_spec__0___redArg(x_36, x_39, x_41, x_37, x_6, x_7, x_8);
lean_dec(x_36);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_45 = x_42;
} else {
 lean_dec_ref(x_42);
 x_45 = lean_box(0);
}
x_46 = lean_ctor_get(x_43, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_43, 1);
lean_inc(x_47);
lean_dec(x_43);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
if (lean_is_scalar(x_45)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_45;
}
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_44);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_9);
lean_dec(x_6);
x_50 = lean_array_fget(x_1, x_10);
lean_dec(x_1);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_8);
return x_51;
}
}
else
{
lean_object* x_52; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_1);
x_52 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__4___redArg(x_8);
return x_52;
}
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_____private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l_Subarray_forInUnsafe_loop___at_____private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq_spec__0___redArg(x_1, x_8, x_9, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_____private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Subarray_forInUnsafe_loop___at_____private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq_spec__0(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Term_markAsTrailingParser___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_1);
x_5 = lean_st_ref_set(x_2, x_4, x_3);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Term_markAsTrailingParser(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Term_markAsTrailingParser___redArg(x_1, x_3, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Term_markAsTrailingParser___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Term_markAsTrailingParser___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Term_markAsTrailingParser___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Term_markAsTrailingParser(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Term_withNotFirst___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_box(0);
x_13 = lean_ctor_get_uint8(x_2, sizeof(void*)*1 + 1);
x_14 = lean_ctor_get_uint8(x_2, sizeof(void*)*1 + 2);
lean_inc(x_11);
x_15 = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(x_15, 0, x_11);
x_16 = lean_unbox(x_12);
lean_ctor_set_uint8(x_15, sizeof(void*)*1, x_16);
lean_ctor_set_uint8(x_15, sizeof(void*)*1 + 1, x_13);
lean_ctor_set_uint8(x_15, sizeof(void*)*1 + 2, x_14);
x_17 = lean_apply_9(x_1, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_17;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Term_withNotFirst(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_box(0);
x_14 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 1);
x_15 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 2);
lean_inc(x_12);
x_16 = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(x_16, 0, x_12);
x_17 = lean_unbox(x_13);
lean_ctor_set_uint8(x_16, sizeof(void*)*1, x_17);
lean_ctor_set_uint8(x_16, sizeof(void*)*1 + 1, x_14);
lean_ctor_set_uint8(x_16, sizeof(void*)*1 + 2, x_15);
x_18 = lean_apply_9(x_2, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_18;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Term_withNotFirst___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Term_withNotFirst___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Term_withNotFirst___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Term_withNotFirst(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_ensureUnaryOutput(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_dec_eq(x_4, x_5);
lean_dec(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_7 = lean_box(0);
x_8 = l_Lean_SourceInfo_fromRef(x_7, x_6);
x_9 = lean_mk_string_unchecked("UnhygienicMain", 14, 14);
x_10 = l_Lean_Name_mkStr1(x_9);
x_11 = lean_mk_string_unchecked("Lean", 4, 4);
x_12 = lean_mk_string_unchecked("Parser", 6, 6);
x_13 = lean_mk_string_unchecked("Term", 4, 4);
x_14 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_15 = l_Lean_Name_mkStr4(x_11, x_12, x_13, x_14);
x_16 = lean_mk_string_unchecked("ParserDescr.unary", 17, 17);
x_17 = l_String_toSubstring_x27(x_16);
x_18 = lean_mk_string_unchecked("ParserDescr", 11, 11);
x_19 = lean_mk_string_unchecked("unary", 5, 5);
lean_inc(x_19);
lean_inc(x_18);
x_20 = l_Lean_Name_mkStr2(x_18, x_19);
x_21 = l_Lean_addMacroScope(x_10, x_20, x_5);
lean_inc(x_11);
x_22 = l_Lean_Name_mkStr3(x_11, x_18, x_19);
x_23 = lean_box(0);
lean_inc(x_22);
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 1, x_23);
lean_ctor_set(x_1, 0, x_22);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_22);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_1);
lean_ctor_set(x_27, 1, x_26);
lean_inc(x_8);
x_28 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_28, 0, x_8);
lean_ctor_set(x_28, 1, x_17);
lean_ctor_set(x_28, 2, x_21);
lean_ctor_set(x_28, 3, x_27);
x_29 = lean_mk_string_unchecked("null", 4, 4);
x_30 = l_Lean_Name_mkStr1(x_29);
x_35 = lean_mk_string_unchecked("group", 5, 5);
x_36 = l_Lean_Name_mkStr1(x_35);
lean_inc(x_36);
x_37 = l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(x_23, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_38 = l_Lean_quoteNameMk(x_36);
x_31 = x_38;
goto block_34;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_36);
x_39 = lean_ctor_get(x_37, 0);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_mk_string_unchecked("quotedName", 10, 10);
x_41 = l_Lean_Name_mkStr4(x_11, x_12, x_13, x_40);
x_42 = lean_mk_string_unchecked("`", 1, 1);
x_43 = lean_mk_string_unchecked(".", 1, 1);
x_44 = l_String_intercalate(x_43, x_39);
lean_dec(x_43);
x_45 = lean_string_append(x_42, x_44);
lean_dec(x_44);
x_46 = lean_box(2);
x_47 = l_Lean_Syntax_mkNameLit(x_45, x_46);
x_48 = lean_mk_empty_array_with_capacity(x_5);
x_49 = lean_array_push(x_48, x_47);
x_50 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_50, 0, x_46);
lean_ctor_set(x_50, 1, x_41);
lean_ctor_set(x_50, 2, x_49);
x_31 = x_50;
goto block_34;
}
block_34:
{
lean_object* x_32; lean_object* x_33; 
lean_inc(x_8);
x_32 = l_Lean_Syntax_node2(x_8, x_30, x_31, x_3);
x_33 = l_Lean_Syntax_node2(x_8, x_15, x_28, x_32);
return x_33;
}
}
else
{
lean_free_object(x_1);
return x_3;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_51 = lean_ctor_get(x_1, 0);
x_52 = lean_ctor_get(x_1, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_1);
x_53 = lean_unsigned_to_nat(1u);
x_54 = lean_nat_dec_eq(x_52, x_53);
lean_dec(x_52);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_55 = lean_box(0);
x_56 = l_Lean_SourceInfo_fromRef(x_55, x_54);
x_57 = lean_mk_string_unchecked("UnhygienicMain", 14, 14);
x_58 = l_Lean_Name_mkStr1(x_57);
x_59 = lean_mk_string_unchecked("Lean", 4, 4);
x_60 = lean_mk_string_unchecked("Parser", 6, 6);
x_61 = lean_mk_string_unchecked("Term", 4, 4);
x_62 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
x_63 = l_Lean_Name_mkStr4(x_59, x_60, x_61, x_62);
x_64 = lean_mk_string_unchecked("ParserDescr.unary", 17, 17);
x_65 = l_String_toSubstring_x27(x_64);
x_66 = lean_mk_string_unchecked("ParserDescr", 11, 11);
x_67 = lean_mk_string_unchecked("unary", 5, 5);
lean_inc(x_67);
lean_inc(x_66);
x_68 = l_Lean_Name_mkStr2(x_66, x_67);
x_69 = l_Lean_addMacroScope(x_58, x_68, x_53);
lean_inc(x_59);
x_70 = l_Lean_Name_mkStr3(x_59, x_66, x_67);
x_71 = lean_box(0);
lean_inc(x_70);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
x_73 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_73, 0, x_70);
x_74 = lean_box(0);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_72);
lean_ctor_set(x_76, 1, x_75);
lean_inc(x_56);
x_77 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_77, 0, x_56);
lean_ctor_set(x_77, 1, x_65);
lean_ctor_set(x_77, 2, x_69);
lean_ctor_set(x_77, 3, x_76);
x_78 = lean_mk_string_unchecked("null", 4, 4);
x_79 = l_Lean_Name_mkStr1(x_78);
x_84 = lean_mk_string_unchecked("group", 5, 5);
x_85 = l_Lean_Name_mkStr1(x_84);
lean_inc(x_85);
x_86 = l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(x_71, x_85);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; 
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
x_87 = l_Lean_quoteNameMk(x_85);
x_80 = x_87;
goto block_83;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_85);
x_88 = lean_ctor_get(x_86, 0);
lean_inc(x_88);
lean_dec(x_86);
x_89 = lean_mk_string_unchecked("quotedName", 10, 10);
x_90 = l_Lean_Name_mkStr4(x_59, x_60, x_61, x_89);
x_91 = lean_mk_string_unchecked("`", 1, 1);
x_92 = lean_mk_string_unchecked(".", 1, 1);
x_93 = l_String_intercalate(x_92, x_88);
lean_dec(x_92);
x_94 = lean_string_append(x_91, x_93);
lean_dec(x_93);
x_95 = lean_box(2);
x_96 = l_Lean_Syntax_mkNameLit(x_94, x_95);
x_97 = lean_mk_empty_array_with_capacity(x_53);
x_98 = lean_array_push(x_97, x_96);
x_99 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_99, 0, x_95);
lean_ctor_set(x_99, 1, x_90);
lean_ctor_set(x_99, 2, x_98);
x_80 = x_99;
goto block_83;
}
block_83:
{
lean_object* x_81; lean_object* x_82; 
lean_inc(x_56);
x_81 = l_Lean_Syntax_node2(x_56, x_79, x_80, x_51);
x_82 = l_Lean_Syntax_node2(x_56, x_63, x_77, x_81);
return x_82;
}
}
else
{
return x_51;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Term_withNestedParser(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_box(0);
x_13 = lean_ctor_get_uint8(x_2, sizeof(void*)*1 + 2);
lean_inc(x_11);
x_14 = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(x_14, 0, x_11);
x_15 = lean_unbox(x_12);
lean_ctor_set_uint8(x_14, sizeof(void*)*1, x_15);
x_16 = lean_unbox(x_12);
lean_ctor_set_uint8(x_14, sizeof(void*)*1 + 1, x_16);
lean_ctor_set_uint8(x_14, sizeof(void*)*1 + 2, x_13);
x_17 = lean_apply_9(x_1, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_17;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Term_withNestedParser___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Term_withNestedParser(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_addCategoryInfo(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_st_ref_get(x_8, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_22; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_14 = lean_mk_string_unchecked("Lean", 4, 4);
x_15 = lean_mk_string_unchecked("Parser", 6, 6);
x_16 = lean_mk_string_unchecked("Category", 8, 8);
x_17 = l_Lean_Name_mkStr3(x_14, x_15, x_16);
x_18 = l_Lean_Name_append(x_17, x_2);
x_19 = lean_ctor_get(x_12, 0);
lean_inc(x_19);
lean_dec(x_12);
x_20 = lean_box(1);
x_21 = lean_unbox(x_20);
lean_inc(x_18);
x_22 = l_Lean_Environment_contains(x_19, x_18, x_21);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_23 = lean_box(0);
lean_ctor_set(x_10, 0, x_23);
return x_10;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
lean_free_object(x_10);
x_24 = lean_box(0);
x_25 = l_Lean_Expr_const___override(x_18, x_24);
x_26 = lean_box(0);
x_27 = lean_box(0);
x_28 = lean_box(0);
x_29 = lean_box(0);
x_30 = lean_unbox(x_29);
x_31 = l_Lean_Elab_Term_addTermInfo_x27(x_1, x_25, x_26, x_27, x_28, x_30, x_3, x_4, x_5, x_6, x_7, x_8, x_13);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_42; 
x_32 = lean_ctor_get(x_10, 0);
x_33 = lean_ctor_get(x_10, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_10);
x_34 = lean_mk_string_unchecked("Lean", 4, 4);
x_35 = lean_mk_string_unchecked("Parser", 6, 6);
x_36 = lean_mk_string_unchecked("Category", 8, 8);
x_37 = l_Lean_Name_mkStr3(x_34, x_35, x_36);
x_38 = l_Lean_Name_append(x_37, x_2);
x_39 = lean_ctor_get(x_32, 0);
lean_inc(x_39);
lean_dec(x_32);
x_40 = lean_box(1);
x_41 = lean_unbox(x_40);
lean_inc(x_38);
x_42 = l_Lean_Environment_contains(x_39, x_38, x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_38);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_33);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; 
x_45 = lean_box(0);
x_46 = l_Lean_Expr_const___override(x_38, x_45);
x_47 = lean_box(0);
x_48 = lean_box(0);
x_49 = lean_box(0);
x_50 = lean_box(0);
x_51 = lean_unbox(x_50);
x_52 = l_Lean_Elab_Term_addTermInfo_x27(x_1, x_46, x_47, x_48, x_49, x_51, x_3, x_4, x_5, x_6, x_7, x_8, x_33);
return x_52;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_addAliasInfo(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_st_ref_get(x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 6);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_ctor_get_uint8(x_12, sizeof(void*)*3);
lean_dec(x_12);
if (x_13 == 0)
{
uint8_t x_14; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_10, 0);
lean_dec(x_15);
x_16 = lean_box(0);
lean_ctor_set(x_10, 0, x_16);
return x_10;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_dec(x_10);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_20);
lean_dec(x_10);
x_21 = lean_st_ref_get(x_8, x_20);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_21, 1);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_2, 0);
lean_inc(x_26);
lean_dec(x_2);
lean_inc(x_26);
x_27 = l_Lean_Environment_contains(x_25, x_26, x_13);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_28 = lean_box(0);
lean_ctor_set(x_21, 0, x_28);
return x_21;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; 
lean_free_object(x_21);
x_29 = lean_box(0);
x_30 = l_Lean_Expr_const___override(x_26, x_29);
x_31 = lean_box(0);
x_32 = lean_box(0);
x_33 = lean_box(0);
x_34 = lean_box(0);
x_35 = lean_unbox(x_34);
x_36 = l_Lean_Elab_Term_addTermInfo_x27(x_1, x_30, x_31, x_32, x_33, x_35, x_3, x_4, x_5, x_6, x_7, x_8, x_24);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_37 = lean_ctor_get(x_21, 0);
x_38 = lean_ctor_get(x_21, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_21);
x_39 = lean_ctor_get(x_37, 0);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_ctor_get(x_2, 0);
lean_inc(x_40);
lean_dec(x_2);
lean_inc(x_40);
x_41 = l_Lean_Environment_contains(x_39, x_40, x_13);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_40);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_38);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; 
x_44 = lean_box(0);
x_45 = l_Lean_Expr_const___override(x_40, x_44);
x_46 = lean_box(0);
x_47 = lean_box(0);
x_48 = lean_box(0);
x_49 = lean_box(0);
x_50 = lean_unbox(x_49);
x_51 = l_Lean_Elab_Term_addTermInfo_x27(x_1, x_45, x_46, x_47, x_48, x_50, x_3, x_4, x_5, x_6, x_7, x_8, x_38);
return x_51;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_isTracingEnabledFor___at___Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0_spec__0___redArg(x_1, x_8, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_addTrace___at___Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0_spec__1___redArg(x_1, x_2, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
lean_inc(x_15);
x_17 = l_Lean_isTracingEnabledFor___at___Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0_spec__0___redArg(x_15, x_8, x_10);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_unbox(x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_16);
lean_dec(x_15);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_1 = x_14;
x_10 = x_20;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_dec(x_17);
x_23 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_23, 0, x_16);
x_24 = l_Lean_MessageData_ofFormat(x_23);
x_25 = l_Lean_addTrace___at___Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0_spec__1___redArg(x_15, x_24, x_6, x_7, x_8, x_9, x_22);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_1 = x_14;
x_10 = x_26;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0_spec__3_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_addMessageContextFull___at___Lean_Meta_recordSynthPendingFailure_spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_4, 5);
lean_inc(x_10);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_11);
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_7, 0);
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_7);
x_14 = lean_ctor_get(x_4, 5);
lean_inc(x_14);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_12);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0_spec__3_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0_spec__3_spec__3___redArg(x_2, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_12 = lean_ctor_get(x_9, 5);
x_13 = l_Lean_replaceRef(x_1, x_12);
x_14 = lean_ctor_get(x_9, 0);
x_15 = lean_ctor_get(x_9, 1);
x_16 = lean_ctor_get(x_9, 2);
x_17 = lean_ctor_get(x_9, 3);
x_18 = lean_ctor_get(x_9, 4);
x_19 = lean_ctor_get(x_9, 6);
x_20 = lean_ctor_get(x_9, 7);
x_21 = lean_ctor_get(x_9, 8);
x_22 = lean_ctor_get(x_9, 9);
x_23 = lean_ctor_get(x_9, 10);
x_24 = lean_ctor_get_uint8(x_9, sizeof(void*)*13);
x_25 = lean_ctor_get(x_9, 11);
x_26 = lean_ctor_get_uint8(x_9, sizeof(void*)*13 + 1);
x_27 = lean_ctor_get(x_9, 12);
lean_inc(x_27);
lean_inc(x_25);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_28 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_28, 0, x_14);
lean_ctor_set(x_28, 1, x_15);
lean_ctor_set(x_28, 2, x_16);
lean_ctor_set(x_28, 3, x_17);
lean_ctor_set(x_28, 4, x_18);
lean_ctor_set(x_28, 5, x_13);
lean_ctor_set(x_28, 6, x_19);
lean_ctor_set(x_28, 7, x_20);
lean_ctor_set(x_28, 8, x_21);
lean_ctor_set(x_28, 9, x_22);
lean_ctor_set(x_28, 10, x_23);
lean_ctor_set(x_28, 11, x_25);
lean_ctor_set(x_28, 12, x_27);
lean_ctor_set_uint8(x_28, sizeof(void*)*13, x_24);
lean_ctor_set_uint8(x_28, sizeof(void*)*13 + 1, x_26);
x_29 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0_spec__3_spec__3___redArg(x_2, x_7, x_8, x_28, x_10, x_11);
lean_dec(x_28);
return x_29;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0_spec__3___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0_spec__5___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_3 = lean_mk_string_unchecked("runtime", 7, 7);
x_4 = lean_mk_string_unchecked("maxRecDepth", 11, 11);
x_5 = l_Lean_Name_mkStr2(x_3, x_4);
x_6 = lean_mk_string_unchecked("maximum recursion depth has been reached\nuse `set_option maxRecDepth <num>` to increase limit\nuse `set_option diagnostics true` to get diagnostic information", 157, 157);
x_7 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = l_Lean_MessageData_ofFormat(x_7);
x_9 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_throwMaxRecDepthAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0_spec__5___redArg(x_2, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0_spec__6___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_unsupportedSyntaxExceptionId;
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0_spec__6___redArg(x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_box(1);
x_6 = lean_unbox(x_5);
x_7 = l_Lean_Environment_contains(x_1, x_2, x_6);
x_8 = lean_box(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Elab_expandMacroImpl_x3f(x_1, x_2, x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_5, 0);
lean_dec(x_8);
x_9 = lean_box(0);
lean_ctor_set(x_5, 0, x_9);
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_6);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_6, 0);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; uint8_t x_17; 
lean_free_object(x_6);
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
lean_dec(x_5);
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = l_liftExcept___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__0___redArg(x_15, x_16);
lean_dec(x_15);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 0);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = l_liftExcept___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__0___redArg(x_20, x_16);
lean_dec(x_20);
return x_21;
}
}
else
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_5, 1);
lean_inc(x_22);
lean_dec(x_5);
x_23 = !lean_is_exclusive(x_15);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_15, 0);
lean_ctor_set(x_6, 0, x_24);
lean_ctor_set(x_15, 0, x_6);
x_25 = l_liftExcept___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__0___redArg(x_15, x_22);
lean_dec(x_15);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_15, 0);
lean_inc(x_26);
lean_dec(x_15);
lean_ctor_set(x_6, 0, x_26);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_6);
x_28 = l_liftExcept___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__0___redArg(x_27, x_22);
lean_dec(x_27);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_6, 0);
lean_inc(x_29);
lean_dec(x_6);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_5, 1);
lean_inc(x_31);
lean_dec(x_5);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 x_33 = x_30;
} else {
 lean_dec_ref(x_30);
 x_33 = lean_box(0);
}
if (lean_is_scalar(x_33)) {
 x_34 = lean_alloc_ctor(0, 1, 0);
} else {
 x_34 = x_33;
}
lean_ctor_set(x_34, 0, x_32);
x_35 = l_liftExcept___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__0___redArg(x_34, x_31);
lean_dec(x_34);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_36 = lean_ctor_get(x_5, 1);
lean_inc(x_36);
lean_dec(x_5);
x_37 = lean_ctor_get(x_30, 0);
lean_inc(x_37);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 x_38 = x_30;
} else {
 lean_dec_ref(x_30);
 x_38 = lean_box(0);
}
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_37);
if (lean_is_scalar(x_38)) {
 x_40 = lean_alloc_ctor(1, 1, 0);
} else {
 x_40 = x_38;
}
lean_ctor_set(x_40, 0, x_39);
x_41 = l_liftExcept___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__0___redArg(x_40, x_36);
lean_dec(x_40);
return x_41;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_ResolveName_resolveGlobalName(x_1, x_2, x_3, x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0___redArg___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_ResolveName_resolveNamespace(x_1, x_2, x_3, x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_11 = lean_st_ref_get(x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_8, 6);
lean_inc(x_14);
x_15 = lean_ctor_get(x_8, 7);
lean_inc(x_15);
x_16 = lean_st_ref_get(x_9, x_13);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
x_20 = lean_ctor_get(x_12, 0);
lean_inc(x_20);
lean_dec(x_12);
lean_inc(x_20);
x_21 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0___redArg___lam__0___boxed), 4, 1);
lean_closure_set(x_21, 0, x_20);
lean_inc(x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0___redArg___lam__1___boxed), 4, 1);
lean_closure_set(x_22, 0, x_20);
lean_inc(x_14);
x_23 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0___redArg___lam__2___boxed), 3, 1);
lean_closure_set(x_23, 0, x_14);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_20);
x_24 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0___redArg___lam__3___boxed), 6, 3);
lean_closure_set(x_24, 0, x_20);
lean_closure_set(x_24, 1, x_14);
lean_closure_set(x_24, 2, x_15);
lean_inc(x_20);
x_25 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0___redArg___lam__4___boxed), 6, 3);
lean_closure_set(x_25, 0, x_20);
lean_closure_set(x_25, 1, x_14);
lean_closure_set(x_25, 2, x_15);
x_26 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_26, 0, x_22);
lean_ctor_set(x_26, 1, x_23);
lean_ctor_set(x_26, 2, x_21);
lean_ctor_set(x_26, 3, x_25);
lean_ctor_set(x_26, 4, x_24);
x_27 = lean_ctor_get(x_8, 5);
lean_inc(x_27);
x_28 = lean_ctor_get(x_8, 10);
lean_inc(x_28);
x_29 = lean_ctor_get(x_8, 3);
lean_inc(x_29);
x_30 = lean_ctor_get(x_8, 4);
lean_inc(x_30);
x_31 = lean_ctor_get(x_18, 1);
lean_inc(x_31);
lean_dec(x_18);
x_32 = l_Lean_Environment_mainModule(x_20);
lean_dec(x_20);
x_33 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_33, 0, x_26);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_33, 2, x_28);
lean_ctor_set(x_33, 3, x_29);
lean_ctor_set(x_33, 4, x_30);
lean_ctor_set(x_33, 5, x_27);
x_34 = lean_box(0);
lean_ctor_set(x_16, 1, x_34);
lean_ctor_set(x_16, 0, x_31);
x_35 = lean_apply_2(x_1, x_33, x_16);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_st_ref_take(x_9, x_19);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_ctor_get(x_37, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_39, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_39, 2);
lean_inc(x_43);
x_44 = lean_ctor_get(x_39, 3);
lean_inc(x_44);
x_45 = lean_ctor_get(x_39, 4);
lean_inc(x_45);
x_46 = lean_ctor_get(x_39, 5);
lean_inc(x_46);
x_47 = lean_ctor_get(x_39, 6);
lean_inc(x_47);
x_48 = lean_ctor_get(x_39, 7);
lean_inc(x_48);
lean_dec(x_39);
x_49 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_49, 0, x_42);
lean_ctor_set(x_49, 1, x_41);
lean_ctor_set(x_49, 2, x_43);
lean_ctor_set(x_49, 3, x_44);
lean_ctor_set(x_49, 4, x_45);
lean_ctor_set(x_49, 5, x_46);
lean_ctor_set(x_49, 6, x_47);
lean_ctor_set(x_49, 7, x_48);
x_50 = lean_st_ref_set(x_9, x_49, x_40);
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
lean_dec(x_50);
x_52 = lean_ctor_get(x_37, 1);
lean_inc(x_52);
lean_dec(x_37);
x_53 = l_List_reverse___redArg(x_52);
x_54 = l_List_forM___at___Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0_spec__2(x_53, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_51);
lean_dec(x_8);
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_54, 0);
lean_dec(x_56);
lean_ctor_set(x_54, 0, x_36);
return x_54;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_57);
lean_dec(x_54);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_36);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
else
{
lean_object* x_59; 
x_59 = lean_ctor_get(x_35, 0);
lean_inc(x_59);
lean_dec(x_35);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = lean_mk_string_unchecked("maximum recursion depth has been reached\nuse `set_option maxRecDepth <num>` to increase limit\nuse `set_option diagnostics true` to get diagnostic information", 157, 157);
x_63 = lean_string_dec_eq(x_61, x_62);
lean_dec(x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_64, 0, x_61);
x_65 = l_Lean_MessageData_ofFormat(x_64);
x_66 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0_spec__3___redArg(x_60, x_65, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_19);
lean_dec(x_8);
lean_dec(x_60);
return x_66;
}
else
{
lean_object* x_67; 
lean_dec(x_61);
lean_dec(x_8);
x_67 = l_Lean_throwMaxRecDepthAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0_spec__5___redArg(x_60, x_19);
return x_67;
}
}
else
{
lean_object* x_68; 
lean_dec(x_8);
x_68 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0_spec__6___redArg(x_19);
return x_68;
}
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_69 = lean_ctor_get(x_16, 0);
x_70 = lean_ctor_get(x_16, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_16);
x_71 = lean_ctor_get(x_12, 0);
lean_inc(x_71);
lean_dec(x_12);
lean_inc(x_71);
x_72 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0___redArg___lam__0___boxed), 4, 1);
lean_closure_set(x_72, 0, x_71);
lean_inc(x_71);
x_73 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0___redArg___lam__1___boxed), 4, 1);
lean_closure_set(x_73, 0, x_71);
lean_inc(x_14);
x_74 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0___redArg___lam__2___boxed), 3, 1);
lean_closure_set(x_74, 0, x_14);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_71);
x_75 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0___redArg___lam__3___boxed), 6, 3);
lean_closure_set(x_75, 0, x_71);
lean_closure_set(x_75, 1, x_14);
lean_closure_set(x_75, 2, x_15);
lean_inc(x_71);
x_76 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0___redArg___lam__4___boxed), 6, 3);
lean_closure_set(x_76, 0, x_71);
lean_closure_set(x_76, 1, x_14);
lean_closure_set(x_76, 2, x_15);
x_77 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_77, 0, x_73);
lean_ctor_set(x_77, 1, x_74);
lean_ctor_set(x_77, 2, x_72);
lean_ctor_set(x_77, 3, x_76);
lean_ctor_set(x_77, 4, x_75);
x_78 = lean_ctor_get(x_8, 5);
lean_inc(x_78);
x_79 = lean_ctor_get(x_8, 10);
lean_inc(x_79);
x_80 = lean_ctor_get(x_8, 3);
lean_inc(x_80);
x_81 = lean_ctor_get(x_8, 4);
lean_inc(x_81);
x_82 = lean_ctor_get(x_69, 1);
lean_inc(x_82);
lean_dec(x_69);
x_83 = l_Lean_Environment_mainModule(x_71);
lean_dec(x_71);
x_84 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_84, 0, x_77);
lean_ctor_set(x_84, 1, x_83);
lean_ctor_set(x_84, 2, x_79);
lean_ctor_set(x_84, 3, x_80);
lean_ctor_set(x_84, 4, x_81);
lean_ctor_set(x_84, 5, x_78);
x_85 = lean_box(0);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_82);
lean_ctor_set(x_86, 1, x_85);
x_87 = lean_apply_2(x_1, x_84, x_86);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
x_90 = lean_st_ref_take(x_9, x_70);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
x_93 = lean_ctor_get(x_89, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_91, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_91, 2);
lean_inc(x_95);
x_96 = lean_ctor_get(x_91, 3);
lean_inc(x_96);
x_97 = lean_ctor_get(x_91, 4);
lean_inc(x_97);
x_98 = lean_ctor_get(x_91, 5);
lean_inc(x_98);
x_99 = lean_ctor_get(x_91, 6);
lean_inc(x_99);
x_100 = lean_ctor_get(x_91, 7);
lean_inc(x_100);
lean_dec(x_91);
x_101 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_101, 0, x_94);
lean_ctor_set(x_101, 1, x_93);
lean_ctor_set(x_101, 2, x_95);
lean_ctor_set(x_101, 3, x_96);
lean_ctor_set(x_101, 4, x_97);
lean_ctor_set(x_101, 5, x_98);
lean_ctor_set(x_101, 6, x_99);
lean_ctor_set(x_101, 7, x_100);
x_102 = lean_st_ref_set(x_9, x_101, x_92);
x_103 = lean_ctor_get(x_102, 1);
lean_inc(x_103);
lean_dec(x_102);
x_104 = lean_ctor_get(x_89, 1);
lean_inc(x_104);
lean_dec(x_89);
x_105 = l_List_reverse___redArg(x_104);
x_106 = l_List_forM___at___Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0_spec__2(x_105, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_103);
lean_dec(x_8);
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
lean_ctor_set(x_109, 0, x_88);
lean_ctor_set(x_109, 1, x_107);
return x_109;
}
else
{
lean_object* x_110; 
x_110 = lean_ctor_get(x_87, 0);
lean_inc(x_110);
lean_dec(x_87);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
lean_dec(x_110);
x_113 = lean_mk_string_unchecked("maximum recursion depth has been reached\nuse `set_option maxRecDepth <num>` to increase limit\nuse `set_option diagnostics true` to get diagnostic information", 157, 157);
x_114 = lean_string_dec_eq(x_112, x_113);
lean_dec(x_113);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_115, 0, x_112);
x_116 = l_Lean_MessageData_ofFormat(x_115);
x_117 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0_spec__3___redArg(x_111, x_116, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_70);
lean_dec(x_8);
lean_dec(x_111);
return x_117;
}
else
{
lean_object* x_118; 
lean_dec(x_112);
lean_dec(x_8);
x_118 = l_Lean_throwMaxRecDepthAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0_spec__5___redArg(x_111, x_70);
return x_118;
}
}
else
{
lean_object* x_119; 
lean_dec(x_8);
x_119 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0_spec__6___redArg(x_70);
return x_119;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_checkLeftRec(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; uint8_t x_23; uint8_t x_69; 
x_69 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
if (x_69 == 0)
{
x_23 = x_69;
goto block_68;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
lean_inc(x_1);
x_70 = l_Lean_Syntax_getKind(x_1);
x_71 = lean_mk_string_unchecked("Lean", 4, 4);
x_72 = lean_mk_string_unchecked("Parser", 6, 6);
x_73 = lean_mk_string_unchecked("Syntax", 6, 6);
x_74 = lean_mk_string_unchecked("cat", 3, 3);
x_75 = l_Lean_Name_mkStr4(x_71, x_72, x_73, x_74);
x_76 = lean_name_eq(x_70, x_75);
lean_dec(x_75);
lean_dec(x_70);
x_23 = x_76;
goto block_68;
}
block_22:
{
lean_object* x_15; uint8_t x_16; 
x_15 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Term_markAsTrailingParser___redArg(x_14, x_11, x_12);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
x_18 = lean_box(x_13);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_box(x_13);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
block_68:
{
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_24 = lean_box(x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_10);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_26 = lean_unsigned_to_nat(0u);
x_27 = l_Lean_Syntax_getArg(x_1, x_26);
x_28 = l_Lean_Syntax_getId(x_27);
lean_dec(x_27);
x_29 = lean_erase_macro_scopes(x_28);
x_30 = lean_ctor_get(x_2, 0);
x_31 = lean_name_eq(x_29, x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_29);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_32 = lean_box(x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_10);
return x_33;
}
else
{
lean_object* x_34; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_29);
lean_inc(x_1);
x_34 = l_Lean_Elab_Term_addCategoryInfo(x_1, x_29, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_unsigned_to_nat(1u);
x_37 = l_Lean_Syntax_getArg(x_1, x_36);
x_38 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandOptPrecedence___boxed), 3, 1);
lean_closure_set(x_38, 0, x_37);
lean_inc(x_8);
x_39 = l_Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0___redArg(x_38, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_35);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
x_40 = lean_ctor_get_uint8(x_2, sizeof(void*)*1 + 1);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_unsigned_to_nat(3u);
x_43 = l_Lean_Syntax_getArg(x_1, x_42);
lean_dec(x_1);
x_44 = lean_mk_string_unchecked("invalid occurrence of '", 23, 23);
x_45 = l_Lean_stringToMessageData(x_44);
lean_dec(x_44);
x_46 = l_Lean_MessageData_ofName(x_29);
x_47 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_mk_string_unchecked("', parser algorithm does not allow this form of left recursion", 62, 62);
x_49 = l_Lean_stringToMessageData(x_48);
lean_dec(x_48);
x_50 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_49);
x_51 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0_spec__3___redArg(x_43, x_50, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_41);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_43);
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
return x_51;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_51, 0);
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_51);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
else
{
lean_object* x_56; 
lean_dec(x_29);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_56 = lean_ctor_get(x_39, 0);
lean_inc(x_56);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_39, 1);
lean_inc(x_57);
lean_dec(x_39);
x_11 = x_3;
x_12 = x_57;
x_13 = x_31;
x_14 = x_26;
goto block_22;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_39, 1);
lean_inc(x_58);
lean_dec(x_39);
x_59 = lean_ctor_get(x_56, 0);
lean_inc(x_59);
lean_dec(x_56);
x_11 = x_3;
x_12 = x_58;
x_13 = x_31;
x_14 = x_59;
goto block_22;
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_29);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_60 = !lean_is_exclusive(x_39);
if (x_60 == 0)
{
return x_39;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_39, 0);
x_62 = lean_ctor_get(x_39, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_39);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_29);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_64 = !lean_is_exclusive(x_34);
if (x_64 == 0)
{
return x_34;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_34, 0);
x_66 = lean_ctor_get(x_34, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_34);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isTracingEnabledFor___at___Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_isTracingEnabledFor___at___Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_addTrace___at___Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_addTrace___at___Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l_List_forM___at___Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_List_forM___at___Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0_spec__3_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0_spec__3_spec__3___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0_spec__3_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0_spec__3_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0_spec__3___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
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
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_throwMaxRecDepthAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0_spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0_spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0___redArg___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0___redArg___lam__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0___redArg___lam__2(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0___redArg___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0___redArg___lam__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0___redArg___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0___redArg___lam__4(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_checkLeftRec___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Term_checkLeftRec(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabParserName_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_25; lean_object* x_26; 
lean_inc(x_6);
lean_inc(x_1);
x_25 = l_Lean_Parser_resolveParserName(x_1, x_6, x_7, x_8);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_25);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_25, 0);
lean_dec(x_28);
x_29 = lean_box(0);
lean_ctor_set(x_25, 0, x_29);
return x_25;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_25, 1);
lean_inc(x_30);
lean_dec(x_25);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
else
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_26, 0);
lean_inc(x_33);
switch (lean_obj_tag(x_33)) {
case 0:
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_26, 1);
lean_inc(x_34);
lean_dec(x_26);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_25, 1);
lean_inc(x_35);
lean_dec(x_25);
x_36 = lean_ctor_get(x_33, 0);
lean_inc(x_36);
x_37 = l_Lean_Elab_Term_addCategoryInfo(x_1, x_36, x_2, x_3, x_4, x_5, x_6, x_7, x_35);
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_37, 0);
lean_dec(x_39);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_33);
lean_ctor_set(x_37, 0, x_40);
return x_37;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_37, 1);
lean_inc(x_41);
lean_dec(x_37);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_33);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
}
else
{
uint8_t x_44; 
lean_dec(x_33);
x_44 = !lean_is_exclusive(x_37);
if (x_44 == 0)
{
return x_37;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_37, 0);
x_46 = lean_ctor_get(x_37, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_37);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
lean_object* x_48; 
lean_dec(x_34);
lean_dec(x_33);
x_48 = lean_ctor_get(x_25, 1);
lean_inc(x_48);
lean_dec(x_25);
x_9 = x_2;
x_10 = x_3;
x_11 = x_4;
x_12 = x_5;
x_13 = x_6;
x_14 = x_7;
x_15 = x_48;
goto block_24;
}
}
case 1:
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_26, 1);
lean_inc(x_49);
lean_dec(x_26);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; 
x_50 = lean_ctor_get(x_25, 1);
lean_inc(x_50);
lean_dec(x_25);
x_51 = lean_ctor_get(x_33, 0);
lean_inc(x_51);
x_52 = lean_box(0);
x_53 = l_Lean_Expr_const___override(x_51, x_52);
x_54 = lean_box(0);
x_55 = lean_box(0);
x_56 = lean_box(0);
x_57 = lean_box(0);
x_58 = lean_unbox(x_57);
x_59 = l_Lean_Elab_Term_addTermInfo_x27(x_1, x_53, x_54, x_55, x_56, x_58, x_2, x_3, x_4, x_5, x_6, x_7, x_50);
if (lean_obj_tag(x_59) == 0)
{
uint8_t x_60; 
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_59, 0);
lean_dec(x_61);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_33);
lean_ctor_set(x_59, 0, x_62);
return x_59;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_59, 1);
lean_inc(x_63);
lean_dec(x_59);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_33);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_63);
return x_65;
}
}
else
{
uint8_t x_66; 
lean_dec(x_33);
x_66 = !lean_is_exclusive(x_59);
if (x_66 == 0)
{
return x_59;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_59, 0);
x_68 = lean_ctor_get(x_59, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_59);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
else
{
lean_object* x_70; 
lean_dec(x_49);
lean_dec(x_33);
x_70 = lean_ctor_get(x_25, 1);
lean_inc(x_70);
lean_dec(x_25);
x_9 = x_2;
x_10 = x_3;
x_11 = x_4;
x_12 = x_5;
x_13 = x_6;
x_14 = x_7;
x_15 = x_70;
goto block_24;
}
}
default: 
{
lean_object* x_71; 
x_71 = lean_ctor_get(x_26, 1);
lean_inc(x_71);
lean_dec(x_26);
if (lean_obj_tag(x_71) == 0)
{
uint8_t x_72; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_72 = !lean_is_exclusive(x_25);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_25, 0);
lean_dec(x_73);
x_74 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_74, 0, x_33);
lean_ctor_set(x_25, 0, x_74);
return x_25;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_25, 1);
lean_inc(x_75);
lean_dec(x_25);
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_33);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_75);
return x_77;
}
}
else
{
lean_object* x_78; 
lean_dec(x_71);
lean_dec(x_33);
x_78 = lean_ctor_get(x_25, 1);
lean_inc(x_78);
lean_dec(x_25);
x_9 = x_2;
x_10 = x_3;
x_11 = x_4;
x_12 = x_5;
x_13 = x_6;
x_14 = x_7;
x_15 = x_78;
goto block_24;
}
}
}
}
block_24:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_16 = lean_mk_string_unchecked("ambiguous parser ", 17, 17);
x_17 = l_Lean_stringToMessageData(x_16);
lean_dec(x_16);
lean_inc(x_1);
x_18 = l_Lean_MessageData_ofSyntax(x_1);
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_mk_string_unchecked("", 0, 0);
x_21 = l_Lean_stringToMessageData(x_20);
lean_dec(x_20);
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__2___redArg(x_1, x_22, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_1);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabParserName(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_9 = l_Lean_Elab_Term_elabParserName_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_mk_string_unchecked("unknown parser ", 15, 15);
x_13 = l_Lean_stringToMessageData(x_12);
lean_dec(x_12);
lean_inc(x_1);
x_14 = l_Lean_MessageData_ofSyntax(x_1);
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_mk_string_unchecked("", 0, 0);
x_17 = l_Lean_stringToMessageData(x_16);
lean_dec(x_16);
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__2___redArg(x_1, x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_9);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_9, 0);
lean_dec(x_21);
x_22 = lean_ctor_get(x_10, 0);
lean_inc(x_22);
lean_dec(x_10);
lean_ctor_set(x_9, 0, x_22);
return x_9;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_9, 1);
lean_inc(x_23);
lean_dec(x_9);
x_24 = lean_ctor_get(x_10, 0);
lean_inc(x_24);
lean_dec(x_10);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
}
else
{
uint8_t x_26; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_9);
if (x_26 == 0)
{
return x_9;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_9, 0);
x_28 = lean_ctor_get(x_9, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_9);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr_processNonReserved___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
x_7 = l_Lean_Syntax_isStrLit_x3f(x_6);
lean_dec(x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
lean_dec(x_2);
x_8 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0_spec__6___redArg(x_4);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = lean_st_ref_get(x_3, x_4);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_2, 5);
lean_inc(x_14);
x_15 = lean_box(0);
x_16 = lean_unbox(x_15);
x_17 = l_Lean_SourceInfo_fromRef(x_14, x_16);
lean_dec(x_14);
x_18 = lean_ctor_get(x_2, 10);
lean_inc(x_18);
lean_dec(x_2);
x_19 = lean_ctor_get(x_13, 0);
lean_inc(x_19);
lean_dec(x_13);
x_20 = l_Lean_Environment_mainModule(x_19);
lean_dec(x_19);
x_21 = lean_mk_string_unchecked("Lean", 4, 4);
x_22 = lean_mk_string_unchecked("Parser", 6, 6);
x_23 = lean_mk_string_unchecked("Term", 4, 4);
x_24 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
x_25 = l_Lean_Name_mkStr4(x_21, x_22, x_23, x_24);
x_26 = lean_mk_string_unchecked("paren", 5, 5);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
x_27 = l_Lean_Name_mkStr4(x_21, x_22, x_23, x_26);
x_28 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_17);
x_29 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_29, 0, x_17);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_mk_string_unchecked("withAnnotateTerm", 16, 16);
lean_inc(x_21);
x_31 = l_Lean_Name_mkStr2(x_21, x_30);
x_32 = lean_mk_string_unchecked("with_annotate_term", 18, 18);
lean_inc(x_17);
x_33 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_33, 0, x_17);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_unsigned_to_nat(0u);
x_35 = l_Lean_Syntax_getArg(x_1, x_34);
x_36 = lean_mk_string_unchecked("explicit", 8, 8);
lean_inc(x_21);
x_37 = l_Lean_Name_mkStr4(x_21, x_22, x_23, x_36);
x_38 = lean_mk_string_unchecked("@", 1, 1);
lean_inc(x_17);
x_39 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_39, 0, x_17);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_mk_string_unchecked("ParserDescr.nonReservedSymbol", 29, 29);
x_41 = l_String_toSubstring_x27(x_40);
x_42 = lean_mk_string_unchecked("ParserDescr", 11, 11);
x_43 = lean_mk_string_unchecked("nonReservedSymbol", 17, 17);
lean_inc(x_43);
lean_inc(x_42);
x_44 = l_Lean_Name_mkStr2(x_42, x_43);
lean_inc(x_18);
lean_inc(x_20);
x_45 = l_Lean_addMacroScope(x_20, x_44, x_18);
x_46 = l_Lean_Name_mkStr3(x_21, x_42, x_43);
x_47 = lean_box(0);
lean_inc(x_46);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
lean_ctor_set_tag(x_7, 0);
lean_ctor_set(x_7, 0, x_46);
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_7);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_50);
lean_inc(x_17);
x_52 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_52, 0, x_17);
lean_ctor_set(x_52, 1, x_41);
lean_ctor_set(x_52, 2, x_45);
lean_ctor_set(x_52, 3, x_51);
lean_inc(x_17);
x_53 = l_Lean_Syntax_node2(x_17, x_37, x_39, x_52);
lean_inc(x_17);
x_54 = l_Lean_Syntax_node3(x_17, x_31, x_33, x_35, x_53);
x_55 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_17);
x_56 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_56, 0, x_17);
lean_ctor_set(x_56, 1, x_55);
lean_inc(x_17);
x_57 = l_Lean_Syntax_node3(x_17, x_27, x_29, x_54, x_56);
x_58 = lean_mk_string_unchecked("null", 4, 4);
x_59 = l_Lean_Name_mkStr1(x_58);
x_60 = lean_box(2);
x_61 = l_Lean_Syntax_mkStrLit(x_10, x_60);
lean_dec(x_10);
x_62 = lean_mk_string_unchecked("false", 5, 5);
lean_inc(x_62);
x_63 = l_String_toSubstring_x27(x_62);
lean_inc(x_62);
x_64 = l_Lean_Name_mkStr1(x_62);
x_65 = l_Lean_addMacroScope(x_20, x_64, x_18);
x_66 = lean_mk_string_unchecked("Bool", 4, 4);
x_67 = l_Lean_Name_mkStr2(x_66, x_62);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_47);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_49);
lean_inc(x_17);
x_70 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_70, 0, x_17);
lean_ctor_set(x_70, 1, x_63);
lean_ctor_set(x_70, 2, x_65);
lean_ctor_set(x_70, 3, x_69);
lean_inc(x_17);
x_71 = l_Lean_Syntax_node2(x_17, x_59, x_61, x_70);
x_72 = l_Lean_Syntax_node2(x_17, x_25, x_57, x_71);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_5);
lean_ctor_set(x_11, 0, x_73);
return x_11;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_74 = lean_ctor_get(x_11, 0);
x_75 = lean_ctor_get(x_11, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_11);
x_76 = lean_ctor_get(x_2, 5);
lean_inc(x_76);
x_77 = lean_box(0);
x_78 = lean_unbox(x_77);
x_79 = l_Lean_SourceInfo_fromRef(x_76, x_78);
lean_dec(x_76);
x_80 = lean_ctor_get(x_2, 10);
lean_inc(x_80);
lean_dec(x_2);
x_81 = lean_ctor_get(x_74, 0);
lean_inc(x_81);
lean_dec(x_74);
x_82 = l_Lean_Environment_mainModule(x_81);
lean_dec(x_81);
x_83 = lean_mk_string_unchecked("Lean", 4, 4);
x_84 = lean_mk_string_unchecked("Parser", 6, 6);
x_85 = lean_mk_string_unchecked("Term", 4, 4);
x_86 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
x_87 = l_Lean_Name_mkStr4(x_83, x_84, x_85, x_86);
x_88 = lean_mk_string_unchecked("paren", 5, 5);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
x_89 = l_Lean_Name_mkStr4(x_83, x_84, x_85, x_88);
x_90 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_79);
x_91 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_91, 0, x_79);
lean_ctor_set(x_91, 1, x_90);
x_92 = lean_mk_string_unchecked("withAnnotateTerm", 16, 16);
lean_inc(x_83);
x_93 = l_Lean_Name_mkStr2(x_83, x_92);
x_94 = lean_mk_string_unchecked("with_annotate_term", 18, 18);
lean_inc(x_79);
x_95 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_95, 0, x_79);
lean_ctor_set(x_95, 1, x_94);
x_96 = lean_unsigned_to_nat(0u);
x_97 = l_Lean_Syntax_getArg(x_1, x_96);
x_98 = lean_mk_string_unchecked("explicit", 8, 8);
lean_inc(x_83);
x_99 = l_Lean_Name_mkStr4(x_83, x_84, x_85, x_98);
x_100 = lean_mk_string_unchecked("@", 1, 1);
lean_inc(x_79);
x_101 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_101, 0, x_79);
lean_ctor_set(x_101, 1, x_100);
x_102 = lean_mk_string_unchecked("ParserDescr.nonReservedSymbol", 29, 29);
x_103 = l_String_toSubstring_x27(x_102);
x_104 = lean_mk_string_unchecked("ParserDescr", 11, 11);
x_105 = lean_mk_string_unchecked("nonReservedSymbol", 17, 17);
lean_inc(x_105);
lean_inc(x_104);
x_106 = l_Lean_Name_mkStr2(x_104, x_105);
lean_inc(x_80);
lean_inc(x_82);
x_107 = l_Lean_addMacroScope(x_82, x_106, x_80);
x_108 = l_Lean_Name_mkStr3(x_83, x_104, x_105);
x_109 = lean_box(0);
lean_inc(x_108);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
lean_ctor_set_tag(x_7, 0);
lean_ctor_set(x_7, 0, x_108);
x_111 = lean_box(0);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_7);
lean_ctor_set(x_112, 1, x_111);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_110);
lean_ctor_set(x_113, 1, x_112);
lean_inc(x_79);
x_114 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_114, 0, x_79);
lean_ctor_set(x_114, 1, x_103);
lean_ctor_set(x_114, 2, x_107);
lean_ctor_set(x_114, 3, x_113);
lean_inc(x_79);
x_115 = l_Lean_Syntax_node2(x_79, x_99, x_101, x_114);
lean_inc(x_79);
x_116 = l_Lean_Syntax_node3(x_79, x_93, x_95, x_97, x_115);
x_117 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_79);
x_118 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_118, 0, x_79);
lean_ctor_set(x_118, 1, x_117);
lean_inc(x_79);
x_119 = l_Lean_Syntax_node3(x_79, x_89, x_91, x_116, x_118);
x_120 = lean_mk_string_unchecked("null", 4, 4);
x_121 = l_Lean_Name_mkStr1(x_120);
x_122 = lean_box(2);
x_123 = l_Lean_Syntax_mkStrLit(x_10, x_122);
lean_dec(x_10);
x_124 = lean_mk_string_unchecked("false", 5, 5);
lean_inc(x_124);
x_125 = l_String_toSubstring_x27(x_124);
lean_inc(x_124);
x_126 = l_Lean_Name_mkStr1(x_124);
x_127 = l_Lean_addMacroScope(x_82, x_126, x_80);
x_128 = lean_mk_string_unchecked("Bool", 4, 4);
x_129 = l_Lean_Name_mkStr2(x_128, x_124);
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_109);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_111);
lean_inc(x_79);
x_132 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_132, 0, x_79);
lean_ctor_set(x_132, 1, x_125);
lean_ctor_set(x_132, 2, x_127);
lean_ctor_set(x_132, 3, x_131);
lean_inc(x_79);
x_133 = l_Lean_Syntax_node2(x_79, x_121, x_123, x_132);
x_134 = l_Lean_Syntax_node2(x_79, x_87, x_119, x_133);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_5);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_75);
return x_136;
}
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_137 = lean_ctor_get(x_7, 0);
lean_inc(x_137);
lean_dec(x_7);
x_138 = lean_st_ref_get(x_3, x_4);
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_138, 1);
lean_inc(x_140);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_141 = x_138;
} else {
 lean_dec_ref(x_138);
 x_141 = lean_box(0);
}
x_142 = lean_ctor_get(x_2, 5);
lean_inc(x_142);
x_143 = lean_box(0);
x_144 = lean_unbox(x_143);
x_145 = l_Lean_SourceInfo_fromRef(x_142, x_144);
lean_dec(x_142);
x_146 = lean_ctor_get(x_2, 10);
lean_inc(x_146);
lean_dec(x_2);
x_147 = lean_ctor_get(x_139, 0);
lean_inc(x_147);
lean_dec(x_139);
x_148 = l_Lean_Environment_mainModule(x_147);
lean_dec(x_147);
x_149 = lean_mk_string_unchecked("Lean", 4, 4);
x_150 = lean_mk_string_unchecked("Parser", 6, 6);
x_151 = lean_mk_string_unchecked("Term", 4, 4);
x_152 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_151);
lean_inc(x_150);
lean_inc(x_149);
x_153 = l_Lean_Name_mkStr4(x_149, x_150, x_151, x_152);
x_154 = lean_mk_string_unchecked("paren", 5, 5);
lean_inc(x_151);
lean_inc(x_150);
lean_inc(x_149);
x_155 = l_Lean_Name_mkStr4(x_149, x_150, x_151, x_154);
x_156 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_145);
x_157 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_157, 0, x_145);
lean_ctor_set(x_157, 1, x_156);
x_158 = lean_mk_string_unchecked("withAnnotateTerm", 16, 16);
lean_inc(x_149);
x_159 = l_Lean_Name_mkStr2(x_149, x_158);
x_160 = lean_mk_string_unchecked("with_annotate_term", 18, 18);
lean_inc(x_145);
x_161 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_161, 0, x_145);
lean_ctor_set(x_161, 1, x_160);
x_162 = lean_unsigned_to_nat(0u);
x_163 = l_Lean_Syntax_getArg(x_1, x_162);
x_164 = lean_mk_string_unchecked("explicit", 8, 8);
lean_inc(x_149);
x_165 = l_Lean_Name_mkStr4(x_149, x_150, x_151, x_164);
x_166 = lean_mk_string_unchecked("@", 1, 1);
lean_inc(x_145);
x_167 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_167, 0, x_145);
lean_ctor_set(x_167, 1, x_166);
x_168 = lean_mk_string_unchecked("ParserDescr.nonReservedSymbol", 29, 29);
x_169 = l_String_toSubstring_x27(x_168);
x_170 = lean_mk_string_unchecked("ParserDescr", 11, 11);
x_171 = lean_mk_string_unchecked("nonReservedSymbol", 17, 17);
lean_inc(x_171);
lean_inc(x_170);
x_172 = l_Lean_Name_mkStr2(x_170, x_171);
lean_inc(x_146);
lean_inc(x_148);
x_173 = l_Lean_addMacroScope(x_148, x_172, x_146);
x_174 = l_Lean_Name_mkStr3(x_149, x_170, x_171);
x_175 = lean_box(0);
lean_inc(x_174);
x_176 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_176, 0, x_174);
lean_ctor_set(x_176, 1, x_175);
x_177 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_177, 0, x_174);
x_178 = lean_box(0);
x_179 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_179, 0, x_177);
lean_ctor_set(x_179, 1, x_178);
x_180 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_180, 0, x_176);
lean_ctor_set(x_180, 1, x_179);
lean_inc(x_145);
x_181 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_181, 0, x_145);
lean_ctor_set(x_181, 1, x_169);
lean_ctor_set(x_181, 2, x_173);
lean_ctor_set(x_181, 3, x_180);
lean_inc(x_145);
x_182 = l_Lean_Syntax_node2(x_145, x_165, x_167, x_181);
lean_inc(x_145);
x_183 = l_Lean_Syntax_node3(x_145, x_159, x_161, x_163, x_182);
x_184 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_145);
x_185 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_185, 0, x_145);
lean_ctor_set(x_185, 1, x_184);
lean_inc(x_145);
x_186 = l_Lean_Syntax_node3(x_145, x_155, x_157, x_183, x_185);
x_187 = lean_mk_string_unchecked("null", 4, 4);
x_188 = l_Lean_Name_mkStr1(x_187);
x_189 = lean_box(2);
x_190 = l_Lean_Syntax_mkStrLit(x_137, x_189);
lean_dec(x_137);
x_191 = lean_mk_string_unchecked("false", 5, 5);
lean_inc(x_191);
x_192 = l_String_toSubstring_x27(x_191);
lean_inc(x_191);
x_193 = l_Lean_Name_mkStr1(x_191);
x_194 = l_Lean_addMacroScope(x_148, x_193, x_146);
x_195 = lean_mk_string_unchecked("Bool", 4, 4);
x_196 = l_Lean_Name_mkStr2(x_195, x_191);
x_197 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_197, 0, x_196);
lean_ctor_set(x_197, 1, x_175);
x_198 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_178);
lean_inc(x_145);
x_199 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_199, 0, x_145);
lean_ctor_set(x_199, 1, x_192);
lean_ctor_set(x_199, 2, x_194);
lean_ctor_set(x_199, 3, x_198);
lean_inc(x_145);
x_200 = l_Lean_Syntax_node2(x_145, x_188, x_190, x_199);
x_201 = l_Lean_Syntax_node2(x_145, x_153, x_186, x_200);
x_202 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_202, 0, x_201);
lean_ctor_set(x_202, 1, x_5);
if (lean_is_scalar(x_141)) {
 x_203 = lean_alloc_ctor(0, 2, 0);
} else {
 x_203 = x_141;
}
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set(x_203, 1, x_140);
return x_203;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr_processNonReserved(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Term_toParserDescr_processNonReserved___redArg(x_1, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr_processNonReserved___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_toParserDescr_processNonReserved___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr_processNonReserved___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Term_toParserDescr_processNonReserved(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Term_toParserDescr_isValidAtom(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; uint8_t x_9; uint8_t x_13; uint8_t x_14; uint8_t x_15; uint32_t x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; uint8_t x_32; uint32_t x_33; uint32_t x_34; uint8_t x_35; uint8_t x_36; uint8_t x_37; uint32_t x_43; uint8_t x_44; lean_object* x_45; uint32_t x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; lean_object* x_58; uint8_t x_59; uint8_t x_60; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_string_utf8_byte_size(x_1);
x_4 = l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(x_1, x_3, x_2);
x_5 = l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(x_1, x_4, x_3);
x_6 = lean_string_utf8_extract(x_1, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
x_58 = lean_string_utf8_byte_size(x_6);
x_59 = l_instDecidableEqPos(x_58, x_2);
if (x_59 == 0)
{
uint32_t x_80; lean_object* x_81; uint32_t x_82; uint8_t x_83; 
x_80 = lean_string_utf8_get(x_6, x_2);
x_81 = lean_unsigned_to_nat(39u);
x_82 = l_Char_ofNat(x_81);
x_83 = l_instDecidableEqChar(x_80, x_82);
if (x_83 == 0)
{
lean_object* x_84; uint8_t x_85; 
x_84 = lean_box(1);
x_85 = lean_unbox(x_84);
x_60 = x_85;
goto block_79;
}
else
{
lean_object* x_86; uint8_t x_87; 
x_86 = lean_mk_string_unchecked("''", 2, 2);
x_87 = l_String_isPrefixOf(x_86, x_6);
lean_dec(x_86);
if (x_87 == 0)
{
lean_dec(x_58);
lean_dec(x_6);
return x_87;
}
else
{
x_60 = x_87;
goto block_79;
}
}
}
else
{
lean_object* x_88; uint8_t x_89; 
lean_dec(x_58);
lean_dec(x_6);
x_88 = lean_box(0);
x_89 = lean_unbox(x_88);
return x_89;
}
block_12:
{
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_string_utf8_byte_size(x_6);
x_11 = l_String_anyAux___at___addParenHeuristic_spec__0(x_6, x_10, x_2);
lean_dec(x_10);
lean_dec(x_6);
if (x_11 == 0)
{
return x_7;
}
else
{
return x_9;
}
}
else
{
lean_dec(x_6);
return x_8;
}
}
block_23:
{
if (x_15 == 0)
{
lean_object* x_16; uint32_t x_17; uint32_t x_18; uint8_t x_19; 
x_16 = lean_unsigned_to_nat(48u);
x_17 = lean_uint32_of_nat(x_16);
x_18 = lean_string_utf8_get(x_6, x_2);
x_19 = lean_uint32_dec_le(x_17, x_18);
if (x_19 == 0)
{
x_7 = x_13;
x_8 = x_15;
x_9 = x_19;
goto block_12;
}
else
{
lean_object* x_20; uint32_t x_21; uint8_t x_22; 
x_20 = lean_unsigned_to_nat(57u);
x_21 = lean_uint32_of_nat(x_20);
x_22 = lean_uint32_dec_le(x_18, x_21);
x_7 = x_13;
x_8 = x_15;
x_9 = x_22;
goto block_12;
}
}
else
{
lean_dec(x_6);
return x_14;
}
}
block_31:
{
if (x_27 == 0)
{
lean_object* x_28; uint32_t x_29; uint8_t x_30; 
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_string_utf8_get(x_6, x_28);
x_30 = l_instDecidableEqChar(x_29, x_24);
x_13 = x_25;
x_14 = x_26;
x_15 = x_30;
goto block_23;
}
else
{
lean_dec(x_6);
return x_26;
}
}
block_42:
{
if (x_37 == 0)
{
lean_object* x_38; uint32_t x_39; uint8_t x_40; 
x_38 = lean_unsigned_to_nat(95u);
x_39 = l_Char_ofNat(x_38);
x_40 = l_instDecidableEqChar(x_33, x_39);
if (x_40 == 0)
{
uint8_t x_41; 
x_41 = l_Lean_isLetterLike(x_33);
x_24 = x_34;
x_25 = x_35;
x_26 = x_36;
x_27 = x_41;
goto block_31;
}
else
{
x_24 = x_34;
x_25 = x_35;
x_26 = x_36;
x_27 = x_40;
goto block_31;
}
}
else
{
lean_dec(x_6);
return x_32;
}
}
block_57:
{
if (x_49 == 0)
{
lean_object* x_50; uint32_t x_51; uint32_t x_52; uint8_t x_53; 
x_50 = lean_unsigned_to_nat(97u);
x_51 = lean_uint32_of_nat(x_50);
x_52 = lean_string_utf8_get(x_6, x_45);
x_53 = lean_uint32_dec_le(x_51, x_52);
if (x_53 == 0)
{
x_32 = x_44;
x_33 = x_43;
x_34 = x_46;
x_35 = x_47;
x_36 = x_48;
x_37 = x_53;
goto block_42;
}
else
{
lean_object* x_54; uint32_t x_55; uint8_t x_56; 
x_54 = lean_unsigned_to_nat(122u);
x_55 = lean_uint32_of_nat(x_54);
x_56 = lean_uint32_dec_le(x_52, x_55);
x_32 = x_44;
x_33 = x_43;
x_34 = x_46;
x_35 = x_47;
x_36 = x_48;
x_37 = x_56;
goto block_42;
}
}
else
{
lean_dec(x_6);
return x_44;
}
}
block_79:
{
uint32_t x_61; lean_object* x_62; uint32_t x_63; uint8_t x_64; 
x_61 = lean_string_utf8_get(x_6, x_2);
x_62 = lean_unsigned_to_nat(34u);
x_63 = l_Char_ofNat(x_62);
x_64 = l_instDecidableEqChar(x_61, x_63);
if (x_64 == 0)
{
uint32_t x_65; uint8_t x_66; 
x_65 = l_Lean_idBeginEscape;
x_66 = l_instDecidableEqChar(x_61, x_65);
if (x_66 == 0)
{
lean_object* x_67; uint32_t x_68; uint8_t x_69; 
x_67 = lean_unsigned_to_nat(96u);
x_68 = l_Char_ofNat(x_67);
x_69 = l_instDecidableEqChar(x_61, x_68);
if (x_69 == 0)
{
lean_dec(x_58);
x_13 = x_60;
x_14 = x_66;
x_15 = x_69;
goto block_23;
}
else
{
lean_object* x_70; uint8_t x_71; 
x_70 = lean_unsigned_to_nat(1u);
x_71 = l_instDecidableEqPos(x_58, x_70);
lean_dec(x_58);
if (x_71 == 0)
{
uint32_t x_72; lean_object* x_73; uint32_t x_74; uint8_t x_75; 
x_72 = lean_string_utf8_get(x_6, x_70);
x_73 = lean_unsigned_to_nat(65u);
x_74 = lean_uint32_of_nat(x_73);
x_75 = lean_uint32_dec_le(x_74, x_72);
if (x_75 == 0)
{
x_43 = x_72;
x_44 = x_71;
x_45 = x_70;
x_46 = x_65;
x_47 = x_60;
x_48 = x_66;
x_49 = x_75;
goto block_57;
}
else
{
lean_object* x_76; uint32_t x_77; uint8_t x_78; 
x_76 = lean_unsigned_to_nat(90u);
x_77 = lean_uint32_of_nat(x_76);
x_78 = lean_uint32_dec_le(x_72, x_77);
x_43 = x_72;
x_44 = x_71;
x_45 = x_70;
x_46 = x_65;
x_47 = x_60;
x_48 = x_66;
x_49 = x_78;
goto block_57;
}
}
else
{
x_24 = x_65;
x_25 = x_60;
x_26 = x_66;
x_27 = x_71;
goto block_31;
}
}
}
else
{
lean_dec(x_58);
lean_dec(x_6);
return x_64;
}
}
else
{
lean_dec(x_58);
lean_dec(x_6);
return x_59;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr_isValidAtom___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Term_toParserDescr_isValidAtom(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr_processAtom(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = l_Lean_Syntax_isStrLit_x3f(x_12);
lean_dec(x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
lean_dec(x_8);
x_14 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0_spec__6___redArg(x_10);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_92; 
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 x_16 = x_13;
} else {
 lean_dec_ref(x_13);
 x_16 = lean_box(0);
}
x_92 = l_Lean_Elab_Term_toParserDescr_isValidAtom(x_15);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
lean_dec(x_16);
lean_dec(x_15);
x_93 = lean_mk_string_unchecked("invalid atom", 12, 12);
x_94 = l_Lean_stringToMessageData(x_93);
lean_dec(x_93);
x_95 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0_spec__3___redArg(x_1, x_94, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_8);
x_96 = !lean_is_exclusive(x_95);
if (x_96 == 0)
{
return x_95;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_95, 0);
x_98 = lean_ctor_get(x_95, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_95);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
else
{
uint8_t x_100; lean_object* x_101; uint8_t x_102; uint8_t x_103; 
x_100 = lean_ctor_get_uint8(x_2, sizeof(void*)*1 + 2);
x_101 = lean_box(0);
x_102 = lean_unbox(x_101);
x_103 = l___private_Lean_Parser_Basic_0__Lean_Parser_beqLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8856_(x_100, x_102);
if (x_103 == 0)
{
uint8_t x_104; 
x_104 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
if (x_104 == 0)
{
x_17 = x_8;
x_18 = x_10;
x_19 = x_9;
x_20 = x_104;
goto block_91;
}
else
{
lean_object* x_105; uint8_t x_106; 
lean_dec(x_16);
x_105 = lean_st_ref_get(x_9, x_10);
x_106 = !lean_is_exclusive(x_105);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_107 = lean_ctor_get(x_105, 0);
x_108 = lean_ctor_get(x_8, 5);
lean_inc(x_108);
x_109 = l_Lean_SourceInfo_fromRef(x_108, x_103);
lean_dec(x_108);
x_110 = lean_ctor_get(x_8, 10);
lean_inc(x_110);
lean_dec(x_8);
x_111 = lean_ctor_get(x_107, 0);
lean_inc(x_111);
lean_dec(x_107);
x_112 = l_Lean_Environment_mainModule(x_111);
lean_dec(x_111);
x_113 = lean_mk_string_unchecked("Lean", 4, 4);
x_114 = lean_mk_string_unchecked("Parser", 6, 6);
x_115 = lean_mk_string_unchecked("Term", 4, 4);
x_116 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_113);
x_117 = l_Lean_Name_mkStr4(x_113, x_114, x_115, x_116);
x_118 = lean_mk_string_unchecked("ParserDescr.nonReservedSymbol", 29, 29);
x_119 = l_String_toSubstring_x27(x_118);
x_120 = lean_mk_string_unchecked("ParserDescr", 11, 11);
x_121 = lean_mk_string_unchecked("nonReservedSymbol", 17, 17);
lean_inc(x_121);
lean_inc(x_120);
x_122 = l_Lean_Name_mkStr2(x_120, x_121);
lean_inc(x_110);
lean_inc(x_112);
x_123 = l_Lean_addMacroScope(x_112, x_122, x_110);
x_124 = l_Lean_Name_mkStr3(x_113, x_120, x_121);
x_125 = lean_box(0);
lean_inc(x_124);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
x_127 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_127, 0, x_124);
x_128 = lean_box(0);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_126);
lean_ctor_set(x_130, 1, x_129);
lean_inc(x_109);
x_131 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_131, 0, x_109);
lean_ctor_set(x_131, 1, x_119);
lean_ctor_set(x_131, 2, x_123);
lean_ctor_set(x_131, 3, x_130);
x_132 = lean_mk_string_unchecked("null", 4, 4);
x_133 = l_Lean_Name_mkStr1(x_132);
x_134 = lean_box(2);
x_135 = l_Lean_Syntax_mkStrLit(x_15, x_134);
lean_dec(x_15);
x_136 = lean_mk_string_unchecked("false", 5, 5);
lean_inc(x_136);
x_137 = l_String_toSubstring_x27(x_136);
lean_inc(x_136);
x_138 = l_Lean_Name_mkStr1(x_136);
x_139 = l_Lean_addMacroScope(x_112, x_138, x_110);
x_140 = lean_mk_string_unchecked("Bool", 4, 4);
x_141 = l_Lean_Name_mkStr2(x_140, x_136);
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_125);
x_143 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_128);
lean_inc(x_109);
x_144 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_144, 0, x_109);
lean_ctor_set(x_144, 1, x_137);
lean_ctor_set(x_144, 2, x_139);
lean_ctor_set(x_144, 3, x_143);
lean_inc(x_109);
x_145 = l_Lean_Syntax_node2(x_109, x_133, x_135, x_144);
x_146 = l_Lean_Syntax_node2(x_109, x_117, x_131, x_145);
x_147 = lean_unsigned_to_nat(1u);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_147);
lean_ctor_set(x_105, 0, x_148);
return x_105;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_149 = lean_ctor_get(x_105, 0);
x_150 = lean_ctor_get(x_105, 1);
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_105);
x_151 = lean_ctor_get(x_8, 5);
lean_inc(x_151);
x_152 = l_Lean_SourceInfo_fromRef(x_151, x_103);
lean_dec(x_151);
x_153 = lean_ctor_get(x_8, 10);
lean_inc(x_153);
lean_dec(x_8);
x_154 = lean_ctor_get(x_149, 0);
lean_inc(x_154);
lean_dec(x_149);
x_155 = l_Lean_Environment_mainModule(x_154);
lean_dec(x_154);
x_156 = lean_mk_string_unchecked("Lean", 4, 4);
x_157 = lean_mk_string_unchecked("Parser", 6, 6);
x_158 = lean_mk_string_unchecked("Term", 4, 4);
x_159 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_156);
x_160 = l_Lean_Name_mkStr4(x_156, x_157, x_158, x_159);
x_161 = lean_mk_string_unchecked("ParserDescr.nonReservedSymbol", 29, 29);
x_162 = l_String_toSubstring_x27(x_161);
x_163 = lean_mk_string_unchecked("ParserDescr", 11, 11);
x_164 = lean_mk_string_unchecked("nonReservedSymbol", 17, 17);
lean_inc(x_164);
lean_inc(x_163);
x_165 = l_Lean_Name_mkStr2(x_163, x_164);
lean_inc(x_153);
lean_inc(x_155);
x_166 = l_Lean_addMacroScope(x_155, x_165, x_153);
x_167 = l_Lean_Name_mkStr3(x_156, x_163, x_164);
x_168 = lean_box(0);
lean_inc(x_167);
x_169 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_169, 0, x_167);
lean_ctor_set(x_169, 1, x_168);
x_170 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_170, 0, x_167);
x_171 = lean_box(0);
x_172 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_172, 0, x_170);
lean_ctor_set(x_172, 1, x_171);
x_173 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_173, 0, x_169);
lean_ctor_set(x_173, 1, x_172);
lean_inc(x_152);
x_174 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_174, 0, x_152);
lean_ctor_set(x_174, 1, x_162);
lean_ctor_set(x_174, 2, x_166);
lean_ctor_set(x_174, 3, x_173);
x_175 = lean_mk_string_unchecked("null", 4, 4);
x_176 = l_Lean_Name_mkStr1(x_175);
x_177 = lean_box(2);
x_178 = l_Lean_Syntax_mkStrLit(x_15, x_177);
lean_dec(x_15);
x_179 = lean_mk_string_unchecked("false", 5, 5);
lean_inc(x_179);
x_180 = l_String_toSubstring_x27(x_179);
lean_inc(x_179);
x_181 = l_Lean_Name_mkStr1(x_179);
x_182 = l_Lean_addMacroScope(x_155, x_181, x_153);
x_183 = lean_mk_string_unchecked("Bool", 4, 4);
x_184 = l_Lean_Name_mkStr2(x_183, x_179);
x_185 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_168);
x_186 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_171);
lean_inc(x_152);
x_187 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_187, 0, x_152);
lean_ctor_set(x_187, 1, x_180);
lean_ctor_set(x_187, 2, x_182);
lean_ctor_set(x_187, 3, x_186);
lean_inc(x_152);
x_188 = l_Lean_Syntax_node2(x_152, x_176, x_178, x_187);
x_189 = l_Lean_Syntax_node2(x_152, x_160, x_174, x_188);
x_190 = lean_unsigned_to_nat(1u);
x_191 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_191, 0, x_189);
lean_ctor_set(x_191, 1, x_190);
x_192 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_192, 0, x_191);
lean_ctor_set(x_192, 1, x_150);
return x_192;
}
}
}
else
{
lean_object* x_193; uint8_t x_194; 
x_193 = lean_box(0);
x_194 = lean_unbox(x_193);
x_17 = x_8;
x_18 = x_10;
x_19 = x_9;
x_20 = x_194;
goto block_91;
}
}
block_91:
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_st_ref_get(x_19, x_18);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_17, 5);
lean_inc(x_24);
x_25 = l_Lean_SourceInfo_fromRef(x_24, x_20);
lean_dec(x_24);
x_26 = lean_ctor_get(x_17, 10);
lean_inc(x_26);
lean_dec(x_17);
x_27 = lean_ctor_get(x_23, 0);
lean_inc(x_27);
lean_dec(x_23);
x_28 = l_Lean_Environment_mainModule(x_27);
lean_dec(x_27);
x_29 = lean_mk_string_unchecked("Lean", 4, 4);
x_30 = lean_mk_string_unchecked("Parser", 6, 6);
x_31 = lean_mk_string_unchecked("Term", 4, 4);
x_32 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_29);
x_33 = l_Lean_Name_mkStr4(x_29, x_30, x_31, x_32);
x_34 = lean_mk_string_unchecked("ParserDescr.symbol", 18, 18);
x_35 = l_String_toSubstring_x27(x_34);
x_36 = lean_mk_string_unchecked("ParserDescr", 11, 11);
x_37 = lean_mk_string_unchecked("symbol", 6, 6);
lean_inc(x_37);
lean_inc(x_36);
x_38 = l_Lean_Name_mkStr2(x_36, x_37);
x_39 = l_Lean_addMacroScope(x_28, x_38, x_26);
x_40 = l_Lean_Name_mkStr3(x_29, x_36, x_37);
x_41 = lean_box(0);
lean_inc(x_40);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
if (lean_is_scalar(x_16)) {
 x_43 = lean_alloc_ctor(0, 1, 0);
} else {
 x_43 = x_16;
 lean_ctor_set_tag(x_43, 0);
}
lean_ctor_set(x_43, 0, x_40);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_42);
lean_ctor_set(x_46, 1, x_45);
lean_inc(x_25);
x_47 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_47, 0, x_25);
lean_ctor_set(x_47, 1, x_35);
lean_ctor_set(x_47, 2, x_39);
lean_ctor_set(x_47, 3, x_46);
x_48 = lean_mk_string_unchecked("null", 4, 4);
x_49 = l_Lean_Name_mkStr1(x_48);
x_50 = lean_box(2);
x_51 = l_Lean_Syntax_mkStrLit(x_15, x_50);
lean_dec(x_15);
lean_inc(x_25);
x_52 = l_Lean_Syntax_node1(x_25, x_49, x_51);
x_53 = l_Lean_Syntax_node2(x_25, x_33, x_47, x_52);
x_54 = lean_unsigned_to_nat(1u);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set(x_21, 0, x_55);
return x_21;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_56 = lean_ctor_get(x_21, 0);
x_57 = lean_ctor_get(x_21, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_21);
x_58 = lean_ctor_get(x_17, 5);
lean_inc(x_58);
x_59 = l_Lean_SourceInfo_fromRef(x_58, x_20);
lean_dec(x_58);
x_60 = lean_ctor_get(x_17, 10);
lean_inc(x_60);
lean_dec(x_17);
x_61 = lean_ctor_get(x_56, 0);
lean_inc(x_61);
lean_dec(x_56);
x_62 = l_Lean_Environment_mainModule(x_61);
lean_dec(x_61);
x_63 = lean_mk_string_unchecked("Lean", 4, 4);
x_64 = lean_mk_string_unchecked("Parser", 6, 6);
x_65 = lean_mk_string_unchecked("Term", 4, 4);
x_66 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_63);
x_67 = l_Lean_Name_mkStr4(x_63, x_64, x_65, x_66);
x_68 = lean_mk_string_unchecked("ParserDescr.symbol", 18, 18);
x_69 = l_String_toSubstring_x27(x_68);
x_70 = lean_mk_string_unchecked("ParserDescr", 11, 11);
x_71 = lean_mk_string_unchecked("symbol", 6, 6);
lean_inc(x_71);
lean_inc(x_70);
x_72 = l_Lean_Name_mkStr2(x_70, x_71);
x_73 = l_Lean_addMacroScope(x_62, x_72, x_60);
x_74 = l_Lean_Name_mkStr3(x_63, x_70, x_71);
x_75 = lean_box(0);
lean_inc(x_74);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
if (lean_is_scalar(x_16)) {
 x_77 = lean_alloc_ctor(0, 1, 0);
} else {
 x_77 = x_16;
 lean_ctor_set_tag(x_77, 0);
}
lean_ctor_set(x_77, 0, x_74);
x_78 = lean_box(0);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_76);
lean_ctor_set(x_80, 1, x_79);
lean_inc(x_59);
x_81 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_81, 0, x_59);
lean_ctor_set(x_81, 1, x_69);
lean_ctor_set(x_81, 2, x_73);
lean_ctor_set(x_81, 3, x_80);
x_82 = lean_mk_string_unchecked("null", 4, 4);
x_83 = l_Lean_Name_mkStr1(x_82);
x_84 = lean_box(2);
x_85 = l_Lean_Syntax_mkStrLit(x_15, x_84);
lean_dec(x_15);
lean_inc(x_59);
x_86 = l_Lean_Syntax_node1(x_59, x_83, x_85);
x_87 = l_Lean_Syntax_node2(x_59, x_67, x_81, x_86);
x_88 = lean_unsigned_to_nat(1u);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_57);
return x_90;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr_processAtom___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Term_toParserDescr_processAtom(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr_processParserCategory(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_126; uint8_t x_147; 
x_27 = lean_unsigned_to_nat(0u);
x_28 = l_Lean_Syntax_getArg(x_1, x_27);
x_29 = l_Lean_Syntax_getId(x_28);
lean_dec(x_28);
x_30 = lean_erase_macro_scopes(x_29);
x_147 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
if (x_147 == 0)
{
x_126 = x_147;
goto block_146;
}
else
{
lean_object* x_148; uint8_t x_149; 
x_148 = lean_ctor_get(x_2, 0);
x_149 = lean_name_eq(x_30, x_148);
x_126 = x_149;
goto block_146;
}
block_26:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = l___private_Init_Data_Repr_0__Nat_reprFast(x_15);
x_20 = lean_box(2);
x_21 = l_Lean_Syntax_mkNumLit(x_19, x_20);
lean_inc(x_12);
x_22 = l_Lean_Syntax_node2(x_12, x_11, x_18, x_21);
x_23 = l_Lean_Syntax_node2(x_12, x_14, x_16, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_17);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_13);
return x_25;
}
block_125:
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_st_ref_get(x_33, x_31);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_38 = lean_ctor_get(x_36, 0);
x_39 = lean_ctor_get(x_36, 1);
x_40 = lean_ctor_get(x_32, 5);
lean_inc(x_40);
x_41 = lean_box(0);
x_42 = lean_unbox(x_41);
x_43 = l_Lean_SourceInfo_fromRef(x_40, x_42);
lean_dec(x_40);
x_44 = lean_ctor_get(x_32, 10);
lean_inc(x_44);
lean_dec(x_32);
x_45 = lean_ctor_get(x_38, 0);
lean_inc(x_45);
lean_dec(x_38);
x_46 = l_Lean_Environment_mainModule(x_45);
lean_dec(x_45);
x_47 = lean_mk_string_unchecked("Lean", 4, 4);
x_48 = lean_mk_string_unchecked("Parser", 6, 6);
x_49 = lean_mk_string_unchecked("Term", 4, 4);
x_50 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
x_51 = l_Lean_Name_mkStr4(x_47, x_48, x_49, x_50);
x_52 = lean_mk_string_unchecked("ParserDescr.cat", 15, 15);
x_53 = l_String_toSubstring_x27(x_52);
x_54 = lean_mk_string_unchecked("ParserDescr", 11, 11);
x_55 = lean_mk_string_unchecked("cat", 3, 3);
lean_inc(x_55);
lean_inc(x_54);
x_56 = l_Lean_Name_mkStr2(x_54, x_55);
x_57 = l_Lean_addMacroScope(x_46, x_56, x_44);
lean_inc(x_47);
x_58 = l_Lean_Name_mkStr3(x_47, x_54, x_55);
x_59 = lean_box(0);
lean_inc(x_58);
lean_ctor_set_tag(x_36, 1);
lean_ctor_set(x_36, 1, x_59);
lean_ctor_set(x_36, 0, x_58);
x_60 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_60, 0, x_58);
x_61 = lean_box(0);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_36);
lean_ctor_set(x_63, 1, x_62);
lean_inc(x_43);
x_64 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_64, 0, x_43);
lean_ctor_set(x_64, 1, x_53);
lean_ctor_set(x_64, 2, x_57);
lean_ctor_set(x_64, 3, x_63);
x_65 = lean_mk_string_unchecked("null", 4, 4);
x_66 = l_Lean_Name_mkStr1(x_65);
lean_inc(x_30);
x_67 = l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(x_59, x_30);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; 
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_47);
x_68 = l_Lean_quoteNameMk(x_30);
x_11 = x_66;
x_12 = x_43;
x_13 = x_39;
x_14 = x_51;
x_15 = x_35;
x_16 = x_64;
x_17 = x_34;
x_18 = x_68;
goto block_26;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_30);
x_69 = lean_ctor_get(x_67, 0);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_mk_string_unchecked("quotedName", 10, 10);
x_71 = l_Lean_Name_mkStr4(x_47, x_48, x_49, x_70);
x_72 = lean_mk_string_unchecked("`", 1, 1);
x_73 = lean_mk_string_unchecked(".", 1, 1);
x_74 = l_String_intercalate(x_73, x_69);
lean_dec(x_73);
x_75 = lean_string_append(x_72, x_74);
lean_dec(x_74);
x_76 = lean_box(2);
x_77 = l_Lean_Syntax_mkNameLit(x_75, x_76);
x_78 = lean_mk_empty_array_with_capacity(x_34);
x_79 = lean_array_push(x_78, x_77);
x_80 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_80, 0, x_76);
lean_ctor_set(x_80, 1, x_71);
lean_ctor_set(x_80, 2, x_79);
x_11 = x_66;
x_12 = x_43;
x_13 = x_39;
x_14 = x_51;
x_15 = x_35;
x_16 = x_64;
x_17 = x_34;
x_18 = x_80;
goto block_26;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_81 = lean_ctor_get(x_36, 0);
x_82 = lean_ctor_get(x_36, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_36);
x_83 = lean_ctor_get(x_32, 5);
lean_inc(x_83);
x_84 = lean_box(0);
x_85 = lean_unbox(x_84);
x_86 = l_Lean_SourceInfo_fromRef(x_83, x_85);
lean_dec(x_83);
x_87 = lean_ctor_get(x_32, 10);
lean_inc(x_87);
lean_dec(x_32);
x_88 = lean_ctor_get(x_81, 0);
lean_inc(x_88);
lean_dec(x_81);
x_89 = l_Lean_Environment_mainModule(x_88);
lean_dec(x_88);
x_90 = lean_mk_string_unchecked("Lean", 4, 4);
x_91 = lean_mk_string_unchecked("Parser", 6, 6);
x_92 = lean_mk_string_unchecked("Term", 4, 4);
x_93 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
x_94 = l_Lean_Name_mkStr4(x_90, x_91, x_92, x_93);
x_95 = lean_mk_string_unchecked("ParserDescr.cat", 15, 15);
x_96 = l_String_toSubstring_x27(x_95);
x_97 = lean_mk_string_unchecked("ParserDescr", 11, 11);
x_98 = lean_mk_string_unchecked("cat", 3, 3);
lean_inc(x_98);
lean_inc(x_97);
x_99 = l_Lean_Name_mkStr2(x_97, x_98);
x_100 = l_Lean_addMacroScope(x_89, x_99, x_87);
lean_inc(x_90);
x_101 = l_Lean_Name_mkStr3(x_90, x_97, x_98);
x_102 = lean_box(0);
lean_inc(x_101);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
x_104 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_104, 0, x_101);
x_105 = lean_box(0);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_103);
lean_ctor_set(x_107, 1, x_106);
lean_inc(x_86);
x_108 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_108, 0, x_86);
lean_ctor_set(x_108, 1, x_96);
lean_ctor_set(x_108, 2, x_100);
lean_ctor_set(x_108, 3, x_107);
x_109 = lean_mk_string_unchecked("null", 4, 4);
x_110 = l_Lean_Name_mkStr1(x_109);
lean_inc(x_30);
x_111 = l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(x_102, x_30);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; 
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_90);
x_112 = l_Lean_quoteNameMk(x_30);
x_11 = x_110;
x_12 = x_86;
x_13 = x_82;
x_14 = x_94;
x_15 = x_35;
x_16 = x_108;
x_17 = x_34;
x_18 = x_112;
goto block_26;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_dec(x_30);
x_113 = lean_ctor_get(x_111, 0);
lean_inc(x_113);
lean_dec(x_111);
x_114 = lean_mk_string_unchecked("quotedName", 10, 10);
x_115 = l_Lean_Name_mkStr4(x_90, x_91, x_92, x_114);
x_116 = lean_mk_string_unchecked("`", 1, 1);
x_117 = lean_mk_string_unchecked(".", 1, 1);
x_118 = l_String_intercalate(x_117, x_113);
lean_dec(x_117);
x_119 = lean_string_append(x_116, x_118);
lean_dec(x_118);
x_120 = lean_box(2);
x_121 = l_Lean_Syntax_mkNameLit(x_119, x_120);
x_122 = lean_mk_empty_array_with_capacity(x_34);
x_123 = lean_array_push(x_122, x_121);
x_124 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_124, 0, x_120);
lean_ctor_set(x_124, 1, x_115);
lean_ctor_set(x_124, 2, x_123);
x_11 = x_110;
x_12 = x_86;
x_13 = x_82;
x_14 = x_94;
x_15 = x_35;
x_16 = x_108;
x_17 = x_34;
x_18 = x_124;
goto block_26;
}
}
}
block_146:
{
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_127 = lean_unsigned_to_nat(1u);
x_128 = l_Lean_Syntax_getArg(x_1, x_127);
x_129 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandOptPrecedence___boxed), 3, 1);
lean_closure_set(x_129, 0, x_128);
lean_inc(x_8);
x_130 = l_Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0___redArg(x_129, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; 
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; 
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
lean_dec(x_130);
x_31 = x_132;
x_32 = x_8;
x_33 = x_9;
x_34 = x_127;
x_35 = x_27;
goto block_125;
}
else
{
lean_object* x_133; lean_object* x_134; 
x_133 = lean_ctor_get(x_130, 1);
lean_inc(x_133);
lean_dec(x_130);
x_134 = lean_ctor_get(x_131, 0);
lean_inc(x_134);
lean_dec(x_131);
x_31 = x_133;
x_32 = x_8;
x_33 = x_9;
x_34 = x_127;
x_35 = x_134;
goto block_125;
}
}
else
{
uint8_t x_135; 
lean_dec(x_30);
lean_dec(x_8);
x_135 = !lean_is_exclusive(x_130);
if (x_135 == 0)
{
return x_130;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_130, 0);
x_137 = lean_ctor_get(x_130, 1);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_130);
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
return x_138;
}
}
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; 
lean_dec(x_30);
x_139 = lean_mk_string_unchecked("invalid atomic left recursive syntax", 36, 36);
x_140 = l_Lean_stringToMessageData(x_139);
lean_dec(x_139);
x_141 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0_spec__3___redArg(x_1, x_140, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_8);
x_142 = !lean_is_exclusive(x_141);
if (x_142 == 0)
{
return x_141;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_143 = lean_ctor_get(x_141, 0);
x_144 = lean_ctor_get(x_141, 1);
lean_inc(x_144);
lean_inc(x_143);
lean_dec(x_141);
x_145 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
return x_145;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr_processParserCategory___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Term_toParserDescr_processParserCategory(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr_ensureNoPrec(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = l_Lean_Syntax_isNone(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_mk_string_unchecked("unexpected precedence", 21, 21);
x_15 = l_Lean_stringToMessageData(x_14);
lean_dec(x_14);
x_16 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0_spec__3___redArg(x_12, x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_12);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_12);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_10);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr_ensureNoPrec___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Term_toParserDescr_ensureNoPrec(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr_process(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; 
lean_inc(x_1);
x_11 = l_Lean_Syntax_getKind(x_1);
x_12 = lean_mk_string_unchecked("null", 4, 4);
x_13 = l_Lean_Name_mkStr1(x_12);
x_14 = lean_name_eq(x_11, x_13);
lean_dec(x_13);
x_15 = lean_ctor_get(x_8, 5);
lean_inc(x_15);
x_16 = l_Lean_replaceRef(x_1, x_15);
lean_dec(x_15);
x_17 = lean_ctor_get(x_8, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_8, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_8, 2);
lean_inc(x_19);
x_20 = lean_ctor_get(x_8, 3);
lean_inc(x_20);
x_21 = lean_ctor_get(x_8, 4);
lean_inc(x_21);
x_22 = lean_ctor_get(x_8, 6);
lean_inc(x_22);
x_23 = lean_ctor_get(x_8, 7);
lean_inc(x_23);
x_24 = lean_ctor_get(x_8, 8);
lean_inc(x_24);
x_25 = lean_ctor_get(x_8, 9);
lean_inc(x_25);
x_26 = lean_ctor_get(x_8, 10);
lean_inc(x_26);
x_27 = lean_ctor_get_uint8(x_8, sizeof(void*)*13);
x_28 = lean_ctor_get(x_8, 11);
lean_inc(x_28);
x_29 = lean_ctor_get_uint8(x_8, sizeof(void*)*13 + 1);
x_30 = lean_ctor_get(x_8, 12);
lean_inc(x_30);
lean_dec(x_8);
x_31 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_31, 0, x_17);
lean_ctor_set(x_31, 1, x_18);
lean_ctor_set(x_31, 2, x_19);
lean_ctor_set(x_31, 3, x_20);
lean_ctor_set(x_31, 4, x_21);
lean_ctor_set(x_31, 5, x_16);
lean_ctor_set(x_31, 6, x_22);
lean_ctor_set(x_31, 7, x_23);
lean_ctor_set(x_31, 8, x_24);
lean_ctor_set(x_31, 9, x_25);
lean_ctor_set(x_31, 10, x_26);
lean_ctor_set(x_31, 11, x_28);
lean_ctor_set(x_31, 12, x_30);
lean_ctor_set_uint8(x_31, sizeof(void*)*13, x_27);
lean_ctor_set_uint8(x_31, sizeof(void*)*13 + 1, x_29);
if (x_14 == 0)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_mk_string_unchecked("choice", 6, 6);
x_33 = l_Lean_Name_mkStr1(x_32);
x_34 = lean_name_eq(x_11, x_33);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_35 = lean_mk_string_unchecked("Lean", 4, 4);
x_36 = lean_mk_string_unchecked("Parser", 6, 6);
x_37 = lean_mk_string_unchecked("Syntax", 6, 6);
x_38 = lean_mk_string_unchecked("paren", 5, 5);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
x_39 = l_Lean_Name_mkStr4(x_35, x_36, x_37, x_38);
x_40 = lean_name_eq(x_11, x_39);
lean_dec(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_41 = lean_mk_string_unchecked("cat", 3, 3);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
x_42 = l_Lean_Name_mkStr4(x_35, x_36, x_37, x_41);
x_43 = lean_name_eq(x_11, x_42);
lean_dec(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_44 = lean_mk_string_unchecked("unary", 5, 5);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
x_45 = l_Lean_Name_mkStr4(x_35, x_36, x_37, x_44);
x_46 = lean_name_eq(x_11, x_45);
lean_dec(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_47 = lean_mk_string_unchecked("binary", 6, 6);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
x_48 = l_Lean_Name_mkStr4(x_35, x_36, x_37, x_47);
x_49 = lean_name_eq(x_11, x_48);
lean_dec(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_50 = lean_mk_string_unchecked("sepBy", 5, 5);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
x_51 = l_Lean_Name_mkStr4(x_35, x_36, x_37, x_50);
x_52 = lean_name_eq(x_11, x_51);
lean_dec(x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_53 = lean_mk_string_unchecked("sepBy1", 6, 6);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
x_54 = l_Lean_Name_mkStr4(x_35, x_36, x_37, x_53);
x_55 = lean_name_eq(x_11, x_54);
lean_dec(x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_56 = lean_mk_string_unchecked("atom", 4, 4);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
x_57 = l_Lean_Name_mkStr4(x_35, x_36, x_37, x_56);
x_58 = lean_name_eq(x_11, x_57);
lean_dec(x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_59 = lean_mk_string_unchecked("nonReserved", 11, 11);
x_60 = l_Lean_Name_mkStr4(x_35, x_36, x_37, x_59);
x_61 = lean_name_eq(x_11, x_60);
lean_dec(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
lean_inc(x_1);
x_62 = lean_alloc_closure((void*)(l_Lean_Macro_expandMacro_x3f), 3, 1);
lean_closure_set(x_62, 0, x_1);
lean_inc(x_31);
lean_inc(x_4);
x_63 = l_Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0___redArg(x_62, x_4, x_5, x_6, x_7, x_31, x_9, x_10);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = lean_mk_string_unchecked("unexpected syntax kind of category `syntax`: ", 45, 45);
x_67 = l_Lean_stringToMessageData(x_66);
lean_dec(x_66);
x_68 = l_Lean_MessageData_ofName(x_11);
x_69 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_mk_string_unchecked("", 0, 0);
x_71 = l_Lean_stringToMessageData(x_70);
lean_dec(x_70);
x_72 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_71);
x_73 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0_spec__3___redArg(x_1, x_72, x_2, x_3, x_4, x_5, x_6, x_7, x_31, x_9, x_65);
lean_dec(x_9);
lean_dec(x_31);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; 
lean_dec(x_11);
lean_dec(x_1);
x_74 = lean_ctor_get(x_63, 1);
lean_inc(x_74);
lean_dec(x_63);
x_75 = lean_ctor_get(x_64, 0);
lean_inc(x_75);
lean_dec(x_64);
x_1 = x_75;
x_8 = x_31;
x_10 = x_74;
goto _start;
}
}
else
{
uint8_t x_77; 
lean_dec(x_31);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_77 = !lean_is_exclusive(x_63);
if (x_77 == 0)
{
return x_63;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_63, 0);
x_79 = lean_ctor_get(x_63, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_63);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
else
{
lean_object* x_81; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_81 = l_Lean_Elab_Term_toParserDescr_processNonReserved___redArg(x_1, x_31, x_9, x_10);
lean_dec(x_9);
lean_dec(x_1);
return x_81;
}
}
else
{
lean_object* x_82; 
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_11);
x_82 = l_Lean_Elab_Term_toParserDescr_processAtom(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_31, x_9, x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_82;
}
}
else
{
lean_object* x_83; 
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_11);
x_83 = l_Lean_Elab_Term_toParserDescr_processSepBy1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_31, x_9, x_10);
lean_dec(x_2);
lean_dec(x_1);
return x_83;
}
}
else
{
lean_object* x_84; 
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_11);
x_84 = l_Lean_Elab_Term_toParserDescr_processSepBy(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_31, x_9, x_10);
lean_dec(x_2);
lean_dec(x_1);
return x_84;
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_11);
x_85 = lean_unsigned_to_nat(0u);
x_86 = l_Lean_Syntax_getArg(x_1, x_85);
x_87 = lean_unsigned_to_nat(2u);
x_88 = l_Lean_Syntax_getArg(x_1, x_87);
x_89 = lean_unsigned_to_nat(4u);
x_90 = l_Lean_Syntax_getArg(x_1, x_89);
lean_dec(x_1);
x_91 = lean_mk_empty_array_with_capacity(x_87);
x_92 = lean_array_push(x_91, x_88);
x_93 = lean_array_push(x_92, x_90);
x_94 = l_Lean_Elab_Term_toParserDescr_processAlias(x_86, x_93, x_2, x_3, x_4, x_5, x_6, x_7, x_31, x_9, x_10);
return x_94;
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_11);
x_95 = lean_unsigned_to_nat(0u);
x_96 = l_Lean_Syntax_getArg(x_1, x_95);
x_97 = lean_unsigned_to_nat(2u);
x_98 = l_Lean_Syntax_getArg(x_1, x_97);
lean_dec(x_1);
x_99 = lean_unsigned_to_nat(1u);
x_100 = lean_mk_empty_array_with_capacity(x_99);
x_101 = lean_array_push(x_100, x_98);
x_102 = l_Lean_Elab_Term_toParserDescr_processAlias(x_96, x_101, x_2, x_3, x_4, x_5, x_6, x_7, x_31, x_9, x_10);
return x_102;
}
}
else
{
lean_object* x_103; 
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_11);
x_103 = l_Lean_Elab_Term_toParserDescr_processNullaryOrCat(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_31, x_9, x_10);
lean_dec(x_1);
return x_103;
}
}
else
{
lean_object* x_104; lean_object* x_105; 
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_11);
x_104 = lean_unsigned_to_nat(1u);
x_105 = l_Lean_Syntax_getArg(x_1, x_104);
lean_dec(x_1);
x_1 = x_105;
x_8 = x_31;
goto _start;
}
}
else
{
lean_object* x_107; lean_object* x_108; 
lean_dec(x_11);
x_107 = lean_unsigned_to_nat(0u);
x_108 = l_Lean_Syntax_getArg(x_1, x_107);
lean_dec(x_1);
x_1 = x_108;
x_8 = x_31;
goto _start;
}
}
else
{
lean_object* x_110; 
lean_dec(x_11);
x_110 = l_Lean_Elab_Term_toParserDescr_processSeq(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_31, x_9, x_10);
lean_dec(x_2);
lean_dec(x_1);
return x_110;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr_processSepBy1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_box(0);
x_15 = lean_ctor_get_uint8(x_2, sizeof(void*)*1 + 2);
lean_inc(x_13);
x_16 = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(x_16, 0, x_13);
x_17 = lean_unbox(x_14);
lean_ctor_set_uint8(x_16, sizeof(void*)*1, x_17);
x_18 = lean_unbox(x_14);
lean_ctor_set_uint8(x_16, sizeof(void*)*1 + 1, x_18);
lean_ctor_set_uint8(x_16, sizeof(void*)*1 + 2, x_15);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_19 = l_Lean_Elab_Term_toParserDescr_process(x_12, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_170; lean_object* x_171; uint8_t x_172; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_22 = x_19;
} else {
 lean_dec_ref(x_19);
 x_22 = lean_box(0);
}
x_23 = lean_unsigned_to_nat(3u);
x_24 = l_Lean_Syntax_getArg(x_1, x_23);
x_170 = lean_unsigned_to_nat(4u);
x_171 = l_Lean_Syntax_getArg(x_1, x_170);
x_172 = l_Lean_Syntax_isNone(x_171);
if (x_172 == 0)
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_173 = l_Lean_Syntax_getArg(x_171, x_11);
lean_dec(x_171);
lean_inc(x_13);
x_174 = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(x_174, 0, x_13);
lean_ctor_set_uint8(x_174, sizeof(void*)*1, x_172);
lean_ctor_set_uint8(x_174, sizeof(void*)*1 + 1, x_172);
lean_ctor_set_uint8(x_174, sizeof(void*)*1 + 2, x_15);
lean_inc(x_9);
lean_inc(x_8);
x_175 = l_Lean_Elab_Term_toParserDescr_process(x_173, x_174, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_21);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_175, 1);
lean_inc(x_177);
lean_dec(x_175);
x_178 = l_Lean_Elab_Term_ensureUnaryOutput(x_176);
x_159 = x_178;
x_160 = x_8;
x_161 = x_9;
x_162 = x_177;
goto block_169;
}
else
{
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_9);
lean_dec(x_8);
return x_175;
}
}
else
{
lean_object* x_179; uint8_t x_180; 
lean_dec(x_171);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_179 = lean_st_ref_get(x_9, x_21);
x_180 = !lean_is_exclusive(x_179);
if (x_180 == 0)
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; uint8_t x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_181 = lean_ctor_get(x_179, 0);
x_182 = lean_ctor_get(x_179, 1);
x_183 = lean_ctor_get(x_8, 5);
lean_inc(x_183);
x_184 = lean_unbox(x_14);
x_185 = l_Lean_SourceInfo_fromRef(x_183, x_184);
lean_dec(x_183);
x_186 = lean_ctor_get(x_8, 10);
lean_inc(x_186);
x_187 = lean_ctor_get(x_181, 0);
lean_inc(x_187);
lean_dec(x_181);
x_188 = l_Lean_Environment_mainModule(x_187);
lean_dec(x_187);
x_189 = lean_mk_string_unchecked("Lean", 4, 4);
x_190 = lean_mk_string_unchecked("Parser", 6, 6);
x_191 = lean_mk_string_unchecked("Term", 4, 4);
x_192 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_189);
x_193 = l_Lean_Name_mkStr4(x_189, x_190, x_191, x_192);
x_194 = lean_mk_string_unchecked("ParserDescr.symbol", 18, 18);
x_195 = l_String_toSubstring_x27(x_194);
x_196 = lean_mk_string_unchecked("ParserDescr", 11, 11);
x_197 = lean_mk_string_unchecked("symbol", 6, 6);
lean_inc(x_197);
lean_inc(x_196);
x_198 = l_Lean_Name_mkStr2(x_196, x_197);
x_199 = l_Lean_addMacroScope(x_188, x_198, x_186);
x_200 = l_Lean_Name_mkStr3(x_189, x_196, x_197);
x_201 = lean_box(0);
lean_inc(x_200);
lean_ctor_set_tag(x_179, 1);
lean_ctor_set(x_179, 1, x_201);
lean_ctor_set(x_179, 0, x_200);
x_202 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_202, 0, x_200);
x_203 = lean_box(0);
x_204 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_204, 0, x_202);
lean_ctor_set(x_204, 1, x_203);
x_205 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_205, 0, x_179);
lean_ctor_set(x_205, 1, x_204);
lean_inc(x_185);
x_206 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_206, 0, x_185);
lean_ctor_set(x_206, 1, x_195);
lean_ctor_set(x_206, 2, x_199);
lean_ctor_set(x_206, 3, x_205);
x_207 = lean_mk_string_unchecked("null", 4, 4);
x_208 = l_Lean_Name_mkStr1(x_207);
lean_inc(x_24);
lean_inc(x_185);
x_209 = l_Lean_Syntax_node1(x_185, x_208, x_24);
x_210 = l_Lean_Syntax_node2(x_185, x_193, x_206, x_209);
x_159 = x_210;
x_160 = x_8;
x_161 = x_9;
x_162 = x_182;
goto block_169;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; uint8_t x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_211 = lean_ctor_get(x_179, 0);
x_212 = lean_ctor_get(x_179, 1);
lean_inc(x_212);
lean_inc(x_211);
lean_dec(x_179);
x_213 = lean_ctor_get(x_8, 5);
lean_inc(x_213);
x_214 = lean_unbox(x_14);
x_215 = l_Lean_SourceInfo_fromRef(x_213, x_214);
lean_dec(x_213);
x_216 = lean_ctor_get(x_8, 10);
lean_inc(x_216);
x_217 = lean_ctor_get(x_211, 0);
lean_inc(x_217);
lean_dec(x_211);
x_218 = l_Lean_Environment_mainModule(x_217);
lean_dec(x_217);
x_219 = lean_mk_string_unchecked("Lean", 4, 4);
x_220 = lean_mk_string_unchecked("Parser", 6, 6);
x_221 = lean_mk_string_unchecked("Term", 4, 4);
x_222 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_219);
x_223 = l_Lean_Name_mkStr4(x_219, x_220, x_221, x_222);
x_224 = lean_mk_string_unchecked("ParserDescr.symbol", 18, 18);
x_225 = l_String_toSubstring_x27(x_224);
x_226 = lean_mk_string_unchecked("ParserDescr", 11, 11);
x_227 = lean_mk_string_unchecked("symbol", 6, 6);
lean_inc(x_227);
lean_inc(x_226);
x_228 = l_Lean_Name_mkStr2(x_226, x_227);
x_229 = l_Lean_addMacroScope(x_218, x_228, x_216);
x_230 = l_Lean_Name_mkStr3(x_219, x_226, x_227);
x_231 = lean_box(0);
lean_inc(x_230);
x_232 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_232, 0, x_230);
lean_ctor_set(x_232, 1, x_231);
x_233 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_233, 0, x_230);
x_234 = lean_box(0);
x_235 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_235, 0, x_233);
lean_ctor_set(x_235, 1, x_234);
x_236 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_236, 0, x_232);
lean_ctor_set(x_236, 1, x_235);
lean_inc(x_215);
x_237 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_237, 0, x_215);
lean_ctor_set(x_237, 1, x_225);
lean_ctor_set(x_237, 2, x_229);
lean_ctor_set(x_237, 3, x_236);
x_238 = lean_mk_string_unchecked("null", 4, 4);
x_239 = l_Lean_Name_mkStr1(x_238);
lean_inc(x_24);
lean_inc(x_215);
x_240 = l_Lean_Syntax_node1(x_215, x_239, x_24);
x_241 = l_Lean_Syntax_node2(x_215, x_223, x_237, x_240);
x_159 = x_241;
x_160 = x_8;
x_161 = x_9;
x_162 = x_212;
goto block_169;
}
}
block_37:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_inc(x_30);
x_33 = l_Lean_Syntax_node4(x_30, x_26, x_29, x_24, x_25, x_32);
x_34 = l_Lean_Syntax_node2(x_30, x_31, x_28, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_11);
if (lean_is_scalar(x_22)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_22;
}
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_27);
return x_36;
}
block_158:
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_st_ref_get(x_41, x_40);
lean_dec(x_41);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_45 = lean_ctor_get(x_43, 0);
x_46 = lean_ctor_get(x_43, 1);
x_47 = lean_ctor_get(x_39, 5);
lean_inc(x_47);
x_48 = lean_unbox(x_14);
x_49 = l_Lean_SourceInfo_fromRef(x_47, x_48);
lean_dec(x_47);
x_50 = lean_ctor_get(x_39, 10);
lean_inc(x_50);
lean_dec(x_39);
x_51 = lean_ctor_get(x_45, 0);
lean_inc(x_51);
lean_dec(x_45);
x_52 = l_Lean_Environment_mainModule(x_51);
lean_dec(x_51);
x_53 = lean_mk_string_unchecked("Lean", 4, 4);
x_54 = lean_mk_string_unchecked("Parser", 6, 6);
x_55 = lean_mk_string_unchecked("Term", 4, 4);
x_56 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
x_57 = l_Lean_Name_mkStr4(x_53, x_54, x_55, x_56);
x_58 = lean_mk_string_unchecked("paren", 5, 5);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
x_59 = l_Lean_Name_mkStr4(x_53, x_54, x_55, x_58);
x_60 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_49);
lean_ctor_set_tag(x_43, 2);
lean_ctor_set(x_43, 1, x_60);
lean_ctor_set(x_43, 0, x_49);
x_61 = lean_mk_string_unchecked("withAnnotateTerm", 16, 16);
lean_inc(x_53);
x_62 = l_Lean_Name_mkStr2(x_53, x_61);
x_63 = lean_mk_string_unchecked("with_annotate_term", 18, 18);
lean_inc(x_49);
x_64 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_64, 0, x_49);
lean_ctor_set(x_64, 1, x_63);
x_65 = lean_unsigned_to_nat(0u);
x_66 = l_Lean_Syntax_getArg(x_1, x_65);
x_67 = lean_mk_string_unchecked("explicit", 8, 8);
lean_inc(x_53);
x_68 = l_Lean_Name_mkStr4(x_53, x_54, x_55, x_67);
x_69 = lean_mk_string_unchecked("@", 1, 1);
lean_inc(x_49);
x_70 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_70, 0, x_49);
lean_ctor_set(x_70, 1, x_69);
x_71 = lean_mk_string_unchecked("ParserDescr.sepBy1", 18, 18);
x_72 = l_String_toSubstring_x27(x_71);
x_73 = lean_mk_string_unchecked("ParserDescr", 11, 11);
x_74 = lean_mk_string_unchecked("sepBy1", 6, 6);
lean_inc(x_74);
lean_inc(x_73);
x_75 = l_Lean_Name_mkStr2(x_73, x_74);
x_76 = l_Lean_addMacroScope(x_52, x_75, x_50);
x_77 = l_Lean_Name_mkStr3(x_53, x_73, x_74);
x_78 = lean_box(0);
lean_inc(x_77);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
x_80 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_80, 0, x_77);
x_81 = lean_box(0);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_79);
lean_ctor_set(x_83, 1, x_82);
lean_inc(x_49);
x_84 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_84, 0, x_49);
lean_ctor_set(x_84, 1, x_72);
lean_ctor_set(x_84, 2, x_76);
lean_ctor_set(x_84, 3, x_83);
lean_inc(x_49);
x_85 = l_Lean_Syntax_node2(x_49, x_68, x_70, x_84);
lean_inc(x_49);
x_86 = l_Lean_Syntax_node3(x_49, x_62, x_64, x_66, x_85);
x_87 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_49);
x_88 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_88, 0, x_49);
lean_ctor_set(x_88, 1, x_87);
lean_inc(x_49);
x_89 = l_Lean_Syntax_node3(x_49, x_59, x_43, x_86, x_88);
x_90 = lean_mk_string_unchecked("null", 4, 4);
x_91 = l_Lean_Name_mkStr1(x_90);
x_92 = l_Lean_Elab_Term_ensureUnaryOutput(x_20);
if (x_42 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_93 = lean_mk_string_unchecked("Bool", 4, 4);
x_94 = lean_mk_string_unchecked("false", 5, 5);
x_95 = l_Lean_Name_mkStr2(x_93, x_94);
x_96 = l_Lean_mkCIdent(x_95);
x_25 = x_38;
x_26 = x_91;
x_27 = x_46;
x_28 = x_89;
x_29 = x_92;
x_30 = x_49;
x_31 = x_57;
x_32 = x_96;
goto block_37;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_97 = lean_mk_string_unchecked("Bool", 4, 4);
x_98 = lean_mk_string_unchecked("true", 4, 4);
x_99 = l_Lean_Name_mkStr2(x_97, x_98);
x_100 = l_Lean_mkCIdent(x_99);
x_25 = x_38;
x_26 = x_91;
x_27 = x_46;
x_28 = x_89;
x_29 = x_92;
x_30 = x_49;
x_31 = x_57;
x_32 = x_100;
goto block_37;
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_101 = lean_ctor_get(x_43, 0);
x_102 = lean_ctor_get(x_43, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_43);
x_103 = lean_ctor_get(x_39, 5);
lean_inc(x_103);
x_104 = lean_unbox(x_14);
x_105 = l_Lean_SourceInfo_fromRef(x_103, x_104);
lean_dec(x_103);
x_106 = lean_ctor_get(x_39, 10);
lean_inc(x_106);
lean_dec(x_39);
x_107 = lean_ctor_get(x_101, 0);
lean_inc(x_107);
lean_dec(x_101);
x_108 = l_Lean_Environment_mainModule(x_107);
lean_dec(x_107);
x_109 = lean_mk_string_unchecked("Lean", 4, 4);
x_110 = lean_mk_string_unchecked("Parser", 6, 6);
x_111 = lean_mk_string_unchecked("Term", 4, 4);
x_112 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
x_113 = l_Lean_Name_mkStr4(x_109, x_110, x_111, x_112);
x_114 = lean_mk_string_unchecked("paren", 5, 5);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
x_115 = l_Lean_Name_mkStr4(x_109, x_110, x_111, x_114);
x_116 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_105);
x_117 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_117, 0, x_105);
lean_ctor_set(x_117, 1, x_116);
x_118 = lean_mk_string_unchecked("withAnnotateTerm", 16, 16);
lean_inc(x_109);
x_119 = l_Lean_Name_mkStr2(x_109, x_118);
x_120 = lean_mk_string_unchecked("with_annotate_term", 18, 18);
lean_inc(x_105);
x_121 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_121, 0, x_105);
lean_ctor_set(x_121, 1, x_120);
x_122 = lean_unsigned_to_nat(0u);
x_123 = l_Lean_Syntax_getArg(x_1, x_122);
x_124 = lean_mk_string_unchecked("explicit", 8, 8);
lean_inc(x_109);
x_125 = l_Lean_Name_mkStr4(x_109, x_110, x_111, x_124);
x_126 = lean_mk_string_unchecked("@", 1, 1);
lean_inc(x_105);
x_127 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_127, 0, x_105);
lean_ctor_set(x_127, 1, x_126);
x_128 = lean_mk_string_unchecked("ParserDescr.sepBy1", 18, 18);
x_129 = l_String_toSubstring_x27(x_128);
x_130 = lean_mk_string_unchecked("ParserDescr", 11, 11);
x_131 = lean_mk_string_unchecked("sepBy1", 6, 6);
lean_inc(x_131);
lean_inc(x_130);
x_132 = l_Lean_Name_mkStr2(x_130, x_131);
x_133 = l_Lean_addMacroScope(x_108, x_132, x_106);
x_134 = l_Lean_Name_mkStr3(x_109, x_130, x_131);
x_135 = lean_box(0);
lean_inc(x_134);
x_136 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
x_137 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_137, 0, x_134);
x_138 = lean_box(0);
x_139 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set(x_139, 1, x_138);
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_136);
lean_ctor_set(x_140, 1, x_139);
lean_inc(x_105);
x_141 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_141, 0, x_105);
lean_ctor_set(x_141, 1, x_129);
lean_ctor_set(x_141, 2, x_133);
lean_ctor_set(x_141, 3, x_140);
lean_inc(x_105);
x_142 = l_Lean_Syntax_node2(x_105, x_125, x_127, x_141);
lean_inc(x_105);
x_143 = l_Lean_Syntax_node3(x_105, x_119, x_121, x_123, x_142);
x_144 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_105);
x_145 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_145, 0, x_105);
lean_ctor_set(x_145, 1, x_144);
lean_inc(x_105);
x_146 = l_Lean_Syntax_node3(x_105, x_115, x_117, x_143, x_145);
x_147 = lean_mk_string_unchecked("null", 4, 4);
x_148 = l_Lean_Name_mkStr1(x_147);
x_149 = l_Lean_Elab_Term_ensureUnaryOutput(x_20);
if (x_42 == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_150 = lean_mk_string_unchecked("Bool", 4, 4);
x_151 = lean_mk_string_unchecked("false", 5, 5);
x_152 = l_Lean_Name_mkStr2(x_150, x_151);
x_153 = l_Lean_mkCIdent(x_152);
x_25 = x_38;
x_26 = x_148;
x_27 = x_102;
x_28 = x_146;
x_29 = x_149;
x_30 = x_105;
x_31 = x_113;
x_32 = x_153;
goto block_37;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_154 = lean_mk_string_unchecked("Bool", 4, 4);
x_155 = lean_mk_string_unchecked("true", 4, 4);
x_156 = l_Lean_Name_mkStr2(x_154, x_155);
x_157 = l_Lean_mkCIdent(x_156);
x_25 = x_38;
x_26 = x_148;
x_27 = x_102;
x_28 = x_146;
x_29 = x_149;
x_30 = x_105;
x_31 = x_113;
x_32 = x_157;
goto block_37;
}
}
}
block_169:
{
lean_object* x_163; lean_object* x_164; uint8_t x_165; 
x_163 = lean_unsigned_to_nat(5u);
x_164 = l_Lean_Syntax_getArg(x_1, x_163);
x_165 = l_Lean_Syntax_isNone(x_164);
lean_dec(x_164);
if (x_165 == 0)
{
lean_object* x_166; uint8_t x_167; 
x_166 = lean_box(1);
x_167 = lean_unbox(x_166);
x_38 = x_159;
x_39 = x_160;
x_40 = x_162;
x_41 = x_161;
x_42 = x_167;
goto block_158;
}
else
{
uint8_t x_168; 
x_168 = lean_unbox(x_14);
x_38 = x_159;
x_39 = x_160;
x_40 = x_162;
x_41 = x_161;
x_42 = x_168;
goto block_158;
}
}
}
else
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr_processSepBy(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_box(0);
x_15 = lean_ctor_get_uint8(x_2, sizeof(void*)*1 + 2);
lean_inc(x_13);
x_16 = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(x_16, 0, x_13);
x_17 = lean_unbox(x_14);
lean_ctor_set_uint8(x_16, sizeof(void*)*1, x_17);
x_18 = lean_unbox(x_14);
lean_ctor_set_uint8(x_16, sizeof(void*)*1 + 1, x_18);
lean_ctor_set_uint8(x_16, sizeof(void*)*1 + 2, x_15);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_19 = l_Lean_Elab_Term_toParserDescr_process(x_12, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_170; lean_object* x_171; uint8_t x_172; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_22 = x_19;
} else {
 lean_dec_ref(x_19);
 x_22 = lean_box(0);
}
x_23 = lean_unsigned_to_nat(3u);
x_24 = l_Lean_Syntax_getArg(x_1, x_23);
x_170 = lean_unsigned_to_nat(4u);
x_171 = l_Lean_Syntax_getArg(x_1, x_170);
x_172 = l_Lean_Syntax_isNone(x_171);
if (x_172 == 0)
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_173 = l_Lean_Syntax_getArg(x_171, x_11);
lean_dec(x_171);
lean_inc(x_13);
x_174 = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(x_174, 0, x_13);
lean_ctor_set_uint8(x_174, sizeof(void*)*1, x_172);
lean_ctor_set_uint8(x_174, sizeof(void*)*1 + 1, x_172);
lean_ctor_set_uint8(x_174, sizeof(void*)*1 + 2, x_15);
lean_inc(x_9);
lean_inc(x_8);
x_175 = l_Lean_Elab_Term_toParserDescr_process(x_173, x_174, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_21);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_175, 1);
lean_inc(x_177);
lean_dec(x_175);
x_178 = l_Lean_Elab_Term_ensureUnaryOutput(x_176);
x_159 = x_178;
x_160 = x_8;
x_161 = x_9;
x_162 = x_177;
goto block_169;
}
else
{
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_9);
lean_dec(x_8);
return x_175;
}
}
else
{
lean_object* x_179; uint8_t x_180; 
lean_dec(x_171);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_179 = lean_st_ref_get(x_9, x_21);
x_180 = !lean_is_exclusive(x_179);
if (x_180 == 0)
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; uint8_t x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_181 = lean_ctor_get(x_179, 0);
x_182 = lean_ctor_get(x_179, 1);
x_183 = lean_ctor_get(x_8, 5);
lean_inc(x_183);
x_184 = lean_unbox(x_14);
x_185 = l_Lean_SourceInfo_fromRef(x_183, x_184);
lean_dec(x_183);
x_186 = lean_ctor_get(x_8, 10);
lean_inc(x_186);
x_187 = lean_ctor_get(x_181, 0);
lean_inc(x_187);
lean_dec(x_181);
x_188 = l_Lean_Environment_mainModule(x_187);
lean_dec(x_187);
x_189 = lean_mk_string_unchecked("Lean", 4, 4);
x_190 = lean_mk_string_unchecked("Parser", 6, 6);
x_191 = lean_mk_string_unchecked("Term", 4, 4);
x_192 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_189);
x_193 = l_Lean_Name_mkStr4(x_189, x_190, x_191, x_192);
x_194 = lean_mk_string_unchecked("ParserDescr.symbol", 18, 18);
x_195 = l_String_toSubstring_x27(x_194);
x_196 = lean_mk_string_unchecked("ParserDescr", 11, 11);
x_197 = lean_mk_string_unchecked("symbol", 6, 6);
lean_inc(x_197);
lean_inc(x_196);
x_198 = l_Lean_Name_mkStr2(x_196, x_197);
x_199 = l_Lean_addMacroScope(x_188, x_198, x_186);
x_200 = l_Lean_Name_mkStr3(x_189, x_196, x_197);
x_201 = lean_box(0);
lean_inc(x_200);
lean_ctor_set_tag(x_179, 1);
lean_ctor_set(x_179, 1, x_201);
lean_ctor_set(x_179, 0, x_200);
x_202 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_202, 0, x_200);
x_203 = lean_box(0);
x_204 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_204, 0, x_202);
lean_ctor_set(x_204, 1, x_203);
x_205 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_205, 0, x_179);
lean_ctor_set(x_205, 1, x_204);
lean_inc(x_185);
x_206 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_206, 0, x_185);
lean_ctor_set(x_206, 1, x_195);
lean_ctor_set(x_206, 2, x_199);
lean_ctor_set(x_206, 3, x_205);
x_207 = lean_mk_string_unchecked("null", 4, 4);
x_208 = l_Lean_Name_mkStr1(x_207);
lean_inc(x_24);
lean_inc(x_185);
x_209 = l_Lean_Syntax_node1(x_185, x_208, x_24);
x_210 = l_Lean_Syntax_node2(x_185, x_193, x_206, x_209);
x_159 = x_210;
x_160 = x_8;
x_161 = x_9;
x_162 = x_182;
goto block_169;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; uint8_t x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_211 = lean_ctor_get(x_179, 0);
x_212 = lean_ctor_get(x_179, 1);
lean_inc(x_212);
lean_inc(x_211);
lean_dec(x_179);
x_213 = lean_ctor_get(x_8, 5);
lean_inc(x_213);
x_214 = lean_unbox(x_14);
x_215 = l_Lean_SourceInfo_fromRef(x_213, x_214);
lean_dec(x_213);
x_216 = lean_ctor_get(x_8, 10);
lean_inc(x_216);
x_217 = lean_ctor_get(x_211, 0);
lean_inc(x_217);
lean_dec(x_211);
x_218 = l_Lean_Environment_mainModule(x_217);
lean_dec(x_217);
x_219 = lean_mk_string_unchecked("Lean", 4, 4);
x_220 = lean_mk_string_unchecked("Parser", 6, 6);
x_221 = lean_mk_string_unchecked("Term", 4, 4);
x_222 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_219);
x_223 = l_Lean_Name_mkStr4(x_219, x_220, x_221, x_222);
x_224 = lean_mk_string_unchecked("ParserDescr.symbol", 18, 18);
x_225 = l_String_toSubstring_x27(x_224);
x_226 = lean_mk_string_unchecked("ParserDescr", 11, 11);
x_227 = lean_mk_string_unchecked("symbol", 6, 6);
lean_inc(x_227);
lean_inc(x_226);
x_228 = l_Lean_Name_mkStr2(x_226, x_227);
x_229 = l_Lean_addMacroScope(x_218, x_228, x_216);
x_230 = l_Lean_Name_mkStr3(x_219, x_226, x_227);
x_231 = lean_box(0);
lean_inc(x_230);
x_232 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_232, 0, x_230);
lean_ctor_set(x_232, 1, x_231);
x_233 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_233, 0, x_230);
x_234 = lean_box(0);
x_235 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_235, 0, x_233);
lean_ctor_set(x_235, 1, x_234);
x_236 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_236, 0, x_232);
lean_ctor_set(x_236, 1, x_235);
lean_inc(x_215);
x_237 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_237, 0, x_215);
lean_ctor_set(x_237, 1, x_225);
lean_ctor_set(x_237, 2, x_229);
lean_ctor_set(x_237, 3, x_236);
x_238 = lean_mk_string_unchecked("null", 4, 4);
x_239 = l_Lean_Name_mkStr1(x_238);
lean_inc(x_24);
lean_inc(x_215);
x_240 = l_Lean_Syntax_node1(x_215, x_239, x_24);
x_241 = l_Lean_Syntax_node2(x_215, x_223, x_237, x_240);
x_159 = x_241;
x_160 = x_8;
x_161 = x_9;
x_162 = x_212;
goto block_169;
}
}
block_37:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_inc(x_27);
x_33 = l_Lean_Syntax_node4(x_27, x_30, x_31, x_24, x_25, x_32);
x_34 = l_Lean_Syntax_node2(x_27, x_26, x_29, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_11);
if (lean_is_scalar(x_22)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_22;
}
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_28);
return x_36;
}
block_158:
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_st_ref_get(x_41, x_39);
lean_dec(x_41);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_45 = lean_ctor_get(x_43, 0);
x_46 = lean_ctor_get(x_43, 1);
x_47 = lean_ctor_get(x_40, 5);
lean_inc(x_47);
x_48 = lean_unbox(x_14);
x_49 = l_Lean_SourceInfo_fromRef(x_47, x_48);
lean_dec(x_47);
x_50 = lean_ctor_get(x_40, 10);
lean_inc(x_50);
lean_dec(x_40);
x_51 = lean_ctor_get(x_45, 0);
lean_inc(x_51);
lean_dec(x_45);
x_52 = l_Lean_Environment_mainModule(x_51);
lean_dec(x_51);
x_53 = lean_mk_string_unchecked("Lean", 4, 4);
x_54 = lean_mk_string_unchecked("Parser", 6, 6);
x_55 = lean_mk_string_unchecked("Term", 4, 4);
x_56 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
x_57 = l_Lean_Name_mkStr4(x_53, x_54, x_55, x_56);
x_58 = lean_mk_string_unchecked("paren", 5, 5);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
x_59 = l_Lean_Name_mkStr4(x_53, x_54, x_55, x_58);
x_60 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_49);
lean_ctor_set_tag(x_43, 2);
lean_ctor_set(x_43, 1, x_60);
lean_ctor_set(x_43, 0, x_49);
x_61 = lean_mk_string_unchecked("withAnnotateTerm", 16, 16);
lean_inc(x_53);
x_62 = l_Lean_Name_mkStr2(x_53, x_61);
x_63 = lean_mk_string_unchecked("with_annotate_term", 18, 18);
lean_inc(x_49);
x_64 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_64, 0, x_49);
lean_ctor_set(x_64, 1, x_63);
x_65 = lean_unsigned_to_nat(0u);
x_66 = l_Lean_Syntax_getArg(x_1, x_65);
x_67 = lean_mk_string_unchecked("explicit", 8, 8);
lean_inc(x_53);
x_68 = l_Lean_Name_mkStr4(x_53, x_54, x_55, x_67);
x_69 = lean_mk_string_unchecked("@", 1, 1);
lean_inc(x_49);
x_70 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_70, 0, x_49);
lean_ctor_set(x_70, 1, x_69);
x_71 = lean_mk_string_unchecked("ParserDescr.sepBy", 17, 17);
x_72 = l_String_toSubstring_x27(x_71);
x_73 = lean_mk_string_unchecked("ParserDescr", 11, 11);
x_74 = lean_mk_string_unchecked("sepBy", 5, 5);
lean_inc(x_74);
lean_inc(x_73);
x_75 = l_Lean_Name_mkStr2(x_73, x_74);
x_76 = l_Lean_addMacroScope(x_52, x_75, x_50);
x_77 = l_Lean_Name_mkStr3(x_53, x_73, x_74);
x_78 = lean_box(0);
lean_inc(x_77);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
x_80 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_80, 0, x_77);
x_81 = lean_box(0);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_79);
lean_ctor_set(x_83, 1, x_82);
lean_inc(x_49);
x_84 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_84, 0, x_49);
lean_ctor_set(x_84, 1, x_72);
lean_ctor_set(x_84, 2, x_76);
lean_ctor_set(x_84, 3, x_83);
lean_inc(x_49);
x_85 = l_Lean_Syntax_node2(x_49, x_68, x_70, x_84);
lean_inc(x_49);
x_86 = l_Lean_Syntax_node3(x_49, x_62, x_64, x_66, x_85);
x_87 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_49);
x_88 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_88, 0, x_49);
lean_ctor_set(x_88, 1, x_87);
lean_inc(x_49);
x_89 = l_Lean_Syntax_node3(x_49, x_59, x_43, x_86, x_88);
x_90 = lean_mk_string_unchecked("null", 4, 4);
x_91 = l_Lean_Name_mkStr1(x_90);
x_92 = l_Lean_Elab_Term_ensureUnaryOutput(x_20);
if (x_42 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_93 = lean_mk_string_unchecked("Bool", 4, 4);
x_94 = lean_mk_string_unchecked("false", 5, 5);
x_95 = l_Lean_Name_mkStr2(x_93, x_94);
x_96 = l_Lean_mkCIdent(x_95);
x_25 = x_38;
x_26 = x_57;
x_27 = x_49;
x_28 = x_46;
x_29 = x_89;
x_30 = x_91;
x_31 = x_92;
x_32 = x_96;
goto block_37;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_97 = lean_mk_string_unchecked("Bool", 4, 4);
x_98 = lean_mk_string_unchecked("true", 4, 4);
x_99 = l_Lean_Name_mkStr2(x_97, x_98);
x_100 = l_Lean_mkCIdent(x_99);
x_25 = x_38;
x_26 = x_57;
x_27 = x_49;
x_28 = x_46;
x_29 = x_89;
x_30 = x_91;
x_31 = x_92;
x_32 = x_100;
goto block_37;
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_101 = lean_ctor_get(x_43, 0);
x_102 = lean_ctor_get(x_43, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_43);
x_103 = lean_ctor_get(x_40, 5);
lean_inc(x_103);
x_104 = lean_unbox(x_14);
x_105 = l_Lean_SourceInfo_fromRef(x_103, x_104);
lean_dec(x_103);
x_106 = lean_ctor_get(x_40, 10);
lean_inc(x_106);
lean_dec(x_40);
x_107 = lean_ctor_get(x_101, 0);
lean_inc(x_107);
lean_dec(x_101);
x_108 = l_Lean_Environment_mainModule(x_107);
lean_dec(x_107);
x_109 = lean_mk_string_unchecked("Lean", 4, 4);
x_110 = lean_mk_string_unchecked("Parser", 6, 6);
x_111 = lean_mk_string_unchecked("Term", 4, 4);
x_112 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
x_113 = l_Lean_Name_mkStr4(x_109, x_110, x_111, x_112);
x_114 = lean_mk_string_unchecked("paren", 5, 5);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
x_115 = l_Lean_Name_mkStr4(x_109, x_110, x_111, x_114);
x_116 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_105);
x_117 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_117, 0, x_105);
lean_ctor_set(x_117, 1, x_116);
x_118 = lean_mk_string_unchecked("withAnnotateTerm", 16, 16);
lean_inc(x_109);
x_119 = l_Lean_Name_mkStr2(x_109, x_118);
x_120 = lean_mk_string_unchecked("with_annotate_term", 18, 18);
lean_inc(x_105);
x_121 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_121, 0, x_105);
lean_ctor_set(x_121, 1, x_120);
x_122 = lean_unsigned_to_nat(0u);
x_123 = l_Lean_Syntax_getArg(x_1, x_122);
x_124 = lean_mk_string_unchecked("explicit", 8, 8);
lean_inc(x_109);
x_125 = l_Lean_Name_mkStr4(x_109, x_110, x_111, x_124);
x_126 = lean_mk_string_unchecked("@", 1, 1);
lean_inc(x_105);
x_127 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_127, 0, x_105);
lean_ctor_set(x_127, 1, x_126);
x_128 = lean_mk_string_unchecked("ParserDescr.sepBy", 17, 17);
x_129 = l_String_toSubstring_x27(x_128);
x_130 = lean_mk_string_unchecked("ParserDescr", 11, 11);
x_131 = lean_mk_string_unchecked("sepBy", 5, 5);
lean_inc(x_131);
lean_inc(x_130);
x_132 = l_Lean_Name_mkStr2(x_130, x_131);
x_133 = l_Lean_addMacroScope(x_108, x_132, x_106);
x_134 = l_Lean_Name_mkStr3(x_109, x_130, x_131);
x_135 = lean_box(0);
lean_inc(x_134);
x_136 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
x_137 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_137, 0, x_134);
x_138 = lean_box(0);
x_139 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set(x_139, 1, x_138);
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_136);
lean_ctor_set(x_140, 1, x_139);
lean_inc(x_105);
x_141 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_141, 0, x_105);
lean_ctor_set(x_141, 1, x_129);
lean_ctor_set(x_141, 2, x_133);
lean_ctor_set(x_141, 3, x_140);
lean_inc(x_105);
x_142 = l_Lean_Syntax_node2(x_105, x_125, x_127, x_141);
lean_inc(x_105);
x_143 = l_Lean_Syntax_node3(x_105, x_119, x_121, x_123, x_142);
x_144 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_105);
x_145 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_145, 0, x_105);
lean_ctor_set(x_145, 1, x_144);
lean_inc(x_105);
x_146 = l_Lean_Syntax_node3(x_105, x_115, x_117, x_143, x_145);
x_147 = lean_mk_string_unchecked("null", 4, 4);
x_148 = l_Lean_Name_mkStr1(x_147);
x_149 = l_Lean_Elab_Term_ensureUnaryOutput(x_20);
if (x_42 == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_150 = lean_mk_string_unchecked("Bool", 4, 4);
x_151 = lean_mk_string_unchecked("false", 5, 5);
x_152 = l_Lean_Name_mkStr2(x_150, x_151);
x_153 = l_Lean_mkCIdent(x_152);
x_25 = x_38;
x_26 = x_113;
x_27 = x_105;
x_28 = x_102;
x_29 = x_146;
x_30 = x_148;
x_31 = x_149;
x_32 = x_153;
goto block_37;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_154 = lean_mk_string_unchecked("Bool", 4, 4);
x_155 = lean_mk_string_unchecked("true", 4, 4);
x_156 = l_Lean_Name_mkStr2(x_154, x_155);
x_157 = l_Lean_mkCIdent(x_156);
x_25 = x_38;
x_26 = x_113;
x_27 = x_105;
x_28 = x_102;
x_29 = x_146;
x_30 = x_148;
x_31 = x_149;
x_32 = x_157;
goto block_37;
}
}
}
block_169:
{
lean_object* x_163; lean_object* x_164; uint8_t x_165; 
x_163 = lean_unsigned_to_nat(5u);
x_164 = l_Lean_Syntax_getArg(x_1, x_163);
x_165 = l_Lean_Syntax_isNone(x_164);
lean_dec(x_164);
if (x_165 == 0)
{
lean_object* x_166; uint8_t x_167; 
x_166 = lean_box(1);
x_167 = lean_unbox(x_166);
x_38 = x_159;
x_39 = x_162;
x_40 = x_160;
x_41 = x_161;
x_42 = x_167;
goto block_158;
}
else
{
uint8_t x_168; 
x_168 = lean_unbox(x_14);
x_38 = x_159;
x_39 = x_162;
x_40 = x_160;
x_41 = x_161;
x_42 = x_168;
goto block_158;
}
}
}
else
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Elab_Term_toParserDescr_processAlias_spec__0___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
LEAN_EXPORT lean_object* l_panic___at___Lean_Elab_Term_toParserDescr_processAlias_spec__0___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Elab_Term_toParserDescr_processAlias_spec__0___lam__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Elab_Term_toParserDescr_processAlias_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_11 = lean_alloc_closure((void*)(l_panic___at___Lean_Elab_Term_toParserDescr_processAlias_spec__0___lam__0), 11, 0);
x_12 = lean_alloc_closure((void*)(l_panic___at___Lean_Elab_Term_toParserDescr_processAlias_spec__0___lam__1___boxed), 9, 0);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__0___boxed), 7, 0);
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__1), 9, 0);
x_15 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__0___boxed), 5, 0);
x_16 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__1), 7, 0);
x_17 = l_instMonadEIO(lean_box(0));
x_18 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
lean_inc(x_20);
x_21 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_21, 0, x_20);
x_22 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_22, 0, x_20);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_closure((void*)(l_instMonadEIO___lam__1), 5, 0);
x_25 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_25, 0, x_24);
x_26 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_26, 0, x_25);
x_27 = lean_alloc_closure((void*)(l_instMonadEIO___lam__2), 5, 0);
x_28 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_28, 0, x_27);
x_29 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_29, 0, x_28);
x_30 = lean_alloc_closure((void*)(l_EStateM_seqRight), 7, 2);
lean_closure_set(x_30, 0, lean_box(0));
lean_closure_set(x_30, 1, lean_box(0));
x_31 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_31, 0, x_30);
x_32 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_32, 0, x_31);
lean_inc(x_32);
lean_inc(x_29);
lean_inc(x_26);
x_33 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_33, 0, x_23);
lean_ctor_set(x_33, 1, x_15);
lean_ctor_set(x_33, 2, x_26);
lean_ctor_set(x_33, 3, x_29);
lean_ctor_set(x_33, 4, x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_16);
x_35 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_34);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec(x_35);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_dec(x_36);
lean_inc(x_37);
x_38 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_38, 0, x_37);
x_39 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_39, 0, x_37);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_41, 0, x_26);
x_42 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_42, 0, x_41);
x_43 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_43, 0, x_29);
x_44 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_44, 0, x_43);
x_45 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_45, 0, x_32);
x_46 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_46, 0, x_45);
lean_inc(x_46);
lean_inc(x_44);
lean_inc(x_42);
x_47 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_47, 0, x_40);
lean_ctor_set(x_47, 1, x_13);
lean_ctor_set(x_47, 2, x_42);
lean_ctor_set(x_47, 3, x_44);
lean_ctor_set(x_47, 4, x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_14);
x_49 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_48);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
lean_dec(x_49);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
lean_dec(x_50);
lean_inc(x_51);
x_52 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_52, 0, x_51);
x_53 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_53, 0, x_51);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_55, 0, x_42);
x_56 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_56, 0, x_55);
x_57 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_57, 0, x_44);
x_58 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_58, 0, x_57);
x_59 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_59, 0, x_46);
x_60 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_60, 0, x_59);
x_61 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_61, 0, x_54);
lean_ctor_set(x_61, 1, x_12);
lean_ctor_set(x_61, 2, x_56);
lean_ctor_set(x_61, 3, x_58);
lean_ctor_set(x_61, 4, x_60);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_11);
x_63 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_62);
x_64 = lean_mk_string_unchecked("term", 4, 4);
x_65 = l_Lean_Name_mkStr1(x_64);
x_66 = lean_box(0);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
x_68 = l_Lean_instInhabitedTSyntax(x_67);
lean_dec(x_67);
x_69 = l_instInhabitedOfMonad___redArg(x_63, x_68);
x_70 = lean_alloc_closure((void*)(l_panic___at___Lean_Elab_Term_toParserDescr_processAlias_spec__0___lam__2___boxed), 2, 1);
lean_closure_set(x_70, 0, x_69);
x_71 = lean_panic_fn(x_70, x_1);
x_72 = lean_apply_9(x_71, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_72;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Term_toParserDescr_processAlias_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_nat_add(x_4, x_6);
lean_dec(x_6);
lean_dec(x_4);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_usize_of_nat(x_8);
x_10 = lean_usize_add(x_2, x_9);
x_2 = x_10;
x_4 = x_7;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_toParserDescr_processAlias_spec__2(size_t x_1, size_t x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_toParserDescr_processAlias_spec__3(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_8 = l_Lean_Elab_Term_ensureUnaryOutput(x_5);
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_toParserDescr_processAlias_spec__4(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_2, x_1);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_3);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; lean_object* x_22; 
x_15 = lean_array_uget(x_3, x_2);
x_16 = lean_ctor_get(x_4, 0);
x_17 = lean_box(0);
x_18 = lean_ctor_get_uint8(x_4, sizeof(void*)*1 + 2);
lean_inc(x_16);
x_19 = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(x_19, 0, x_16);
x_20 = lean_unbox(x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*1, x_20);
x_21 = lean_unbox(x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*1 + 1, x_21);
lean_ctor_set_uint8(x_19, sizeof(void*)*1 + 2, x_18);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_22 = l_Lean_Elab_Term_toParserDescr_process(x_15, x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; size_t x_28; size_t x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_box(0);
x_26 = lean_array_uset(x_3, x_2, x_25);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_usize_of_nat(x_27);
x_29 = lean_usize_add(x_2, x_28);
x_30 = lean_array_uset(x_26, x_2, x_23);
x_2 = x_29;
x_3 = x_30;
x_12 = x_24;
goto _start;
}
else
{
uint8_t x_32; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_32 = !lean_is_exclusive(x_22);
if (x_32 == 0)
{
return x_22;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_22, 0);
x_34 = lean_ctor_get(x_22, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_22);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_toParserDescr_processAlias_spec__5___redArg(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_2, x_1);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; 
x_9 = lean_array_uget(x_3, x_2);
x_10 = lean_box(0);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_13 = x_9;
} else {
 lean_dec_ref(x_9);
 x_13 = lean_box(0);
}
x_14 = lean_array_uset(x_3, x_2, x_10);
x_142 = l_Lean_Syntax_getArgs(x_11);
lean_dec(x_11);
x_143 = lean_array_get_size(x_142);
x_144 = lean_unsigned_to_nat(1u);
x_145 = lean_nat_dec_eq(x_143, x_144);
lean_dec(x_143);
if (x_145 == 0)
{
lean_dec(x_142);
lean_dec(x_13);
x_15 = x_12;
x_16 = x_6;
goto block_22;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; uint8_t x_153; 
x_146 = lean_unsigned_to_nat(0u);
x_147 = lean_array_fget(x_142, x_146);
lean_dec(x_142);
x_148 = lean_mk_string_unchecked("Lean", 4, 4);
x_149 = lean_mk_string_unchecked("Parser", 6, 6);
x_150 = lean_mk_string_unchecked("Syntax", 6, 6);
x_151 = lean_mk_string_unchecked("nonReserved", 11, 11);
lean_inc(x_150);
lean_inc(x_149);
lean_inc(x_148);
x_152 = l_Lean_Name_mkStr4(x_148, x_149, x_150, x_151);
lean_inc(x_147);
x_153 = l_Lean_Syntax_isOfKind(x_147, x_152);
lean_dec(x_152);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; uint8_t x_156; 
x_154 = lean_mk_string_unchecked("atom", 4, 4);
x_155 = l_Lean_Name_mkStr4(x_148, x_149, x_150, x_154);
lean_inc(x_147);
x_156 = l_Lean_Syntax_isOfKind(x_147, x_155);
lean_dec(x_155);
if (x_156 == 0)
{
lean_dec(x_147);
lean_dec(x_13);
x_15 = x_12;
x_16 = x_6;
goto block_22;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; uint8_t x_160; 
x_157 = l_Lean_Syntax_getArg(x_147, x_146);
lean_dec(x_147);
x_158 = lean_mk_string_unchecked("str", 3, 3);
x_159 = l_Lean_Name_mkStr1(x_158);
lean_inc(x_157);
x_160 = l_Lean_Syntax_isOfKind(x_157, x_159);
lean_dec(x_159);
if (x_160 == 0)
{
lean_dec(x_157);
lean_dec(x_13);
x_15 = x_12;
x_16 = x_6;
goto block_22;
}
else
{
lean_inc(x_4);
x_36 = x_157;
x_37 = x_4;
x_38 = x_5;
x_39 = x_6;
goto block_141;
}
}
}
else
{
lean_object* x_161; 
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_148);
x_161 = l_Lean_Syntax_getArg(x_147, x_144);
lean_dec(x_147);
lean_inc(x_4);
x_36 = x_161;
x_37 = x_4;
x_38 = x_5;
x_39 = x_6;
goto block_141;
}
}
block_22:
{
lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_usize_of_nat(x_17);
x_19 = lean_usize_add(x_2, x_18);
x_20 = lean_array_uset(x_14, x_2, x_15);
x_2 = x_19;
x_3 = x_20;
x_6 = x_16;
goto _start;
}
block_35:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_12, 0);
lean_inc(x_30);
lean_dec(x_12);
lean_inc(x_27);
x_31 = l_Lean_Syntax_node3(x_27, x_26, x_28, x_29, x_30);
x_32 = l_Lean_Syntax_node2(x_27, x_23, x_25, x_31);
x_33 = lean_unsigned_to_nat(1u);
if (lean_is_scalar(x_13)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_13;
}
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_15 = x_34;
x_16 = x_24;
goto block_22;
}
block_141:
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_st_ref_get(x_38, x_39);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_42 = lean_ctor_get(x_40, 0);
x_43 = lean_ctor_get(x_40, 1);
x_44 = lean_ctor_get(x_37, 5);
lean_inc(x_44);
x_45 = lean_box(0);
x_46 = l_Lean_TSyntax_getString(x_36);
lean_dec(x_36);
x_47 = lean_unbox(x_45);
x_48 = l_Lean_SourceInfo_fromRef(x_44, x_47);
lean_dec(x_44);
x_49 = lean_ctor_get(x_37, 10);
lean_inc(x_49);
lean_dec(x_37);
x_50 = lean_ctor_get(x_42, 0);
lean_inc(x_50);
lean_dec(x_42);
x_51 = l_Lean_Environment_mainModule(x_50);
lean_dec(x_50);
x_52 = lean_mk_string_unchecked("Lean", 4, 4);
x_53 = lean_mk_string_unchecked("Parser", 6, 6);
x_54 = lean_mk_string_unchecked("Term", 4, 4);
x_55 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
x_56 = l_Lean_Name_mkStr4(x_52, x_53, x_54, x_55);
x_57 = lean_mk_string_unchecked("ParserDescr.nodeWithAntiquot", 28, 28);
x_58 = l_String_toSubstring_x27(x_57);
x_59 = lean_mk_string_unchecked("ParserDescr", 11, 11);
x_60 = lean_mk_string_unchecked("nodeWithAntiquot", 16, 16);
lean_inc(x_60);
lean_inc(x_59);
x_61 = l_Lean_Name_mkStr2(x_59, x_60);
x_62 = l_Lean_addMacroScope(x_51, x_61, x_49);
lean_inc(x_52);
x_63 = l_Lean_Name_mkStr3(x_52, x_59, x_60);
x_64 = lean_box(0);
lean_inc(x_63);
lean_ctor_set_tag(x_40, 1);
lean_ctor_set(x_40, 1, x_64);
lean_ctor_set(x_40, 0, x_63);
x_65 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_65, 0, x_63);
x_66 = lean_box(0);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_40);
lean_ctor_set(x_68, 1, x_67);
lean_inc(x_48);
x_69 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_69, 0, x_48);
lean_ctor_set(x_69, 1, x_58);
lean_ctor_set(x_69, 2, x_62);
lean_ctor_set(x_69, 3, x_68);
x_70 = lean_mk_string_unchecked("null", 4, 4);
x_71 = l_Lean_Name_mkStr1(x_70);
x_72 = lean_box(2);
x_73 = l_Lean_Syntax_mkStrLit(x_46, x_72);
x_74 = lean_mk_string_unchecked("token", 5, 5);
x_75 = l_Lean_Name_mkStr1(x_74);
x_76 = l_Lean_Name_str___override(x_75, x_46);
lean_inc(x_76);
x_77 = l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(x_64, x_76);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; 
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
x_78 = l_Lean_quoteNameMk(x_76);
x_23 = x_56;
x_24 = x_43;
x_25 = x_69;
x_26 = x_71;
x_27 = x_48;
x_28 = x_73;
x_29 = x_78;
goto block_35;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_76);
x_79 = lean_ctor_get(x_77, 0);
lean_inc(x_79);
lean_dec(x_77);
x_80 = lean_mk_string_unchecked("quotedName", 10, 10);
x_81 = l_Lean_Name_mkStr4(x_52, x_53, x_54, x_80);
x_82 = lean_mk_string_unchecked("`", 1, 1);
x_83 = lean_mk_string_unchecked(".", 1, 1);
x_84 = l_String_intercalate(x_83, x_79);
lean_dec(x_83);
x_85 = lean_string_append(x_82, x_84);
lean_dec(x_84);
x_86 = l_Lean_Syntax_mkNameLit(x_85, x_72);
x_87 = lean_unsigned_to_nat(1u);
x_88 = lean_mk_empty_array_with_capacity(x_87);
x_89 = lean_array_push(x_88, x_86);
x_90 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_90, 0, x_72);
lean_ctor_set(x_90, 1, x_81);
lean_ctor_set(x_90, 2, x_89);
x_23 = x_56;
x_24 = x_43;
x_25 = x_69;
x_26 = x_71;
x_27 = x_48;
x_28 = x_73;
x_29 = x_90;
goto block_35;
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_91 = lean_ctor_get(x_40, 0);
x_92 = lean_ctor_get(x_40, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_40);
x_93 = lean_ctor_get(x_37, 5);
lean_inc(x_93);
x_94 = lean_box(0);
x_95 = l_Lean_TSyntax_getString(x_36);
lean_dec(x_36);
x_96 = lean_unbox(x_94);
x_97 = l_Lean_SourceInfo_fromRef(x_93, x_96);
lean_dec(x_93);
x_98 = lean_ctor_get(x_37, 10);
lean_inc(x_98);
lean_dec(x_37);
x_99 = lean_ctor_get(x_91, 0);
lean_inc(x_99);
lean_dec(x_91);
x_100 = l_Lean_Environment_mainModule(x_99);
lean_dec(x_99);
x_101 = lean_mk_string_unchecked("Lean", 4, 4);
x_102 = lean_mk_string_unchecked("Parser", 6, 6);
x_103 = lean_mk_string_unchecked("Term", 4, 4);
x_104 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
x_105 = l_Lean_Name_mkStr4(x_101, x_102, x_103, x_104);
x_106 = lean_mk_string_unchecked("ParserDescr.nodeWithAntiquot", 28, 28);
x_107 = l_String_toSubstring_x27(x_106);
x_108 = lean_mk_string_unchecked("ParserDescr", 11, 11);
x_109 = lean_mk_string_unchecked("nodeWithAntiquot", 16, 16);
lean_inc(x_109);
lean_inc(x_108);
x_110 = l_Lean_Name_mkStr2(x_108, x_109);
x_111 = l_Lean_addMacroScope(x_100, x_110, x_98);
lean_inc(x_101);
x_112 = l_Lean_Name_mkStr3(x_101, x_108, x_109);
x_113 = lean_box(0);
lean_inc(x_112);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
x_115 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_115, 0, x_112);
x_116 = lean_box(0);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_114);
lean_ctor_set(x_118, 1, x_117);
lean_inc(x_97);
x_119 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_119, 0, x_97);
lean_ctor_set(x_119, 1, x_107);
lean_ctor_set(x_119, 2, x_111);
lean_ctor_set(x_119, 3, x_118);
x_120 = lean_mk_string_unchecked("null", 4, 4);
x_121 = l_Lean_Name_mkStr1(x_120);
x_122 = lean_box(2);
x_123 = l_Lean_Syntax_mkStrLit(x_95, x_122);
x_124 = lean_mk_string_unchecked("token", 5, 5);
x_125 = l_Lean_Name_mkStr1(x_124);
x_126 = l_Lean_Name_str___override(x_125, x_95);
lean_inc(x_126);
x_127 = l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(x_113, x_126);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; 
lean_dec(x_103);
lean_dec(x_102);
lean_dec(x_101);
x_128 = l_Lean_quoteNameMk(x_126);
x_23 = x_105;
x_24 = x_92;
x_25 = x_119;
x_26 = x_121;
x_27 = x_97;
x_28 = x_123;
x_29 = x_128;
goto block_35;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_dec(x_126);
x_129 = lean_ctor_get(x_127, 0);
lean_inc(x_129);
lean_dec(x_127);
x_130 = lean_mk_string_unchecked("quotedName", 10, 10);
x_131 = l_Lean_Name_mkStr4(x_101, x_102, x_103, x_130);
x_132 = lean_mk_string_unchecked("`", 1, 1);
x_133 = lean_mk_string_unchecked(".", 1, 1);
x_134 = l_String_intercalate(x_133, x_129);
lean_dec(x_133);
x_135 = lean_string_append(x_132, x_134);
lean_dec(x_134);
x_136 = l_Lean_Syntax_mkNameLit(x_135, x_122);
x_137 = lean_unsigned_to_nat(1u);
x_138 = lean_mk_empty_array_with_capacity(x_137);
x_139 = lean_array_push(x_138, x_136);
x_140 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_140, 0, x_122);
lean_ctor_set(x_140, 1, x_131);
lean_ctor_set(x_140, 2, x_139);
x_23 = x_105;
x_24 = x_92;
x_25 = x_119;
x_26 = x_121;
x_27 = x_97;
x_28 = x_123;
x_29 = x_140;
goto block_35;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_toParserDescr_processAlias_spec__5(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Array_mapMUnsafe_map___at___Lean_Elab_Term_toParserDescr_processAlias_spec__5___redArg(x_1, x_2, x_3, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr_processAlias(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_438; 
x_56 = l_Lean_Syntax_getId(x_1);
x_57 = lean_erase_macro_scopes(x_56);
x_402 = l_Lean_Parser_getParserAliasInfo(x_57, x_11);
x_403 = lean_ctor_get(x_402, 0);
lean_inc(x_403);
x_404 = lean_ctor_get(x_402, 1);
lean_inc(x_404);
lean_dec(x_402);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_403);
x_438 = l_Lean_Elab_Term_addAliasInfo(x_1, x_403, x_5, x_6, x_7, x_8, x_9, x_10, x_404);
if (lean_obj_tag(x_438) == 0)
{
lean_object* x_439; size_t x_440; lean_object* x_441; size_t x_442; lean_object* x_443; 
x_439 = lean_ctor_get(x_438, 1);
lean_inc(x_439);
lean_dec(x_438);
x_440 = lean_array_size(x_2);
x_441 = lean_unsigned_to_nat(0u);
x_442 = lean_usize_of_nat(x_441);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_443 = l_Array_mapMUnsafe_map___at___Lean_Elab_Term_toParserDescr_processAlias_spec__4(x_440, x_442, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_439);
if (lean_obj_tag(x_443) == 0)
{
lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; uint8_t x_448; 
x_444 = lean_ctor_get(x_443, 0);
lean_inc(x_444);
x_445 = lean_ctor_get(x_443, 1);
lean_inc(x_445);
lean_dec(x_443);
x_446 = lean_mk_string_unchecked("orelse", 6, 6);
x_447 = l_Lean_Name_mkStr1(x_446);
x_448 = lean_name_eq(x_57, x_447);
lean_dec(x_447);
if (x_448 == 0)
{
lean_dec(x_2);
x_405 = x_444;
x_406 = x_3;
x_407 = x_4;
x_408 = x_5;
x_409 = x_6;
x_410 = x_7;
x_411 = x_8;
x_412 = x_9;
x_413 = x_10;
x_414 = x_445;
goto block_437;
}
else
{
lean_object* x_449; size_t x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; 
x_449 = l_Array_zip___redArg(x_2, x_444);
lean_dec(x_444);
lean_dec(x_2);
x_450 = lean_array_size(x_449);
lean_inc(x_9);
x_451 = l_Array_mapMUnsafe_map___at___Lean_Elab_Term_toParserDescr_processAlias_spec__5___redArg(x_450, x_442, x_449, x_9, x_10, x_445);
x_452 = lean_ctor_get(x_451, 0);
lean_inc(x_452);
x_453 = lean_ctor_get(x_451, 1);
lean_inc(x_453);
lean_dec(x_451);
x_405 = x_452;
x_406 = x_3;
x_407 = x_4;
x_408 = x_5;
x_409 = x_6;
x_410 = x_7;
x_411 = x_8;
x_412 = x_9;
x_413 = x_10;
x_414 = x_453;
goto block_437;
}
}
else
{
uint8_t x_454; 
lean_dec(x_403);
lean_dec(x_57);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_454 = !lean_is_exclusive(x_443);
if (x_454 == 0)
{
return x_443;
}
else
{
lean_object* x_455; lean_object* x_456; lean_object* x_457; 
x_455 = lean_ctor_get(x_443, 0);
x_456 = lean_ctor_get(x_443, 1);
lean_inc(x_456);
lean_inc(x_455);
lean_dec(x_443);
x_457 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_457, 0, x_455);
lean_ctor_set(x_457, 1, x_456);
return x_457;
}
}
}
else
{
uint8_t x_458; 
lean_dec(x_403);
lean_dec(x_57);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_458 = !lean_is_exclusive(x_438);
if (x_458 == 0)
{
return x_438;
}
else
{
lean_object* x_459; lean_object* x_460; lean_object* x_461; 
x_459 = lean_ctor_get(x_438, 0);
x_460 = lean_ctor_get(x_438, 1);
lean_inc(x_460);
lean_inc(x_459);
lean_dec(x_438);
x_461 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_461, 0, x_459);
lean_ctor_set(x_461, 1, x_460);
return x_461;
}
}
block_17:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
block_32:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_array_fget(x_25, x_22);
x_29 = lean_array_fget(x_25, x_20);
lean_dec(x_25);
lean_inc(x_24);
x_30 = l_Lean_Syntax_node3(x_24, x_23, x_27, x_28, x_29);
x_31 = l_Lean_Syntax_node2(x_24, x_26, x_18, x_30);
x_12 = x_19;
x_13 = x_31;
x_14 = x_21;
goto block_17;
}
block_45:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_array_fget(x_40, x_35);
lean_dec(x_40);
lean_inc(x_38);
x_43 = l_Lean_Syntax_node2(x_38, x_37, x_41, x_42);
x_44 = l_Lean_Syntax_node2(x_38, x_36, x_39, x_43);
x_12 = x_33;
x_13 = x_44;
x_14 = x_34;
goto block_17;
}
block_55:
{
lean_object* x_53; lean_object* x_54; 
lean_inc(x_50);
x_53 = l_Lean_Syntax_node1(x_50, x_49, x_52);
x_54 = l_Lean_Syntax_node2(x_50, x_51, x_47, x_53);
x_12 = x_46;
x_13 = x_54;
x_14 = x_48;
goto block_17;
}
block_401:
{
lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_69 = lean_array_get_size(x_67);
x_70 = lean_unsigned_to_nat(0u);
x_71 = lean_nat_dec_eq(x_69, x_70);
if (x_71 == 0)
{
lean_object* x_72; uint8_t x_73; 
x_72 = lean_unsigned_to_nat(1u);
x_73 = lean_nat_dec_eq(x_69, x_72);
if (x_73 == 0)
{
lean_object* x_74; uint8_t x_75; 
x_74 = lean_unsigned_to_nat(2u);
x_75 = lean_nat_dec_eq(x_69, x_74);
lean_dec(x_69);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_67);
lean_dec(x_57);
x_76 = lean_mk_string_unchecked("Lean.Elab.Syntax", 16, 16);
x_77 = lean_mk_string_unchecked("Lean.Elab.Term.toParserDescr.processAlias", 41, 41);
x_78 = lean_unsigned_to_nat(193u);
x_79 = lean_unsigned_to_nat(21u);
x_80 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_81 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_76, x_77, x_78, x_79, x_80);
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_76);
x_82 = l_panic___at___Lean_Elab_Term_toParserDescr_processAlias_spec__0(x_81, x_58, x_63, x_64, x_65, x_59, x_62, x_60, x_66, x_61);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_12 = x_68;
x_13 = x_83;
x_14 = x_84;
goto block_17;
}
else
{
uint8_t x_85; 
lean_dec(x_68);
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
lean_object* x_89; 
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_59);
lean_dec(x_58);
lean_inc(x_57);
x_89 = l_Lean_Parser_ensureBinaryParserAlias(x_57, x_61);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_90 = lean_ctor_get(x_89, 1);
lean_inc(x_90);
lean_dec(x_89);
x_91 = lean_st_ref_get(x_66, x_90);
lean_dec(x_66);
x_92 = !lean_is_exclusive(x_91);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_93 = lean_ctor_get(x_91, 0);
x_94 = lean_ctor_get(x_91, 1);
x_95 = lean_ctor_get(x_60, 5);
lean_inc(x_95);
x_96 = l_Lean_SourceInfo_fromRef(x_95, x_73);
lean_dec(x_95);
x_97 = lean_ctor_get(x_60, 10);
lean_inc(x_97);
lean_dec(x_60);
x_98 = lean_ctor_get(x_93, 0);
lean_inc(x_98);
lean_dec(x_93);
x_99 = l_Lean_Environment_mainModule(x_98);
lean_dec(x_98);
x_100 = lean_mk_string_unchecked("Lean", 4, 4);
x_101 = lean_mk_string_unchecked("Parser", 6, 6);
x_102 = lean_mk_string_unchecked("Term", 4, 4);
x_103 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
x_104 = l_Lean_Name_mkStr4(x_100, x_101, x_102, x_103);
x_105 = lean_mk_string_unchecked("ParserDescr.binary", 18, 18);
x_106 = l_String_toSubstring_x27(x_105);
x_107 = lean_mk_string_unchecked("ParserDescr", 11, 11);
x_108 = lean_mk_string_unchecked("binary", 6, 6);
lean_inc(x_108);
lean_inc(x_107);
x_109 = l_Lean_Name_mkStr2(x_107, x_108);
x_110 = l_Lean_addMacroScope(x_99, x_109, x_97);
lean_inc(x_100);
x_111 = l_Lean_Name_mkStr3(x_100, x_107, x_108);
x_112 = lean_box(0);
lean_inc(x_111);
lean_ctor_set_tag(x_91, 1);
lean_ctor_set(x_91, 1, x_112);
lean_ctor_set(x_91, 0, x_111);
x_113 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_113, 0, x_111);
x_114 = lean_box(0);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_91);
lean_ctor_set(x_116, 1, x_115);
lean_inc(x_96);
x_117 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_117, 0, x_96);
lean_ctor_set(x_117, 1, x_106);
lean_ctor_set(x_117, 2, x_110);
lean_ctor_set(x_117, 3, x_116);
x_118 = lean_mk_string_unchecked("null", 4, 4);
x_119 = l_Lean_Name_mkStr1(x_118);
lean_inc(x_57);
x_120 = l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(x_112, x_57);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; 
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_100);
x_121 = l_Lean_quoteNameMk(x_57);
x_18 = x_117;
x_19 = x_68;
x_20 = x_72;
x_21 = x_94;
x_22 = x_70;
x_23 = x_119;
x_24 = x_96;
x_25 = x_67;
x_26 = x_104;
x_27 = x_121;
goto block_32;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
lean_dec(x_57);
x_122 = lean_ctor_get(x_120, 0);
lean_inc(x_122);
lean_dec(x_120);
x_123 = lean_mk_string_unchecked("quotedName", 10, 10);
x_124 = l_Lean_Name_mkStr4(x_100, x_101, x_102, x_123);
x_125 = lean_mk_string_unchecked("`", 1, 1);
x_126 = lean_mk_string_unchecked(".", 1, 1);
x_127 = l_String_intercalate(x_126, x_122);
lean_dec(x_126);
x_128 = lean_string_append(x_125, x_127);
lean_dec(x_127);
x_129 = lean_box(2);
x_130 = l_Lean_Syntax_mkNameLit(x_128, x_129);
x_131 = lean_mk_empty_array_with_capacity(x_72);
x_132 = lean_array_push(x_131, x_130);
x_133 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_133, 0, x_129);
lean_ctor_set(x_133, 1, x_124);
lean_ctor_set(x_133, 2, x_132);
x_18 = x_117;
x_19 = x_68;
x_20 = x_72;
x_21 = x_94;
x_22 = x_70;
x_23 = x_119;
x_24 = x_96;
x_25 = x_67;
x_26 = x_104;
x_27 = x_133;
goto block_32;
}
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_134 = lean_ctor_get(x_91, 0);
x_135 = lean_ctor_get(x_91, 1);
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_91);
x_136 = lean_ctor_get(x_60, 5);
lean_inc(x_136);
x_137 = l_Lean_SourceInfo_fromRef(x_136, x_73);
lean_dec(x_136);
x_138 = lean_ctor_get(x_60, 10);
lean_inc(x_138);
lean_dec(x_60);
x_139 = lean_ctor_get(x_134, 0);
lean_inc(x_139);
lean_dec(x_134);
x_140 = l_Lean_Environment_mainModule(x_139);
lean_dec(x_139);
x_141 = lean_mk_string_unchecked("Lean", 4, 4);
x_142 = lean_mk_string_unchecked("Parser", 6, 6);
x_143 = lean_mk_string_unchecked("Term", 4, 4);
x_144 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_143);
lean_inc(x_142);
lean_inc(x_141);
x_145 = l_Lean_Name_mkStr4(x_141, x_142, x_143, x_144);
x_146 = lean_mk_string_unchecked("ParserDescr.binary", 18, 18);
x_147 = l_String_toSubstring_x27(x_146);
x_148 = lean_mk_string_unchecked("ParserDescr", 11, 11);
x_149 = lean_mk_string_unchecked("binary", 6, 6);
lean_inc(x_149);
lean_inc(x_148);
x_150 = l_Lean_Name_mkStr2(x_148, x_149);
x_151 = l_Lean_addMacroScope(x_140, x_150, x_138);
lean_inc(x_141);
x_152 = l_Lean_Name_mkStr3(x_141, x_148, x_149);
x_153 = lean_box(0);
lean_inc(x_152);
x_154 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_154, 0, x_152);
lean_ctor_set(x_154, 1, x_153);
x_155 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_155, 0, x_152);
x_156 = lean_box(0);
x_157 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_157, 0, x_155);
lean_ctor_set(x_157, 1, x_156);
x_158 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_158, 0, x_154);
lean_ctor_set(x_158, 1, x_157);
lean_inc(x_137);
x_159 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_159, 0, x_137);
lean_ctor_set(x_159, 1, x_147);
lean_ctor_set(x_159, 2, x_151);
lean_ctor_set(x_159, 3, x_158);
x_160 = lean_mk_string_unchecked("null", 4, 4);
x_161 = l_Lean_Name_mkStr1(x_160);
lean_inc(x_57);
x_162 = l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(x_153, x_57);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; 
lean_dec(x_143);
lean_dec(x_142);
lean_dec(x_141);
x_163 = l_Lean_quoteNameMk(x_57);
x_18 = x_159;
x_19 = x_68;
x_20 = x_72;
x_21 = x_135;
x_22 = x_70;
x_23 = x_161;
x_24 = x_137;
x_25 = x_67;
x_26 = x_145;
x_27 = x_163;
goto block_32;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
lean_dec(x_57);
x_164 = lean_ctor_get(x_162, 0);
lean_inc(x_164);
lean_dec(x_162);
x_165 = lean_mk_string_unchecked("quotedName", 10, 10);
x_166 = l_Lean_Name_mkStr4(x_141, x_142, x_143, x_165);
x_167 = lean_mk_string_unchecked("`", 1, 1);
x_168 = lean_mk_string_unchecked(".", 1, 1);
x_169 = l_String_intercalate(x_168, x_164);
lean_dec(x_168);
x_170 = lean_string_append(x_167, x_169);
lean_dec(x_169);
x_171 = lean_box(2);
x_172 = l_Lean_Syntax_mkNameLit(x_170, x_171);
x_173 = lean_mk_empty_array_with_capacity(x_72);
x_174 = lean_array_push(x_173, x_172);
x_175 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_175, 0, x_171);
lean_ctor_set(x_175, 1, x_166);
lean_ctor_set(x_175, 2, x_174);
x_18 = x_159;
x_19 = x_68;
x_20 = x_72;
x_21 = x_135;
x_22 = x_70;
x_23 = x_161;
x_24 = x_137;
x_25 = x_67;
x_26 = x_145;
x_27 = x_175;
goto block_32;
}
}
}
else
{
uint8_t x_176; 
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_57);
x_176 = !lean_is_exclusive(x_89);
if (x_176 == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_177 = lean_ctor_get(x_89, 0);
x_178 = lean_ctor_get(x_60, 5);
lean_inc(x_178);
lean_dec(x_60);
x_179 = lean_io_error_to_string(x_177);
x_180 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_180, 0, x_179);
x_181 = l_Lean_MessageData_ofFormat(x_180);
x_182 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_182, 0, x_178);
lean_ctor_set(x_182, 1, x_181);
lean_ctor_set(x_89, 0, x_182);
return x_89;
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_183 = lean_ctor_get(x_89, 0);
x_184 = lean_ctor_get(x_89, 1);
lean_inc(x_184);
lean_inc(x_183);
lean_dec(x_89);
x_185 = lean_ctor_get(x_60, 5);
lean_inc(x_185);
lean_dec(x_60);
x_186 = lean_io_error_to_string(x_183);
x_187 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_187, 0, x_186);
x_188 = l_Lean_MessageData_ofFormat(x_187);
x_189 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_189, 0, x_185);
lean_ctor_set(x_189, 1, x_188);
x_190 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_190, 0, x_189);
lean_ctor_set(x_190, 1, x_184);
return x_190;
}
}
}
}
else
{
lean_object* x_191; 
lean_dec(x_69);
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_59);
lean_dec(x_58);
lean_inc(x_57);
x_191 = l_Lean_Parser_ensureUnaryParserAlias(x_57, x_61);
if (lean_obj_tag(x_191) == 0)
{
lean_object* x_192; lean_object* x_193; uint8_t x_194; 
x_192 = lean_ctor_get(x_191, 1);
lean_inc(x_192);
lean_dec(x_191);
x_193 = lean_st_ref_get(x_66, x_192);
lean_dec(x_66);
x_194 = !lean_is_exclusive(x_193);
if (x_194 == 0)
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_195 = lean_ctor_get(x_193, 0);
x_196 = lean_ctor_get(x_193, 1);
x_197 = lean_ctor_get(x_60, 5);
lean_inc(x_197);
x_198 = l_Lean_SourceInfo_fromRef(x_197, x_71);
lean_dec(x_197);
x_199 = lean_ctor_get(x_60, 10);
lean_inc(x_199);
lean_dec(x_60);
x_200 = lean_ctor_get(x_195, 0);
lean_inc(x_200);
lean_dec(x_195);
x_201 = l_Lean_Environment_mainModule(x_200);
lean_dec(x_200);
x_202 = lean_mk_string_unchecked("Lean", 4, 4);
x_203 = lean_mk_string_unchecked("Parser", 6, 6);
x_204 = lean_mk_string_unchecked("Term", 4, 4);
x_205 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_204);
lean_inc(x_203);
lean_inc(x_202);
x_206 = l_Lean_Name_mkStr4(x_202, x_203, x_204, x_205);
x_207 = lean_mk_string_unchecked("ParserDescr.unary", 17, 17);
x_208 = l_String_toSubstring_x27(x_207);
x_209 = lean_mk_string_unchecked("ParserDescr", 11, 11);
x_210 = lean_mk_string_unchecked("unary", 5, 5);
lean_inc(x_210);
lean_inc(x_209);
x_211 = l_Lean_Name_mkStr2(x_209, x_210);
x_212 = l_Lean_addMacroScope(x_201, x_211, x_199);
lean_inc(x_202);
x_213 = l_Lean_Name_mkStr3(x_202, x_209, x_210);
x_214 = lean_box(0);
lean_inc(x_213);
lean_ctor_set_tag(x_193, 1);
lean_ctor_set(x_193, 1, x_214);
lean_ctor_set(x_193, 0, x_213);
x_215 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_215, 0, x_213);
x_216 = lean_box(0);
x_217 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_217, 0, x_215);
lean_ctor_set(x_217, 1, x_216);
x_218 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_218, 0, x_193);
lean_ctor_set(x_218, 1, x_217);
lean_inc(x_198);
x_219 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_219, 0, x_198);
lean_ctor_set(x_219, 1, x_208);
lean_ctor_set(x_219, 2, x_212);
lean_ctor_set(x_219, 3, x_218);
x_220 = lean_mk_string_unchecked("null", 4, 4);
x_221 = l_Lean_Name_mkStr1(x_220);
lean_inc(x_57);
x_222 = l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(x_214, x_57);
if (lean_obj_tag(x_222) == 0)
{
lean_object* x_223; 
lean_dec(x_204);
lean_dec(x_203);
lean_dec(x_202);
x_223 = l_Lean_quoteNameMk(x_57);
x_33 = x_68;
x_34 = x_196;
x_35 = x_70;
x_36 = x_206;
x_37 = x_221;
x_38 = x_198;
x_39 = x_219;
x_40 = x_67;
x_41 = x_223;
goto block_45;
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
lean_dec(x_57);
x_224 = lean_ctor_get(x_222, 0);
lean_inc(x_224);
lean_dec(x_222);
x_225 = lean_mk_string_unchecked("quotedName", 10, 10);
x_226 = l_Lean_Name_mkStr4(x_202, x_203, x_204, x_225);
x_227 = lean_mk_string_unchecked("`", 1, 1);
x_228 = lean_mk_string_unchecked(".", 1, 1);
x_229 = l_String_intercalate(x_228, x_224);
lean_dec(x_228);
x_230 = lean_string_append(x_227, x_229);
lean_dec(x_229);
x_231 = lean_box(2);
x_232 = l_Lean_Syntax_mkNameLit(x_230, x_231);
x_233 = lean_mk_empty_array_with_capacity(x_72);
x_234 = lean_array_push(x_233, x_232);
x_235 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_235, 0, x_231);
lean_ctor_set(x_235, 1, x_226);
lean_ctor_set(x_235, 2, x_234);
x_33 = x_68;
x_34 = x_196;
x_35 = x_70;
x_36 = x_206;
x_37 = x_221;
x_38 = x_198;
x_39 = x_219;
x_40 = x_67;
x_41 = x_235;
goto block_45;
}
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_236 = lean_ctor_get(x_193, 0);
x_237 = lean_ctor_get(x_193, 1);
lean_inc(x_237);
lean_inc(x_236);
lean_dec(x_193);
x_238 = lean_ctor_get(x_60, 5);
lean_inc(x_238);
x_239 = l_Lean_SourceInfo_fromRef(x_238, x_71);
lean_dec(x_238);
x_240 = lean_ctor_get(x_60, 10);
lean_inc(x_240);
lean_dec(x_60);
x_241 = lean_ctor_get(x_236, 0);
lean_inc(x_241);
lean_dec(x_236);
x_242 = l_Lean_Environment_mainModule(x_241);
lean_dec(x_241);
x_243 = lean_mk_string_unchecked("Lean", 4, 4);
x_244 = lean_mk_string_unchecked("Parser", 6, 6);
x_245 = lean_mk_string_unchecked("Term", 4, 4);
x_246 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_245);
lean_inc(x_244);
lean_inc(x_243);
x_247 = l_Lean_Name_mkStr4(x_243, x_244, x_245, x_246);
x_248 = lean_mk_string_unchecked("ParserDescr.unary", 17, 17);
x_249 = l_String_toSubstring_x27(x_248);
x_250 = lean_mk_string_unchecked("ParserDescr", 11, 11);
x_251 = lean_mk_string_unchecked("unary", 5, 5);
lean_inc(x_251);
lean_inc(x_250);
x_252 = l_Lean_Name_mkStr2(x_250, x_251);
x_253 = l_Lean_addMacroScope(x_242, x_252, x_240);
lean_inc(x_243);
x_254 = l_Lean_Name_mkStr3(x_243, x_250, x_251);
x_255 = lean_box(0);
lean_inc(x_254);
x_256 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_256, 0, x_254);
lean_ctor_set(x_256, 1, x_255);
x_257 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_257, 0, x_254);
x_258 = lean_box(0);
x_259 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_259, 0, x_257);
lean_ctor_set(x_259, 1, x_258);
x_260 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_260, 0, x_256);
lean_ctor_set(x_260, 1, x_259);
lean_inc(x_239);
x_261 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_261, 0, x_239);
lean_ctor_set(x_261, 1, x_249);
lean_ctor_set(x_261, 2, x_253);
lean_ctor_set(x_261, 3, x_260);
x_262 = lean_mk_string_unchecked("null", 4, 4);
x_263 = l_Lean_Name_mkStr1(x_262);
lean_inc(x_57);
x_264 = l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(x_255, x_57);
if (lean_obj_tag(x_264) == 0)
{
lean_object* x_265; 
lean_dec(x_245);
lean_dec(x_244);
lean_dec(x_243);
x_265 = l_Lean_quoteNameMk(x_57);
x_33 = x_68;
x_34 = x_237;
x_35 = x_70;
x_36 = x_247;
x_37 = x_263;
x_38 = x_239;
x_39 = x_261;
x_40 = x_67;
x_41 = x_265;
goto block_45;
}
else
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; 
lean_dec(x_57);
x_266 = lean_ctor_get(x_264, 0);
lean_inc(x_266);
lean_dec(x_264);
x_267 = lean_mk_string_unchecked("quotedName", 10, 10);
x_268 = l_Lean_Name_mkStr4(x_243, x_244, x_245, x_267);
x_269 = lean_mk_string_unchecked("`", 1, 1);
x_270 = lean_mk_string_unchecked(".", 1, 1);
x_271 = l_String_intercalate(x_270, x_266);
lean_dec(x_270);
x_272 = lean_string_append(x_269, x_271);
lean_dec(x_271);
x_273 = lean_box(2);
x_274 = l_Lean_Syntax_mkNameLit(x_272, x_273);
x_275 = lean_mk_empty_array_with_capacity(x_72);
x_276 = lean_array_push(x_275, x_274);
x_277 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_277, 0, x_273);
lean_ctor_set(x_277, 1, x_268);
lean_ctor_set(x_277, 2, x_276);
x_33 = x_68;
x_34 = x_237;
x_35 = x_70;
x_36 = x_247;
x_37 = x_263;
x_38 = x_239;
x_39 = x_261;
x_40 = x_67;
x_41 = x_277;
goto block_45;
}
}
}
else
{
uint8_t x_278; 
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_57);
x_278 = !lean_is_exclusive(x_191);
if (x_278 == 0)
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; 
x_279 = lean_ctor_get(x_191, 0);
x_280 = lean_ctor_get(x_60, 5);
lean_inc(x_280);
lean_dec(x_60);
x_281 = lean_io_error_to_string(x_279);
x_282 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_282, 0, x_281);
x_283 = l_Lean_MessageData_ofFormat(x_282);
x_284 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_284, 0, x_280);
lean_ctor_set(x_284, 1, x_283);
lean_ctor_set(x_191, 0, x_284);
return x_191;
}
else
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_285 = lean_ctor_get(x_191, 0);
x_286 = lean_ctor_get(x_191, 1);
lean_inc(x_286);
lean_inc(x_285);
lean_dec(x_191);
x_287 = lean_ctor_get(x_60, 5);
lean_inc(x_287);
lean_dec(x_60);
x_288 = lean_io_error_to_string(x_285);
x_289 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_289, 0, x_288);
x_290 = l_Lean_MessageData_ofFormat(x_289);
x_291 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_291, 0, x_287);
lean_ctor_set(x_291, 1, x_290);
x_292 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_292, 0, x_291);
lean_ctor_set(x_292, 1, x_286);
return x_292;
}
}
}
}
else
{
lean_object* x_293; 
lean_dec(x_69);
lean_dec(x_67);
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_59);
lean_dec(x_58);
lean_inc(x_57);
x_293 = l_Lean_Parser_ensureConstantParserAlias(x_57, x_61);
if (lean_obj_tag(x_293) == 0)
{
lean_object* x_294; lean_object* x_295; uint8_t x_296; 
x_294 = lean_ctor_get(x_293, 1);
lean_inc(x_294);
lean_dec(x_293);
x_295 = lean_st_ref_get(x_66, x_294);
lean_dec(x_66);
x_296 = !lean_is_exclusive(x_295);
if (x_296 == 0)
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; uint8_t x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; 
x_297 = lean_ctor_get(x_295, 0);
x_298 = lean_ctor_get(x_295, 1);
x_299 = lean_ctor_get(x_60, 5);
lean_inc(x_299);
x_300 = lean_box(0);
x_301 = lean_unbox(x_300);
x_302 = l_Lean_SourceInfo_fromRef(x_299, x_301);
lean_dec(x_299);
x_303 = lean_ctor_get(x_60, 10);
lean_inc(x_303);
lean_dec(x_60);
x_304 = lean_ctor_get(x_297, 0);
lean_inc(x_304);
lean_dec(x_297);
x_305 = l_Lean_Environment_mainModule(x_304);
lean_dec(x_304);
x_306 = lean_mk_string_unchecked("Lean", 4, 4);
x_307 = lean_mk_string_unchecked("Parser", 6, 6);
x_308 = lean_mk_string_unchecked("Term", 4, 4);
x_309 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_308);
lean_inc(x_307);
lean_inc(x_306);
x_310 = l_Lean_Name_mkStr4(x_306, x_307, x_308, x_309);
x_311 = lean_mk_string_unchecked("ParserDescr.const", 17, 17);
x_312 = l_String_toSubstring_x27(x_311);
x_313 = lean_mk_string_unchecked("ParserDescr", 11, 11);
x_314 = lean_mk_string_unchecked("const", 5, 5);
lean_inc(x_314);
lean_inc(x_313);
x_315 = l_Lean_Name_mkStr2(x_313, x_314);
x_316 = l_Lean_addMacroScope(x_305, x_315, x_303);
lean_inc(x_306);
x_317 = l_Lean_Name_mkStr3(x_306, x_313, x_314);
x_318 = lean_box(0);
lean_inc(x_317);
lean_ctor_set_tag(x_295, 1);
lean_ctor_set(x_295, 1, x_318);
lean_ctor_set(x_295, 0, x_317);
x_319 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_319, 0, x_317);
x_320 = lean_box(0);
x_321 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_321, 0, x_319);
lean_ctor_set(x_321, 1, x_320);
x_322 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_322, 0, x_295);
lean_ctor_set(x_322, 1, x_321);
lean_inc(x_302);
x_323 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_323, 0, x_302);
lean_ctor_set(x_323, 1, x_312);
lean_ctor_set(x_323, 2, x_316);
lean_ctor_set(x_323, 3, x_322);
x_324 = lean_mk_string_unchecked("null", 4, 4);
x_325 = l_Lean_Name_mkStr1(x_324);
lean_inc(x_57);
x_326 = l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(x_318, x_57);
if (lean_obj_tag(x_326) == 0)
{
lean_object* x_327; 
lean_dec(x_308);
lean_dec(x_307);
lean_dec(x_306);
x_327 = l_Lean_quoteNameMk(x_57);
x_46 = x_68;
x_47 = x_323;
x_48 = x_298;
x_49 = x_325;
x_50 = x_302;
x_51 = x_310;
x_52 = x_327;
goto block_55;
}
else
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; 
lean_dec(x_57);
x_328 = lean_ctor_get(x_326, 0);
lean_inc(x_328);
lean_dec(x_326);
x_329 = lean_mk_string_unchecked("quotedName", 10, 10);
x_330 = l_Lean_Name_mkStr4(x_306, x_307, x_308, x_329);
x_331 = lean_mk_string_unchecked("`", 1, 1);
x_332 = lean_mk_string_unchecked(".", 1, 1);
x_333 = l_String_intercalate(x_332, x_328);
lean_dec(x_332);
x_334 = lean_string_append(x_331, x_333);
lean_dec(x_333);
x_335 = lean_box(2);
x_336 = l_Lean_Syntax_mkNameLit(x_334, x_335);
x_337 = lean_unsigned_to_nat(1u);
x_338 = lean_mk_empty_array_with_capacity(x_337);
x_339 = lean_array_push(x_338, x_336);
x_340 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_340, 0, x_335);
lean_ctor_set(x_340, 1, x_330);
lean_ctor_set(x_340, 2, x_339);
x_46 = x_68;
x_47 = x_323;
x_48 = x_298;
x_49 = x_325;
x_50 = x_302;
x_51 = x_310;
x_52 = x_340;
goto block_55;
}
}
else
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; uint8_t x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; 
x_341 = lean_ctor_get(x_295, 0);
x_342 = lean_ctor_get(x_295, 1);
lean_inc(x_342);
lean_inc(x_341);
lean_dec(x_295);
x_343 = lean_ctor_get(x_60, 5);
lean_inc(x_343);
x_344 = lean_box(0);
x_345 = lean_unbox(x_344);
x_346 = l_Lean_SourceInfo_fromRef(x_343, x_345);
lean_dec(x_343);
x_347 = lean_ctor_get(x_60, 10);
lean_inc(x_347);
lean_dec(x_60);
x_348 = lean_ctor_get(x_341, 0);
lean_inc(x_348);
lean_dec(x_341);
x_349 = l_Lean_Environment_mainModule(x_348);
lean_dec(x_348);
x_350 = lean_mk_string_unchecked("Lean", 4, 4);
x_351 = lean_mk_string_unchecked("Parser", 6, 6);
x_352 = lean_mk_string_unchecked("Term", 4, 4);
x_353 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_352);
lean_inc(x_351);
lean_inc(x_350);
x_354 = l_Lean_Name_mkStr4(x_350, x_351, x_352, x_353);
x_355 = lean_mk_string_unchecked("ParserDescr.const", 17, 17);
x_356 = l_String_toSubstring_x27(x_355);
x_357 = lean_mk_string_unchecked("ParserDescr", 11, 11);
x_358 = lean_mk_string_unchecked("const", 5, 5);
lean_inc(x_358);
lean_inc(x_357);
x_359 = l_Lean_Name_mkStr2(x_357, x_358);
x_360 = l_Lean_addMacroScope(x_349, x_359, x_347);
lean_inc(x_350);
x_361 = l_Lean_Name_mkStr3(x_350, x_357, x_358);
x_362 = lean_box(0);
lean_inc(x_361);
x_363 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_363, 0, x_361);
lean_ctor_set(x_363, 1, x_362);
x_364 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_364, 0, x_361);
x_365 = lean_box(0);
x_366 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_366, 0, x_364);
lean_ctor_set(x_366, 1, x_365);
x_367 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_367, 0, x_363);
lean_ctor_set(x_367, 1, x_366);
lean_inc(x_346);
x_368 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_368, 0, x_346);
lean_ctor_set(x_368, 1, x_356);
lean_ctor_set(x_368, 2, x_360);
lean_ctor_set(x_368, 3, x_367);
x_369 = lean_mk_string_unchecked("null", 4, 4);
x_370 = l_Lean_Name_mkStr1(x_369);
lean_inc(x_57);
x_371 = l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(x_362, x_57);
if (lean_obj_tag(x_371) == 0)
{
lean_object* x_372; 
lean_dec(x_352);
lean_dec(x_351);
lean_dec(x_350);
x_372 = l_Lean_quoteNameMk(x_57);
x_46 = x_68;
x_47 = x_368;
x_48 = x_342;
x_49 = x_370;
x_50 = x_346;
x_51 = x_354;
x_52 = x_372;
goto block_55;
}
else
{
lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; 
lean_dec(x_57);
x_373 = lean_ctor_get(x_371, 0);
lean_inc(x_373);
lean_dec(x_371);
x_374 = lean_mk_string_unchecked("quotedName", 10, 10);
x_375 = l_Lean_Name_mkStr4(x_350, x_351, x_352, x_374);
x_376 = lean_mk_string_unchecked("`", 1, 1);
x_377 = lean_mk_string_unchecked(".", 1, 1);
x_378 = l_String_intercalate(x_377, x_373);
lean_dec(x_377);
x_379 = lean_string_append(x_376, x_378);
lean_dec(x_378);
x_380 = lean_box(2);
x_381 = l_Lean_Syntax_mkNameLit(x_379, x_380);
x_382 = lean_unsigned_to_nat(1u);
x_383 = lean_mk_empty_array_with_capacity(x_382);
x_384 = lean_array_push(x_383, x_381);
x_385 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_385, 0, x_380);
lean_ctor_set(x_385, 1, x_375);
lean_ctor_set(x_385, 2, x_384);
x_46 = x_68;
x_47 = x_368;
x_48 = x_342;
x_49 = x_370;
x_50 = x_346;
x_51 = x_354;
x_52 = x_385;
goto block_55;
}
}
}
else
{
uint8_t x_386; 
lean_dec(x_68);
lean_dec(x_66);
lean_dec(x_57);
x_386 = !lean_is_exclusive(x_293);
if (x_386 == 0)
{
lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; 
x_387 = lean_ctor_get(x_293, 0);
x_388 = lean_ctor_get(x_60, 5);
lean_inc(x_388);
lean_dec(x_60);
x_389 = lean_io_error_to_string(x_387);
x_390 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_390, 0, x_389);
x_391 = l_Lean_MessageData_ofFormat(x_390);
x_392 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_392, 0, x_388);
lean_ctor_set(x_392, 1, x_391);
lean_ctor_set(x_293, 0, x_392);
return x_293;
}
else
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; 
x_393 = lean_ctor_get(x_293, 0);
x_394 = lean_ctor_get(x_293, 1);
lean_inc(x_394);
lean_inc(x_393);
lean_dec(x_293);
x_395 = lean_ctor_get(x_60, 5);
lean_inc(x_395);
lean_dec(x_60);
x_396 = lean_io_error_to_string(x_393);
x_397 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_397, 0, x_396);
x_398 = l_Lean_MessageData_ofFormat(x_397);
x_399 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_399, 0, x_395);
lean_ctor_set(x_399, 1, x_398);
x_400 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_400, 0, x_399);
lean_ctor_set(x_400, 1, x_394);
return x_400;
}
}
}
}
block_437:
{
lean_object* x_415; 
x_415 = lean_ctor_get(x_403, 1);
lean_inc(x_415);
if (lean_obj_tag(x_415) == 0)
{
lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; uint8_t x_421; 
lean_dec(x_403);
x_416 = l_Array_unzip___redArg(x_405);
lean_dec(x_405);
x_417 = lean_ctor_get(x_416, 0);
lean_inc(x_417);
x_418 = lean_ctor_get(x_416, 1);
lean_inc(x_418);
lean_dec(x_416);
x_419 = lean_unsigned_to_nat(0u);
x_420 = lean_array_get_size(x_418);
x_421 = lean_nat_dec_lt(x_419, x_420);
if (x_421 == 0)
{
lean_dec(x_420);
lean_dec(x_418);
x_58 = x_406;
x_59 = x_410;
x_60 = x_412;
x_61 = x_414;
x_62 = x_411;
x_63 = x_407;
x_64 = x_408;
x_65 = x_409;
x_66 = x_413;
x_67 = x_417;
x_68 = x_419;
goto block_401;
}
else
{
uint8_t x_422; 
x_422 = lean_nat_dec_le(x_420, x_420);
if (x_422 == 0)
{
lean_dec(x_420);
lean_dec(x_418);
x_58 = x_406;
x_59 = x_410;
x_60 = x_412;
x_61 = x_414;
x_62 = x_411;
x_63 = x_407;
x_64 = x_408;
x_65 = x_409;
x_66 = x_413;
x_67 = x_417;
x_68 = x_419;
goto block_401;
}
else
{
size_t x_423; size_t x_424; lean_object* x_425; 
x_423 = lean_usize_of_nat(x_419);
x_424 = lean_usize_of_nat(x_420);
lean_dec(x_420);
x_425 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_Term_toParserDescr_processAlias_spec__1(x_418, x_423, x_424, x_419);
lean_dec(x_418);
x_58 = x_406;
x_59 = x_410;
x_60 = x_412;
x_61 = x_414;
x_62 = x_411;
x_63 = x_407;
x_64 = x_408;
x_65 = x_409;
x_66 = x_413;
x_67 = x_417;
x_68 = x_425;
goto block_401;
}
}
}
else
{
uint8_t x_426; 
x_426 = lean_ctor_get_uint8(x_403, sizeof(void*)*2);
lean_dec(x_403);
if (x_426 == 0)
{
lean_object* x_427; size_t x_428; lean_object* x_429; size_t x_430; lean_object* x_431; 
x_427 = lean_ctor_get(x_415, 0);
lean_inc(x_427);
lean_dec(x_415);
x_428 = lean_array_size(x_405);
x_429 = lean_unsigned_to_nat(0u);
x_430 = lean_usize_of_nat(x_429);
x_431 = l_Array_mapMUnsafe_map___at___Lean_Elab_Term_toParserDescr_processAlias_spec__2(x_428, x_430, x_405);
x_58 = x_406;
x_59 = x_410;
x_60 = x_412;
x_61 = x_414;
x_62 = x_411;
x_63 = x_407;
x_64 = x_408;
x_65 = x_409;
x_66 = x_413;
x_67 = x_431;
x_68 = x_427;
goto block_401;
}
else
{
lean_object* x_432; size_t x_433; lean_object* x_434; size_t x_435; lean_object* x_436; 
x_432 = lean_ctor_get(x_415, 0);
lean_inc(x_432);
lean_dec(x_415);
x_433 = lean_array_size(x_405);
x_434 = lean_unsigned_to_nat(0u);
x_435 = lean_usize_of_nat(x_434);
x_436 = l_Array_mapMUnsafe_map___at___Lean_Elab_Term_toParserDescr_processAlias_spec__3(x_433, x_435, x_405);
x_58 = x_406;
x_59 = x_410;
x_60 = x_412;
x_61 = x_414;
x_62 = x_411;
x_63 = x_407;
x_64 = x_408;
x_65 = x_409;
x_66 = x_413;
x_67 = x_436;
x_68 = x_432;
goto block_401;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr_processNullaryOrCat(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_12);
x_13 = l_Lean_Elab_Term_elabParserName_x3f(x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Syntax_getId(x_12);
x_17 = lean_erase_macro_scopes(x_16);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_18 = lean_mk_string_unchecked("unknown parser declaration/category/alias '", 43, 43);
x_19 = l_Lean_stringToMessageData(x_18);
lean_dec(x_18);
x_20 = l_Lean_MessageData_ofName(x_17);
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_mk_string_unchecked("'", 1, 1);
x_23 = l_Lean_stringToMessageData(x_22);
lean_dec(x_22);
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0_spec__3_spec__3___redArg(x_24, x_6, x_7, x_8, x_9, x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_25;
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_14);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_14, 0);
switch (lean_obj_tag(x_27)) {
case 0:
{
lean_object* x_28; 
lean_free_object(x_14);
lean_dec(x_27);
lean_dec(x_17);
lean_dec(x_12);
x_28 = l_Lean_Elab_Term_toParserDescr_processParserCategory(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_15);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_28;
}
case 1:
{
uint8_t x_29; 
x_29 = lean_ctor_get_uint8(x_27, sizeof(void*)*1);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_ctor_get(x_27, 0);
lean_inc(x_30);
lean_dec(x_27);
x_31 = l_Lean_Parser_getParserAliasInfo(x_17, x_15);
lean_dec(x_17);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = lean_ctor_get(x_31, 1);
x_35 = lean_ctor_get(x_33, 0);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_name_eq(x_35, x_30);
lean_dec(x_35);
if (x_36 == 0)
{
lean_object* x_37; 
lean_dec(x_12);
x_37 = l_Lean_Elab_Term_toParserDescr_ensureNoPrec(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_34);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_74; 
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_39 = lean_st_ref_get(x_9, x_38);
lean_dec(x_9);
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
x_43 = lean_ctor_get(x_8, 5);
lean_inc(x_43);
x_44 = lean_unsigned_to_nat(1u);
x_45 = l_Lean_SourceInfo_fromRef(x_43, x_29);
lean_dec(x_43);
x_46 = lean_ctor_get(x_8, 10);
lean_inc(x_46);
lean_dec(x_8);
x_47 = lean_ctor_get(x_40, 0);
lean_inc(x_47);
lean_dec(x_40);
x_48 = l_Lean_Environment_mainModule(x_47);
lean_dec(x_47);
x_49 = lean_mk_string_unchecked("Lean", 4, 4);
x_50 = lean_mk_string_unchecked("Parser", 6, 6);
x_51 = lean_mk_string_unchecked("Term", 4, 4);
x_52 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
x_53 = l_Lean_Name_mkStr4(x_49, x_50, x_51, x_52);
x_54 = lean_mk_string_unchecked("ParserDescr.parser", 18, 18);
x_55 = l_String_toSubstring_x27(x_54);
x_56 = lean_mk_string_unchecked("ParserDescr", 11, 11);
x_57 = lean_mk_string_unchecked("parser", 6, 6);
lean_inc(x_57);
lean_inc(x_56);
x_58 = l_Lean_Name_mkStr2(x_56, x_57);
x_59 = l_Lean_addMacroScope(x_48, x_58, x_46);
lean_inc(x_49);
x_60 = l_Lean_Name_mkStr3(x_49, x_56, x_57);
x_61 = lean_box(0);
lean_inc(x_60);
lean_ctor_set_tag(x_31, 1);
lean_ctor_set(x_31, 1, x_61);
lean_ctor_set(x_31, 0, x_60);
lean_ctor_set_tag(x_14, 0);
lean_ctor_set(x_14, 0, x_60);
x_62 = lean_box(0);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_14);
lean_ctor_set(x_63, 1, x_62);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_31);
lean_ctor_set(x_64, 1, x_63);
lean_inc(x_45);
x_65 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_65, 0, x_45);
lean_ctor_set(x_65, 1, x_55);
lean_ctor_set(x_65, 2, x_59);
lean_ctor_set(x_65, 3, x_64);
x_66 = lean_mk_string_unchecked("null", 4, 4);
x_67 = l_Lean_Name_mkStr1(x_66);
lean_inc(x_30);
x_74 = l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(x_61, x_30);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; 
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_49);
x_75 = l_Lean_quoteNameMk(x_30);
x_68 = x_75;
goto block_73;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_30);
x_76 = lean_ctor_get(x_74, 0);
lean_inc(x_76);
lean_dec(x_74);
x_77 = lean_mk_string_unchecked("quotedName", 10, 10);
x_78 = l_Lean_Name_mkStr4(x_49, x_50, x_51, x_77);
x_79 = lean_mk_string_unchecked("`", 1, 1);
x_80 = lean_mk_string_unchecked(".", 1, 1);
x_81 = l_String_intercalate(x_80, x_76);
lean_dec(x_80);
x_82 = lean_string_append(x_79, x_81);
lean_dec(x_81);
x_83 = lean_box(2);
x_84 = l_Lean_Syntax_mkNameLit(x_82, x_83);
x_85 = lean_mk_empty_array_with_capacity(x_44);
x_86 = lean_array_push(x_85, x_84);
x_87 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_87, 0, x_83);
lean_ctor_set(x_87, 1, x_78);
lean_ctor_set(x_87, 2, x_86);
x_68 = x_87;
goto block_73;
}
block_73:
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_inc(x_45);
x_69 = l_Lean_Syntax_node1(x_45, x_67, x_68);
x_70 = l_Lean_Syntax_node2(x_45, x_53, x_65, x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_44);
if (lean_is_scalar(x_42)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_42;
}
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_41);
return x_72;
}
}
else
{
uint8_t x_88; 
lean_free_object(x_31);
lean_dec(x_30);
lean_free_object(x_14);
lean_dec(x_9);
lean_dec(x_8);
x_88 = !lean_is_exclusive(x_37);
if (x_88 == 0)
{
return x_37;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_37, 0);
x_90 = lean_ctor_get(x_37, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_37);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
else
{
lean_object* x_92; 
lean_free_object(x_31);
lean_dec(x_30);
lean_free_object(x_14);
x_92 = l_Lean_Elab_Term_toParserDescr_ensureNoPrec(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_34);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
lean_dec(x_92);
x_94 = lean_mk_empty_array_with_capacity(x_11);
x_95 = l_Lean_Elab_Term_toParserDescr_processAlias(x_12, x_94, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_93);
return x_95;
}
else
{
uint8_t x_96; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_96 = !lean_is_exclusive(x_92);
if (x_96 == 0)
{
return x_92;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_92, 0);
x_98 = lean_ctor_get(x_92, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_92);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_100 = lean_ctor_get(x_31, 0);
x_101 = lean_ctor_get(x_31, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_31);
x_102 = lean_ctor_get(x_100, 0);
lean_inc(x_102);
lean_dec(x_100);
x_103 = lean_name_eq(x_102, x_30);
lean_dec(x_102);
if (x_103 == 0)
{
lean_object* x_104; 
lean_dec(x_12);
x_104 = l_Lean_Elab_Term_toParserDescr_ensureNoPrec(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_101);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_142; 
x_105 = lean_ctor_get(x_104, 1);
lean_inc(x_105);
lean_dec(x_104);
x_106 = lean_st_ref_get(x_9, x_105);
lean_dec(x_9);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_109 = x_106;
} else {
 lean_dec_ref(x_106);
 x_109 = lean_box(0);
}
x_110 = lean_ctor_get(x_8, 5);
lean_inc(x_110);
x_111 = lean_unsigned_to_nat(1u);
x_112 = l_Lean_SourceInfo_fromRef(x_110, x_29);
lean_dec(x_110);
x_113 = lean_ctor_get(x_8, 10);
lean_inc(x_113);
lean_dec(x_8);
x_114 = lean_ctor_get(x_107, 0);
lean_inc(x_114);
lean_dec(x_107);
x_115 = l_Lean_Environment_mainModule(x_114);
lean_dec(x_114);
x_116 = lean_mk_string_unchecked("Lean", 4, 4);
x_117 = lean_mk_string_unchecked("Parser", 6, 6);
x_118 = lean_mk_string_unchecked("Term", 4, 4);
x_119 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_118);
lean_inc(x_117);
lean_inc(x_116);
x_120 = l_Lean_Name_mkStr4(x_116, x_117, x_118, x_119);
x_121 = lean_mk_string_unchecked("ParserDescr.parser", 18, 18);
x_122 = l_String_toSubstring_x27(x_121);
x_123 = lean_mk_string_unchecked("ParserDescr", 11, 11);
x_124 = lean_mk_string_unchecked("parser", 6, 6);
lean_inc(x_124);
lean_inc(x_123);
x_125 = l_Lean_Name_mkStr2(x_123, x_124);
x_126 = l_Lean_addMacroScope(x_115, x_125, x_113);
lean_inc(x_116);
x_127 = l_Lean_Name_mkStr3(x_116, x_123, x_124);
x_128 = lean_box(0);
lean_inc(x_127);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
lean_ctor_set_tag(x_14, 0);
lean_ctor_set(x_14, 0, x_127);
x_130 = lean_box(0);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_14);
lean_ctor_set(x_131, 1, x_130);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_129);
lean_ctor_set(x_132, 1, x_131);
lean_inc(x_112);
x_133 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_133, 0, x_112);
lean_ctor_set(x_133, 1, x_122);
lean_ctor_set(x_133, 2, x_126);
lean_ctor_set(x_133, 3, x_132);
x_134 = lean_mk_string_unchecked("null", 4, 4);
x_135 = l_Lean_Name_mkStr1(x_134);
lean_inc(x_30);
x_142 = l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(x_128, x_30);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; 
lean_dec(x_118);
lean_dec(x_117);
lean_dec(x_116);
x_143 = l_Lean_quoteNameMk(x_30);
x_136 = x_143;
goto block_141;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_dec(x_30);
x_144 = lean_ctor_get(x_142, 0);
lean_inc(x_144);
lean_dec(x_142);
x_145 = lean_mk_string_unchecked("quotedName", 10, 10);
x_146 = l_Lean_Name_mkStr4(x_116, x_117, x_118, x_145);
x_147 = lean_mk_string_unchecked("`", 1, 1);
x_148 = lean_mk_string_unchecked(".", 1, 1);
x_149 = l_String_intercalate(x_148, x_144);
lean_dec(x_148);
x_150 = lean_string_append(x_147, x_149);
lean_dec(x_149);
x_151 = lean_box(2);
x_152 = l_Lean_Syntax_mkNameLit(x_150, x_151);
x_153 = lean_mk_empty_array_with_capacity(x_111);
x_154 = lean_array_push(x_153, x_152);
x_155 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_155, 0, x_151);
lean_ctor_set(x_155, 1, x_146);
lean_ctor_set(x_155, 2, x_154);
x_136 = x_155;
goto block_141;
}
block_141:
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_inc(x_112);
x_137 = l_Lean_Syntax_node1(x_112, x_135, x_136);
x_138 = l_Lean_Syntax_node2(x_112, x_120, x_133, x_137);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_111);
if (lean_is_scalar(x_109)) {
 x_140 = lean_alloc_ctor(0, 2, 0);
} else {
 x_140 = x_109;
}
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_108);
return x_140;
}
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
lean_dec(x_30);
lean_free_object(x_14);
lean_dec(x_9);
lean_dec(x_8);
x_156 = lean_ctor_get(x_104, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_104, 1);
lean_inc(x_157);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_158 = x_104;
} else {
 lean_dec_ref(x_104);
 x_158 = lean_box(0);
}
if (lean_is_scalar(x_158)) {
 x_159 = lean_alloc_ctor(1, 2, 0);
} else {
 x_159 = x_158;
}
lean_ctor_set(x_159, 0, x_156);
lean_ctor_set(x_159, 1, x_157);
return x_159;
}
}
else
{
lean_object* x_160; 
lean_dec(x_30);
lean_free_object(x_14);
x_160 = l_Lean_Elab_Term_toParserDescr_ensureNoPrec(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_101);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_161 = lean_ctor_get(x_160, 1);
lean_inc(x_161);
lean_dec(x_160);
x_162 = lean_mk_empty_array_with_capacity(x_11);
x_163 = l_Lean_Elab_Term_toParserDescr_processAlias(x_12, x_162, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_161);
return x_163;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_164 = lean_ctor_get(x_160, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_160, 1);
lean_inc(x_165);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 x_166 = x_160;
} else {
 lean_dec_ref(x_160);
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
}
}
}
else
{
lean_object* x_168; lean_object* x_169; 
lean_free_object(x_14);
lean_dec(x_17);
lean_dec(x_12);
x_168 = lean_ctor_get(x_27, 0);
lean_inc(x_168);
lean_dec(x_27);
x_169 = l_Lean_Elab_Term_toParserDescr_ensureNoPrec(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (lean_obj_tag(x_169) == 0)
{
uint8_t x_170; 
x_170 = !lean_is_exclusive(x_169);
if (x_170 == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; uint8_t x_174; lean_object* x_175; lean_object* x_176; 
x_171 = lean_ctor_get(x_169, 0);
lean_dec(x_171);
x_172 = lean_unsigned_to_nat(1u);
x_173 = lean_box(0);
x_174 = lean_unbox(x_173);
x_175 = l_Lean_mkIdentFrom(x_1, x_168, x_174);
x_176 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_176, 0, x_175);
lean_ctor_set(x_176, 1, x_172);
lean_ctor_set(x_169, 0, x_176);
return x_169;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; uint8_t x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_177 = lean_ctor_get(x_169, 1);
lean_inc(x_177);
lean_dec(x_169);
x_178 = lean_unsigned_to_nat(1u);
x_179 = lean_box(0);
x_180 = lean_unbox(x_179);
x_181 = l_Lean_mkIdentFrom(x_1, x_168, x_180);
x_182 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_178);
x_183 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_177);
return x_183;
}
}
else
{
uint8_t x_184; 
lean_dec(x_168);
x_184 = !lean_is_exclusive(x_169);
if (x_184 == 0)
{
return x_169;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_185 = lean_ctor_get(x_169, 0);
x_186 = lean_ctor_get(x_169, 1);
lean_inc(x_186);
lean_inc(x_185);
lean_dec(x_169);
x_187 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_187, 0, x_185);
lean_ctor_set(x_187, 1, x_186);
return x_187;
}
}
}
}
default: 
{
lean_object* x_188; 
lean_free_object(x_14);
lean_dec(x_27);
lean_dec(x_17);
x_188 = l_Lean_Elab_Term_toParserDescr_ensureNoPrec(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_15);
if (lean_obj_tag(x_188) == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_189 = lean_ctor_get(x_188, 1);
lean_inc(x_189);
lean_dec(x_188);
x_190 = lean_mk_empty_array_with_capacity(x_11);
x_191 = l_Lean_Elab_Term_toParserDescr_processAlias(x_12, x_190, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_189);
return x_191;
}
else
{
uint8_t x_192; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_192 = !lean_is_exclusive(x_188);
if (x_192 == 0)
{
return x_188;
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_193 = lean_ctor_get(x_188, 0);
x_194 = lean_ctor_get(x_188, 1);
lean_inc(x_194);
lean_inc(x_193);
lean_dec(x_188);
x_195 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_195, 0, x_193);
lean_ctor_set(x_195, 1, x_194);
return x_195;
}
}
}
}
}
else
{
lean_object* x_196; 
x_196 = lean_ctor_get(x_14, 0);
lean_inc(x_196);
lean_dec(x_14);
switch (lean_obj_tag(x_196)) {
case 0:
{
lean_object* x_197; 
lean_dec(x_196);
lean_dec(x_17);
lean_dec(x_12);
x_197 = l_Lean_Elab_Term_toParserDescr_processParserCategory(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_15);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_197;
}
case 1:
{
uint8_t x_198; 
x_198 = lean_ctor_get_uint8(x_196, sizeof(void*)*1);
if (x_198 == 0)
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; uint8_t x_205; 
x_199 = lean_ctor_get(x_196, 0);
lean_inc(x_199);
lean_dec(x_196);
x_200 = l_Lean_Parser_getParserAliasInfo(x_17, x_15);
lean_dec(x_17);
x_201 = lean_ctor_get(x_200, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_200, 1);
lean_inc(x_202);
if (lean_is_exclusive(x_200)) {
 lean_ctor_release(x_200, 0);
 lean_ctor_release(x_200, 1);
 x_203 = x_200;
} else {
 lean_dec_ref(x_200);
 x_203 = lean_box(0);
}
x_204 = lean_ctor_get(x_201, 0);
lean_inc(x_204);
lean_dec(x_201);
x_205 = lean_name_eq(x_204, x_199);
lean_dec(x_204);
if (x_205 == 0)
{
lean_object* x_206; 
lean_dec(x_12);
x_206 = l_Lean_Elab_Term_toParserDescr_ensureNoPrec(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_202);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (lean_obj_tag(x_206) == 0)
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_245; 
x_207 = lean_ctor_get(x_206, 1);
lean_inc(x_207);
lean_dec(x_206);
x_208 = lean_st_ref_get(x_9, x_207);
lean_dec(x_9);
x_209 = lean_ctor_get(x_208, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_208, 1);
lean_inc(x_210);
if (lean_is_exclusive(x_208)) {
 lean_ctor_release(x_208, 0);
 lean_ctor_release(x_208, 1);
 x_211 = x_208;
} else {
 lean_dec_ref(x_208);
 x_211 = lean_box(0);
}
x_212 = lean_ctor_get(x_8, 5);
lean_inc(x_212);
x_213 = lean_unsigned_to_nat(1u);
x_214 = l_Lean_SourceInfo_fromRef(x_212, x_198);
lean_dec(x_212);
x_215 = lean_ctor_get(x_8, 10);
lean_inc(x_215);
lean_dec(x_8);
x_216 = lean_ctor_get(x_209, 0);
lean_inc(x_216);
lean_dec(x_209);
x_217 = l_Lean_Environment_mainModule(x_216);
lean_dec(x_216);
x_218 = lean_mk_string_unchecked("Lean", 4, 4);
x_219 = lean_mk_string_unchecked("Parser", 6, 6);
x_220 = lean_mk_string_unchecked("Term", 4, 4);
x_221 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_220);
lean_inc(x_219);
lean_inc(x_218);
x_222 = l_Lean_Name_mkStr4(x_218, x_219, x_220, x_221);
x_223 = lean_mk_string_unchecked("ParserDescr.parser", 18, 18);
x_224 = l_String_toSubstring_x27(x_223);
x_225 = lean_mk_string_unchecked("ParserDescr", 11, 11);
x_226 = lean_mk_string_unchecked("parser", 6, 6);
lean_inc(x_226);
lean_inc(x_225);
x_227 = l_Lean_Name_mkStr2(x_225, x_226);
x_228 = l_Lean_addMacroScope(x_217, x_227, x_215);
lean_inc(x_218);
x_229 = l_Lean_Name_mkStr3(x_218, x_225, x_226);
x_230 = lean_box(0);
lean_inc(x_229);
if (lean_is_scalar(x_203)) {
 x_231 = lean_alloc_ctor(1, 2, 0);
} else {
 x_231 = x_203;
 lean_ctor_set_tag(x_231, 1);
}
lean_ctor_set(x_231, 0, x_229);
lean_ctor_set(x_231, 1, x_230);
x_232 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_232, 0, x_229);
x_233 = lean_box(0);
x_234 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_234, 0, x_232);
lean_ctor_set(x_234, 1, x_233);
x_235 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_235, 0, x_231);
lean_ctor_set(x_235, 1, x_234);
lean_inc(x_214);
x_236 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_236, 0, x_214);
lean_ctor_set(x_236, 1, x_224);
lean_ctor_set(x_236, 2, x_228);
lean_ctor_set(x_236, 3, x_235);
x_237 = lean_mk_string_unchecked("null", 4, 4);
x_238 = l_Lean_Name_mkStr1(x_237);
lean_inc(x_199);
x_245 = l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(x_230, x_199);
if (lean_obj_tag(x_245) == 0)
{
lean_object* x_246; 
lean_dec(x_220);
lean_dec(x_219);
lean_dec(x_218);
x_246 = l_Lean_quoteNameMk(x_199);
x_239 = x_246;
goto block_244;
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
lean_dec(x_199);
x_247 = lean_ctor_get(x_245, 0);
lean_inc(x_247);
lean_dec(x_245);
x_248 = lean_mk_string_unchecked("quotedName", 10, 10);
x_249 = l_Lean_Name_mkStr4(x_218, x_219, x_220, x_248);
x_250 = lean_mk_string_unchecked("`", 1, 1);
x_251 = lean_mk_string_unchecked(".", 1, 1);
x_252 = l_String_intercalate(x_251, x_247);
lean_dec(x_251);
x_253 = lean_string_append(x_250, x_252);
lean_dec(x_252);
x_254 = lean_box(2);
x_255 = l_Lean_Syntax_mkNameLit(x_253, x_254);
x_256 = lean_mk_empty_array_with_capacity(x_213);
x_257 = lean_array_push(x_256, x_255);
x_258 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_258, 0, x_254);
lean_ctor_set(x_258, 1, x_249);
lean_ctor_set(x_258, 2, x_257);
x_239 = x_258;
goto block_244;
}
block_244:
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
lean_inc(x_214);
x_240 = l_Lean_Syntax_node1(x_214, x_238, x_239);
x_241 = l_Lean_Syntax_node2(x_214, x_222, x_236, x_240);
x_242 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_242, 0, x_241);
lean_ctor_set(x_242, 1, x_213);
if (lean_is_scalar(x_211)) {
 x_243 = lean_alloc_ctor(0, 2, 0);
} else {
 x_243 = x_211;
}
lean_ctor_set(x_243, 0, x_242);
lean_ctor_set(x_243, 1, x_210);
return x_243;
}
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; 
lean_dec(x_203);
lean_dec(x_199);
lean_dec(x_9);
lean_dec(x_8);
x_259 = lean_ctor_get(x_206, 0);
lean_inc(x_259);
x_260 = lean_ctor_get(x_206, 1);
lean_inc(x_260);
if (lean_is_exclusive(x_206)) {
 lean_ctor_release(x_206, 0);
 lean_ctor_release(x_206, 1);
 x_261 = x_206;
} else {
 lean_dec_ref(x_206);
 x_261 = lean_box(0);
}
if (lean_is_scalar(x_261)) {
 x_262 = lean_alloc_ctor(1, 2, 0);
} else {
 x_262 = x_261;
}
lean_ctor_set(x_262, 0, x_259);
lean_ctor_set(x_262, 1, x_260);
return x_262;
}
}
else
{
lean_object* x_263; 
lean_dec(x_203);
lean_dec(x_199);
x_263 = l_Lean_Elab_Term_toParserDescr_ensureNoPrec(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_202);
if (lean_obj_tag(x_263) == 0)
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_264 = lean_ctor_get(x_263, 1);
lean_inc(x_264);
lean_dec(x_263);
x_265 = lean_mk_empty_array_with_capacity(x_11);
x_266 = l_Lean_Elab_Term_toParserDescr_processAlias(x_12, x_265, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_264);
return x_266;
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_267 = lean_ctor_get(x_263, 0);
lean_inc(x_267);
x_268 = lean_ctor_get(x_263, 1);
lean_inc(x_268);
if (lean_is_exclusive(x_263)) {
 lean_ctor_release(x_263, 0);
 lean_ctor_release(x_263, 1);
 x_269 = x_263;
} else {
 lean_dec_ref(x_263);
 x_269 = lean_box(0);
}
if (lean_is_scalar(x_269)) {
 x_270 = lean_alloc_ctor(1, 2, 0);
} else {
 x_270 = x_269;
}
lean_ctor_set(x_270, 0, x_267);
lean_ctor_set(x_270, 1, x_268);
return x_270;
}
}
}
else
{
lean_object* x_271; lean_object* x_272; 
lean_dec(x_17);
lean_dec(x_12);
x_271 = lean_ctor_get(x_196, 0);
lean_inc(x_271);
lean_dec(x_196);
x_272 = l_Lean_Elab_Term_toParserDescr_ensureNoPrec(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (lean_obj_tag(x_272) == 0)
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; uint8_t x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; 
x_273 = lean_ctor_get(x_272, 1);
lean_inc(x_273);
if (lean_is_exclusive(x_272)) {
 lean_ctor_release(x_272, 0);
 lean_ctor_release(x_272, 1);
 x_274 = x_272;
} else {
 lean_dec_ref(x_272);
 x_274 = lean_box(0);
}
x_275 = lean_unsigned_to_nat(1u);
x_276 = lean_box(0);
x_277 = lean_unbox(x_276);
x_278 = l_Lean_mkIdentFrom(x_1, x_271, x_277);
x_279 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_279, 0, x_278);
lean_ctor_set(x_279, 1, x_275);
if (lean_is_scalar(x_274)) {
 x_280 = lean_alloc_ctor(0, 2, 0);
} else {
 x_280 = x_274;
}
lean_ctor_set(x_280, 0, x_279);
lean_ctor_set(x_280, 1, x_273);
return x_280;
}
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; 
lean_dec(x_271);
x_281 = lean_ctor_get(x_272, 0);
lean_inc(x_281);
x_282 = lean_ctor_get(x_272, 1);
lean_inc(x_282);
if (lean_is_exclusive(x_272)) {
 lean_ctor_release(x_272, 0);
 lean_ctor_release(x_272, 1);
 x_283 = x_272;
} else {
 lean_dec_ref(x_272);
 x_283 = lean_box(0);
}
if (lean_is_scalar(x_283)) {
 x_284 = lean_alloc_ctor(1, 2, 0);
} else {
 x_284 = x_283;
}
lean_ctor_set(x_284, 0, x_281);
lean_ctor_set(x_284, 1, x_282);
return x_284;
}
}
}
default: 
{
lean_object* x_285; 
lean_dec(x_196);
lean_dec(x_17);
x_285 = l_Lean_Elab_Term_toParserDescr_ensureNoPrec(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_15);
if (lean_obj_tag(x_285) == 0)
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; 
x_286 = lean_ctor_get(x_285, 1);
lean_inc(x_286);
lean_dec(x_285);
x_287 = lean_mk_empty_array_with_capacity(x_11);
x_288 = l_Lean_Elab_Term_toParserDescr_processAlias(x_12, x_287, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_286);
return x_288;
}
else
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_289 = lean_ctor_get(x_285, 0);
lean_inc(x_289);
x_290 = lean_ctor_get(x_285, 1);
lean_inc(x_290);
if (lean_is_exclusive(x_285)) {
 lean_ctor_release(x_285, 0);
 lean_ctor_release(x_285, 1);
 x_291 = x_285;
} else {
 lean_dec_ref(x_285);
 x_291 = lean_box(0);
}
if (lean_is_scalar(x_291)) {
 x_292 = lean_alloc_ctor(1, 2, 0);
} else {
 x_292 = x_291;
}
lean_ctor_set(x_292, 0, x_289);
lean_ctor_set(x_292, 1, x_290);
return x_292;
}
}
}
}
}
}
else
{
uint8_t x_293; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_293 = !lean_is_exclusive(x_13);
if (x_293 == 0)
{
return x_13;
}
else
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; 
x_294 = lean_ctor_get(x_13, 0);
x_295 = lean_ctor_get(x_13, 1);
lean_inc(x_295);
lean_inc(x_294);
lean_dec(x_13);
x_296 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_296, 0, x_294);
lean_ctor_set(x_296, 1, x_295);
return x_296;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Lean_Elab_Term_toParserDescr_processSeq_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_eq(x_2, x_14);
if (x_15 == 1)
{
lean_object* x_16; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_4);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_36; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_2, x_17);
lean_dec(x_2);
x_19 = lean_array_fget(x_1, x_3);
x_20 = lean_ctor_get(x_5, 0);
x_36 = lean_ctor_get_uint8(x_5, sizeof(void*)*1);
if (x_36 == 0)
{
x_21 = x_36;
goto block_35;
}
else
{
uint8_t x_37; 
x_37 = lean_nat_dec_eq(x_3, x_14);
x_21 = x_37;
goto block_35;
}
block_35:
{
uint8_t x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 1);
x_23 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 2);
lean_inc(x_20);
x_24 = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set_uint8(x_24, sizeof(void*)*1, x_21);
lean_ctor_set_uint8(x_24, sizeof(void*)*1 + 1, x_22);
lean_ctor_set_uint8(x_24, sizeof(void*)*1 + 2, x_23);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_25 = l_Lean_Elab_Term_toParserDescr_process(x_19, x_24, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_nat_add(x_3, x_17);
lean_dec(x_3);
x_29 = lean_array_push(x_4, x_26);
x_2 = x_18;
x_3 = x_28;
x_4 = x_29;
x_13 = x_27;
goto _start;
}
else
{
uint8_t x_31; 
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_31 = !lean_is_exclusive(x_25);
if (x_31 == 0)
{
return x_25;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_25, 0);
x_33 = lean_ctor_get(x_25, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_25);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Lean_Elab_Term_toParserDescr_processSeq_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Array_mapFinIdxM_map___at___Lean_Elab_Term_toParserDescr_processSeq_spec__0___redArg(x_1, x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr_processSeq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_13 = l_Lean_Elab_Term_checkLeftRec(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_38; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Syntax_getArgs(x_1);
x_38 = lean_unbox(x_14);
lean_dec(x_14);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_array_get_size(x_16);
x_40 = lean_mk_empty_array_with_capacity(x_39);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_41 = l_Array_mapFinIdxM_map___at___Lean_Elab_Term_toParserDescr_processSeq_spec__0___redArg(x_16, x_39, x_11, x_40, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_15);
lean_dec(x_16);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq(x_42, x_4, x_5, x_6, x_7, x_8, x_9, x_43);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_44;
}
else
{
uint8_t x_45; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_45 = !lean_is_exclusive(x_41);
if (x_45 == 0)
{
return x_41;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_41, 0);
x_47 = lean_ctor_get(x_41, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_41);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_49 = lean_array_get_size(x_16);
x_50 = lean_unsigned_to_nat(1u);
x_51 = lean_nat_dec_eq(x_49, x_50);
lean_dec(x_49);
if (x_51 == 0)
{
x_17 = x_2;
x_18 = x_3;
x_19 = x_4;
x_20 = x_5;
x_21 = x_6;
x_22 = x_7;
x_23 = x_8;
x_24 = x_9;
x_25 = x_15;
goto block_37;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
lean_dec(x_16);
x_52 = lean_mk_string_unchecked("invalid atomic left recursive syntax", 36, 36);
x_53 = l_Lean_stringToMessageData(x_52);
lean_dec(x_52);
x_54 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Term_checkLeftRec_spec__0_spec__3___redArg(x_1, x_53, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
}
block_37:
{
lean_object* x_26; size_t x_27; size_t x_28; lean_object* x_29; 
x_26 = l_Array_eraseIdxIfInBounds___redArg(x_16, x_11);
x_27 = lean_array_size(x_26);
x_28 = lean_usize_of_nat(x_11);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
x_29 = l_Array_mapMUnsafe_map___at___Lean_Elab_Term_toParserDescr_processAlias_spec__4(x_27, x_28, x_26, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_25);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Term_mkParserSeq(x_30, x_19, x_20, x_21, x_22, x_23, x_24, x_31);
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
return x_32;
}
else
{
uint8_t x_33; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
x_33 = !lean_is_exclusive(x_29);
if (x_33 == 0)
{
return x_29;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_29, 0);
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_29);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
else
{
uint8_t x_59; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr_processSepBy1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Term_toParserDescr_processSepBy1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr_processSepBy___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Term_toParserDescr_processSepBy(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Elab_Term_toParserDescr_processAlias_spec__0___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_panic___at___Lean_Elab_Term_toParserDescr_processAlias_spec__0___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Elab_Term_toParserDescr_processAlias_spec__0___lam__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_panic___at___Lean_Elab_Term_toParserDescr_processAlias_spec__0___lam__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Term_toParserDescr_processAlias_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_Term_toParserDescr_processAlias_spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_toParserDescr_processAlias_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lean_Elab_Term_toParserDescr_processAlias_spec__2(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_toParserDescr_processAlias_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lean_Elab_Term_toParserDescr_processAlias_spec__3(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_toParserDescr_processAlias_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_14 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_15 = l_Array_mapMUnsafe_map___at___Lean_Elab_Term_toParserDescr_processAlias_spec__4(x_13, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_toParserDescr_processAlias_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = l_Array_mapMUnsafe_map___at___Lean_Elab_Term_toParserDescr_processAlias_spec__5___redArg(x_7, x_8, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_toParserDescr_processAlias_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_14 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_15 = l_Array_mapMUnsafe_map___at___Lean_Elab_Term_toParserDescr_processAlias_spec__5(x_13, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr_processNullaryOrCat___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Term_toParserDescr_processNullaryOrCat(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Lean_Elab_Term_toParserDescr_processSeq_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Array_mapFinIdxM_map___at___Lean_Elab_Term_toParserDescr_processSeq_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_5);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Lean_Elab_Term_toParserDescr_processSeq_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Array_mapFinIdxM_map___at___Lean_Elab_Term_toParserDescr_processSeq_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_6);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr_processSeq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Term_toParserDescr_processSeq(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_toParserDescr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_22; lean_object* x_23; 
x_10 = lean_st_ref_get(x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_box(0);
x_14 = lean_st_mk_ref(x_13, x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_11, 0);
lean_inc(x_17);
lean_dec(x_11);
x_18 = l_Lean_Parser_leadingIdentBehavior(x_17, x_2);
x_19 = lean_box(1);
x_20 = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(x_20, 0, x_2);
x_21 = lean_unbox(x_19);
lean_ctor_set_uint8(x_20, sizeof(void*)*1, x_21);
x_22 = lean_unbox(x_19);
lean_ctor_set_uint8(x_20, sizeof(void*)*1 + 1, x_22);
lean_ctor_set_uint8(x_20, sizeof(void*)*1 + 2, x_18);
lean_inc(x_15);
x_23 = l_Lean_Elab_Term_toParserDescr_process(x_1, x_20, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_16);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_st_ref_get(x_15, x_25);
lean_dec(x_15);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_24);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_26, 0);
x_30 = lean_ctor_get(x_24, 1);
lean_dec(x_30);
lean_ctor_set(x_24, 1, x_29);
lean_ctor_set(x_26, 0, x_24);
return x_26;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_26, 0);
x_32 = lean_ctor_get(x_24, 0);
lean_inc(x_32);
lean_dec(x_24);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
lean_ctor_set(x_26, 0, x_33);
return x_26;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_ctor_get(x_26, 0);
x_35 = lean_ctor_get(x_26, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_26);
x_36 = lean_ctor_get(x_24, 0);
lean_inc(x_36);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_37 = x_24;
} else {
 lean_dec_ref(x_24);
 x_37 = lean_box(0);
}
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_37;
}
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_34);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_35);
return x_39;
}
}
else
{
uint8_t x_40; 
lean_dec(x_15);
x_40 = !lean_is_exclusive(x_23);
if (x_40 == 0)
{
return x_23;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_23, 0);
x_42 = lean_ctor_get(x_23, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_23);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = l_Lean_Elab_Command_getRef(x_2, x_3, x_4);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
x_10 = l_Lean_Elab_Command_getCurrMacroScope(x_2, x_3, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_14 = l_Lean_Elab_Command_getMainModule___redArg(x_3, x_13);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_174; lean_object* x_228; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
x_18 = lean_mk_string_unchecked("`(", 2, 2);
x_19 = lean_mk_string_unchecked("quot", 4, 4);
x_20 = lean_string_append(x_18, x_5);
lean_dec(x_5);
x_21 = lean_mk_string_unchecked("| ", 2, 2);
x_22 = l_Lean_Name_mkStr1(x_19);
x_23 = lean_box(0);
x_24 = lean_string_append(x_20, x_21);
lean_dec(x_21);
lean_inc(x_1);
x_25 = l_Lean_Name_append(x_1, x_22);
x_26 = lean_unbox(x_23);
x_27 = l_Lean_SourceInfo_fromRef(x_8, x_26);
lean_dec(x_8);
x_28 = lean_mk_string_unchecked("Lean", 4, 4);
x_29 = lean_mk_string_unchecked("Parser", 6, 6);
x_30 = lean_mk_string_unchecked("Command", 7, 7);
x_31 = lean_mk_string_unchecked("declaration", 11, 11);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
x_32 = l_Lean_Name_mkStr4(x_28, x_29, x_30, x_31);
x_33 = lean_mk_string_unchecked("declModifiers", 13, 13);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
x_34 = l_Lean_Name_mkStr4(x_28, x_29, x_30, x_33);
x_35 = lean_mk_string_unchecked("null", 4, 4);
x_36 = l_Lean_Name_mkStr1(x_35);
x_37 = l_Array_mkArray0(lean_box(0));
lean_inc(x_36);
lean_inc(x_27);
x_38 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_38, 0, x_27);
lean_ctor_set(x_38, 1, x_36);
lean_ctor_set(x_38, 2, x_37);
x_39 = lean_mk_string_unchecked("Term", 4, 4);
x_40 = lean_mk_string_unchecked("attributes", 10, 10);
lean_inc(x_39);
lean_inc(x_29);
lean_inc(x_28);
x_41 = l_Lean_Name_mkStr4(x_28, x_29, x_39, x_40);
x_42 = lean_mk_string_unchecked("@[", 2, 2);
lean_inc(x_27);
lean_ctor_set_tag(x_14, 2);
lean_ctor_set(x_14, 1, x_42);
lean_ctor_set(x_14, 0, x_27);
x_43 = lean_mk_string_unchecked("attrInstance", 12, 12);
lean_inc(x_39);
lean_inc(x_29);
lean_inc(x_28);
x_44 = l_Lean_Name_mkStr4(x_28, x_29, x_39, x_43);
x_45 = lean_mk_string_unchecked("attrKind", 8, 8);
lean_inc(x_39);
lean_inc(x_29);
lean_inc(x_28);
x_46 = l_Lean_Name_mkStr4(x_28, x_29, x_39, x_45);
lean_inc(x_38);
lean_inc(x_27);
x_47 = l_Lean_Syntax_node1(x_27, x_46, x_38);
x_48 = lean_mk_string_unchecked("Attr", 4, 4);
x_49 = lean_mk_string_unchecked("simple", 6, 6);
lean_inc(x_29);
lean_inc(x_28);
x_50 = l_Lean_Name_mkStr4(x_28, x_29, x_48, x_49);
x_51 = lean_mk_string_unchecked("term_parser", 11, 11);
lean_inc(x_51);
x_52 = l_String_toSubstring_x27(x_51);
x_53 = l_Lean_Name_mkStr1(x_51);
lean_inc(x_12);
lean_inc(x_16);
x_54 = l_Lean_addMacroScope(x_16, x_53, x_12);
x_55 = lean_box(0);
lean_inc(x_27);
x_56 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_56, 0, x_27);
lean_ctor_set(x_56, 1, x_52);
lean_ctor_set(x_56, 2, x_54);
lean_ctor_set(x_56, 3, x_55);
lean_inc(x_38);
lean_inc(x_27);
x_57 = l_Lean_Syntax_node2(x_27, x_50, x_56, x_38);
lean_inc(x_27);
x_58 = l_Lean_Syntax_node2(x_27, x_44, x_47, x_57);
lean_inc(x_36);
lean_inc(x_27);
x_59 = l_Lean_Syntax_node1(x_27, x_36, x_58);
x_60 = lean_mk_string_unchecked("]", 1, 1);
lean_inc(x_27);
lean_ctor_set_tag(x_10, 2);
lean_ctor_set(x_10, 1, x_60);
lean_ctor_set(x_10, 0, x_27);
lean_inc(x_27);
x_61 = l_Lean_Syntax_node3(x_27, x_41, x_14, x_59, x_10);
lean_inc(x_36);
lean_inc(x_27);
x_62 = l_Lean_Syntax_node1(x_27, x_36, x_61);
lean_inc_n(x_38, 5);
lean_inc(x_27);
x_63 = l_Lean_Syntax_node6(x_27, x_34, x_38, x_62, x_38, x_38, x_38, x_38);
x_64 = lean_mk_string_unchecked("definition", 10, 10);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
x_65 = l_Lean_Name_mkStr4(x_28, x_29, x_30, x_64);
x_66 = lean_mk_string_unchecked("def", 3, 3);
lean_inc(x_27);
lean_ctor_set_tag(x_6, 2);
lean_ctor_set(x_6, 1, x_66);
lean_ctor_set(x_6, 0, x_27);
x_67 = lean_mk_string_unchecked("declId", 6, 6);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
x_68 = l_Lean_Name_mkStr4(x_28, x_29, x_30, x_67);
lean_inc(x_25);
x_69 = lean_mk_syntax_ident(x_25);
x_70 = lean_unsigned_to_nat(0u);
x_71 = lean_mk_empty_array_with_capacity(x_70);
x_72 = lean_box(2);
lean_inc(x_36);
x_73 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_36);
lean_ctor_set(x_73, 2, x_71);
x_74 = lean_unsigned_to_nat(2u);
x_75 = lean_mk_empty_array_with_capacity(x_74);
x_76 = lean_array_push(x_75, x_69);
x_77 = lean_array_push(x_76, x_73);
x_78 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_78, 0, x_72);
lean_ctor_set(x_78, 1, x_68);
lean_ctor_set(x_78, 2, x_77);
x_79 = lean_mk_string_unchecked("optDeclSig", 10, 10);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
x_80 = l_Lean_Name_mkStr4(x_28, x_29, x_30, x_79);
x_81 = lean_mk_string_unchecked("typeSpec", 8, 8);
lean_inc(x_39);
lean_inc(x_29);
lean_inc(x_28);
x_82 = l_Lean_Name_mkStr4(x_28, x_29, x_39, x_81);
x_83 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_27);
x_84 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_84, 0, x_27);
lean_ctor_set(x_84, 1, x_83);
x_85 = lean_mk_string_unchecked("Lean.ParserDescr", 16, 16);
x_86 = l_String_toSubstring_x27(x_85);
x_87 = lean_mk_string_unchecked("ParserDescr", 11, 11);
lean_inc(x_87);
lean_inc(x_28);
x_88 = l_Lean_Name_mkStr2(x_28, x_87);
lean_inc(x_12);
lean_inc(x_88);
lean_inc(x_16);
x_89 = l_Lean_addMacroScope(x_16, x_88, x_12);
x_90 = lean_box(0);
lean_inc(x_88);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_88);
lean_ctor_set(x_91, 1, x_90);
x_92 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_92, 0, x_88);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_55);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_91);
lean_ctor_set(x_94, 1, x_93);
lean_inc(x_27);
x_95 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_95, 0, x_27);
lean_ctor_set(x_95, 1, x_86);
lean_ctor_set(x_95, 2, x_89);
lean_ctor_set(x_95, 3, x_94);
lean_inc(x_27);
x_96 = l_Lean_Syntax_node2(x_27, x_82, x_84, x_95);
lean_inc(x_36);
lean_inc(x_27);
x_97 = l_Lean_Syntax_node1(x_27, x_36, x_96);
lean_inc(x_38);
lean_inc(x_27);
x_98 = l_Lean_Syntax_node2(x_27, x_80, x_38, x_97);
x_99 = lean_mk_string_unchecked("declValSimple", 13, 13);
lean_inc(x_29);
lean_inc(x_28);
x_100 = l_Lean_Name_mkStr4(x_28, x_29, x_30, x_99);
x_101 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_27);
x_102 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_102, 0, x_27);
lean_ctor_set(x_102, 1, x_101);
x_103 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_39);
lean_inc(x_29);
lean_inc(x_28);
x_104 = l_Lean_Name_mkStr4(x_28, x_29, x_39, x_103);
x_105 = lean_mk_string_unchecked("Lean.ParserDescr.node", 21, 21);
x_106 = l_String_toSubstring_x27(x_105);
x_107 = lean_mk_string_unchecked("node", 4, 4);
lean_inc(x_87);
lean_inc(x_28);
x_108 = l_Lean_Name_mkStr3(x_28, x_87, x_107);
lean_inc(x_12);
lean_inc(x_108);
lean_inc(x_16);
x_109 = l_Lean_addMacroScope(x_16, x_108, x_12);
lean_inc(x_108);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_90);
x_111 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_111, 0, x_108);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_55);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_110);
lean_ctor_set(x_113, 1, x_112);
lean_inc(x_27);
x_114 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_114, 0, x_27);
lean_ctor_set(x_114, 1, x_106);
lean_ctor_set(x_114, 2, x_109);
lean_ctor_set(x_114, 3, x_113);
x_115 = lean_mk_string_unchecked("quotedName", 10, 10);
lean_inc(x_39);
lean_inc(x_29);
lean_inc(x_28);
x_116 = l_Lean_Name_mkStr4(x_28, x_29, x_39, x_115);
x_117 = lean_mk_string_unchecked("name", 4, 4);
x_118 = l_Lean_Name_mkStr1(x_117);
x_119 = lean_mk_string_unchecked("`Lean.Parser.Term.quot", 22, 22);
lean_inc(x_27);
x_120 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_120, 0, x_27);
lean_ctor_set(x_120, 1, x_119);
lean_inc(x_118);
lean_inc(x_27);
x_121 = l_Lean_Syntax_node1(x_27, x_118, x_120);
lean_inc(x_116);
lean_inc(x_27);
x_122 = l_Lean_Syntax_node1(x_27, x_116, x_121);
x_123 = lean_unsigned_to_nat(1024u);
x_124 = l___private_Init_Data_Repr_0__Nat_reprFast(x_123);
x_125 = l_Lean_Syntax_mkNumLit(x_124, x_72);
x_126 = lean_mk_string_unchecked("paren", 5, 5);
lean_inc(x_29);
lean_inc(x_28);
x_127 = l_Lean_Name_mkStr4(x_28, x_29, x_39, x_126);
x_128 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_27);
x_129 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_129, 0, x_27);
lean_ctor_set(x_129, 1, x_128);
lean_inc(x_25);
x_228 = l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(x_90, x_25);
if (lean_obj_tag(x_228) == 0)
{
lean_object* x_229; 
x_229 = l_Lean_quoteNameMk(x_25);
x_174 = x_229;
goto block_227;
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
lean_dec(x_25);
x_230 = lean_ctor_get(x_228, 0);
lean_inc(x_230);
lean_dec(x_228);
x_231 = lean_mk_string_unchecked("`", 1, 1);
x_232 = lean_mk_string_unchecked(".", 1, 1);
x_233 = l_String_intercalate(x_232, x_230);
lean_dec(x_232);
x_234 = lean_string_append(x_231, x_233);
lean_dec(x_233);
x_235 = l_Lean_Syntax_mkNameLit(x_234, x_72);
x_236 = lean_unsigned_to_nat(1u);
x_237 = lean_mk_empty_array_with_capacity(x_236);
x_238 = lean_array_push(x_237, x_235);
lean_inc(x_116);
x_239 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_239, 0, x_72);
lean_ctor_set(x_239, 1, x_116);
lean_ctor_set(x_239, 2, x_238);
x_174 = x_239;
goto block_227;
}
block_173:
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_138 = lean_mk_string_unchecked("num", 3, 3);
x_139 = l_Lean_Name_mkStr1(x_138);
x_140 = lean_mk_string_unchecked("0", 1, 1);
lean_inc(x_27);
x_141 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_141, 0, x_27);
lean_ctor_set(x_141, 1, x_140);
lean_inc(x_27);
x_142 = l_Lean_Syntax_node1(x_27, x_139, x_141);
lean_inc(x_36);
lean_inc(x_27);
x_143 = l_Lean_Syntax_node2(x_27, x_36, x_137, x_142);
lean_inc(x_104);
lean_inc(x_27);
x_144 = l_Lean_Syntax_node2(x_27, x_104, x_134, x_143);
lean_inc(x_135);
lean_inc(x_129);
lean_inc(x_127);
lean_inc(x_27);
x_145 = l_Lean_Syntax_node3(x_27, x_127, x_129, x_144, x_135);
x_146 = lean_mk_string_unchecked("str", 3, 3);
x_147 = l_Lean_Name_mkStr1(x_146);
x_148 = lean_mk_string_unchecked("\")\"", 3, 3);
lean_inc(x_27);
x_149 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_149, 0, x_27);
lean_ctor_set(x_149, 1, x_148);
lean_inc(x_27);
x_150 = l_Lean_Syntax_node1(x_27, x_147, x_149);
lean_inc(x_36);
lean_inc(x_27);
x_151 = l_Lean_Syntax_node1(x_27, x_36, x_150);
lean_inc(x_104);
lean_inc(x_27);
x_152 = l_Lean_Syntax_node2(x_27, x_104, x_136, x_151);
lean_inc(x_135);
lean_inc(x_129);
lean_inc(x_127);
lean_inc(x_27);
x_153 = l_Lean_Syntax_node3(x_27, x_127, x_129, x_152, x_135);
lean_inc(x_133);
lean_inc(x_36);
lean_inc(x_27);
x_154 = l_Lean_Syntax_node3(x_27, x_36, x_133, x_145, x_153);
lean_inc(x_132);
lean_inc(x_104);
lean_inc(x_27);
x_155 = l_Lean_Syntax_node2(x_27, x_104, x_132, x_154);
lean_inc(x_135);
lean_inc(x_129);
lean_inc(x_127);
lean_inc(x_27);
x_156 = l_Lean_Syntax_node3(x_27, x_127, x_129, x_155, x_135);
lean_inc(x_36);
lean_inc(x_27);
x_157 = l_Lean_Syntax_node3(x_27, x_36, x_133, x_131, x_156);
lean_inc(x_104);
lean_inc(x_27);
x_158 = l_Lean_Syntax_node2(x_27, x_104, x_132, x_157);
lean_inc(x_135);
lean_inc(x_129);
lean_inc(x_127);
lean_inc(x_27);
x_159 = l_Lean_Syntax_node3(x_27, x_127, x_129, x_158, x_135);
lean_inc(x_125);
lean_inc(x_36);
lean_inc(x_27);
x_160 = l_Lean_Syntax_node3(x_27, x_36, x_130, x_125, x_159);
lean_inc(x_114);
lean_inc(x_104);
lean_inc(x_27);
x_161 = l_Lean_Syntax_node2(x_27, x_104, x_114, x_160);
lean_inc(x_27);
x_162 = l_Lean_Syntax_node3(x_27, x_127, x_129, x_161, x_135);
lean_inc(x_27);
x_163 = l_Lean_Syntax_node3(x_27, x_36, x_122, x_125, x_162);
lean_inc(x_27);
x_164 = l_Lean_Syntax_node2(x_27, x_104, x_114, x_163);
x_165 = lean_mk_string_unchecked("Termination", 11, 11);
x_166 = lean_mk_string_unchecked("suffix", 6, 6);
x_167 = l_Lean_Name_mkStr4(x_28, x_29, x_165, x_166);
lean_inc_n(x_38, 2);
lean_inc(x_27);
x_168 = l_Lean_Syntax_node2(x_27, x_167, x_38, x_38);
lean_inc(x_38);
lean_inc(x_27);
x_169 = l_Lean_Syntax_node4(x_27, x_100, x_102, x_164, x_168, x_38);
lean_inc(x_27);
x_170 = l_Lean_Syntax_node5(x_27, x_65, x_6, x_78, x_98, x_169, x_38);
x_171 = l_Lean_Syntax_node2(x_27, x_32, x_63, x_170);
x_172 = l_Lean_Elab_Command_elabCommand(x_171, x_2, x_3, x_17);
return x_172;
}
block_227:
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_175 = lean_mk_string_unchecked("Lean.ParserDescr.binary", 23, 23);
x_176 = l_String_toSubstring_x27(x_175);
x_177 = lean_mk_string_unchecked("binary", 6, 6);
lean_inc(x_87);
lean_inc(x_28);
x_178 = l_Lean_Name_mkStr3(x_28, x_87, x_177);
lean_inc(x_12);
lean_inc(x_178);
lean_inc(x_16);
x_179 = l_Lean_addMacroScope(x_16, x_178, x_12);
lean_inc(x_178);
x_180 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_180, 0, x_178);
lean_ctor_set(x_180, 1, x_90);
x_181 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_181, 0, x_178);
x_182 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_55);
x_183 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_183, 0, x_180);
lean_ctor_set(x_183, 1, x_182);
lean_inc(x_27);
x_184 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_184, 0, x_27);
lean_ctor_set(x_184, 1, x_176);
lean_ctor_set(x_184, 2, x_179);
lean_ctor_set(x_184, 3, x_183);
x_185 = lean_mk_string_unchecked("`andthen", 8, 8);
lean_inc(x_27);
x_186 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_186, 0, x_27);
lean_ctor_set(x_186, 1, x_185);
lean_inc(x_27);
x_187 = l_Lean_Syntax_node1(x_27, x_118, x_186);
lean_inc(x_116);
lean_inc(x_27);
x_188 = l_Lean_Syntax_node1(x_27, x_116, x_187);
x_189 = lean_mk_string_unchecked("Lean.ParserDescr.symbol", 23, 23);
x_190 = l_String_toSubstring_x27(x_189);
x_191 = lean_mk_string_unchecked("symbol", 6, 6);
lean_inc(x_87);
lean_inc(x_28);
x_192 = l_Lean_Name_mkStr3(x_28, x_87, x_191);
lean_inc(x_12);
lean_inc(x_192);
lean_inc(x_16);
x_193 = l_Lean_addMacroScope(x_16, x_192, x_12);
lean_inc(x_192);
x_194 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_194, 0, x_192);
lean_ctor_set(x_194, 1, x_90);
x_195 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_195, 0, x_192);
x_196 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_55);
x_197 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_197, 0, x_194);
lean_ctor_set(x_197, 1, x_196);
lean_inc(x_27);
x_198 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_198, 0, x_27);
lean_ctor_set(x_198, 1, x_190);
lean_ctor_set(x_198, 2, x_193);
lean_ctor_set(x_198, 3, x_197);
x_199 = l_Lean_Syntax_mkStrLit(x_24, x_72);
lean_dec(x_24);
lean_inc(x_36);
lean_inc(x_27);
x_200 = l_Lean_Syntax_node1(x_27, x_36, x_199);
lean_inc(x_198);
lean_inc(x_104);
lean_inc(x_27);
x_201 = l_Lean_Syntax_node2(x_27, x_104, x_198, x_200);
x_202 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_27);
x_203 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_203, 0, x_27);
lean_ctor_set(x_203, 1, x_202);
lean_inc(x_203);
lean_inc(x_129);
lean_inc(x_127);
lean_inc(x_27);
x_204 = l_Lean_Syntax_node3(x_27, x_127, x_129, x_201, x_203);
x_205 = lean_mk_string_unchecked("Lean.ParserDescr.cat", 20, 20);
x_206 = l_String_toSubstring_x27(x_205);
x_207 = lean_mk_string_unchecked("cat", 3, 3);
lean_inc(x_28);
x_208 = l_Lean_Name_mkStr3(x_28, x_87, x_207);
lean_inc(x_208);
x_209 = l_Lean_addMacroScope(x_16, x_208, x_12);
lean_inc(x_208);
x_210 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_210, 0, x_208);
lean_ctor_set(x_210, 1, x_90);
x_211 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_211, 0, x_208);
x_212 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_212, 0, x_211);
lean_ctor_set(x_212, 1, x_55);
x_213 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_213, 0, x_210);
lean_ctor_set(x_213, 1, x_212);
lean_inc(x_27);
x_214 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_214, 0, x_27);
lean_ctor_set(x_214, 1, x_206);
lean_ctor_set(x_214, 2, x_209);
lean_ctor_set(x_214, 3, x_213);
lean_inc(x_1);
x_215 = l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(x_90, x_1);
if (lean_obj_tag(x_215) == 0)
{
lean_object* x_216; 
lean_dec(x_116);
x_216 = l_Lean_quoteNameMk(x_1);
x_130 = x_174;
x_131 = x_204;
x_132 = x_184;
x_133 = x_188;
x_134 = x_214;
x_135 = x_203;
x_136 = x_198;
x_137 = x_216;
goto block_173;
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
lean_dec(x_1);
x_217 = lean_ctor_get(x_215, 0);
lean_inc(x_217);
lean_dec(x_215);
x_218 = lean_mk_string_unchecked("`", 1, 1);
x_219 = lean_mk_string_unchecked(".", 1, 1);
x_220 = l_String_intercalate(x_219, x_217);
lean_dec(x_219);
x_221 = lean_string_append(x_218, x_220);
lean_dec(x_220);
x_222 = l_Lean_Syntax_mkNameLit(x_221, x_72);
x_223 = lean_unsigned_to_nat(1u);
x_224 = lean_mk_empty_array_with_capacity(x_223);
x_225 = lean_array_push(x_224, x_222);
x_226 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_226, 0, x_72);
lean_ctor_set(x_226, 1, x_116);
lean_ctor_set(x_226, 2, x_225);
x_130 = x_174;
x_131 = x_204;
x_132 = x_184;
x_133 = x_188;
x_134 = x_214;
x_135 = x_203;
x_136 = x_198;
x_137 = x_226;
goto block_173;
}
}
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; uint8_t x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_399; lean_object* x_453; 
x_240 = lean_ctor_get(x_14, 0);
x_241 = lean_ctor_get(x_14, 1);
lean_inc(x_241);
lean_inc(x_240);
lean_dec(x_14);
x_242 = lean_mk_string_unchecked("`(", 2, 2);
x_243 = lean_mk_string_unchecked("quot", 4, 4);
x_244 = lean_string_append(x_242, x_5);
lean_dec(x_5);
x_245 = lean_mk_string_unchecked("| ", 2, 2);
x_246 = l_Lean_Name_mkStr1(x_243);
x_247 = lean_box(0);
x_248 = lean_string_append(x_244, x_245);
lean_dec(x_245);
lean_inc(x_1);
x_249 = l_Lean_Name_append(x_1, x_246);
x_250 = lean_unbox(x_247);
x_251 = l_Lean_SourceInfo_fromRef(x_8, x_250);
lean_dec(x_8);
x_252 = lean_mk_string_unchecked("Lean", 4, 4);
x_253 = lean_mk_string_unchecked("Parser", 6, 6);
x_254 = lean_mk_string_unchecked("Command", 7, 7);
x_255 = lean_mk_string_unchecked("declaration", 11, 11);
lean_inc(x_254);
lean_inc(x_253);
lean_inc(x_252);
x_256 = l_Lean_Name_mkStr4(x_252, x_253, x_254, x_255);
x_257 = lean_mk_string_unchecked("declModifiers", 13, 13);
lean_inc(x_254);
lean_inc(x_253);
lean_inc(x_252);
x_258 = l_Lean_Name_mkStr4(x_252, x_253, x_254, x_257);
x_259 = lean_mk_string_unchecked("null", 4, 4);
x_260 = l_Lean_Name_mkStr1(x_259);
x_261 = l_Array_mkArray0(lean_box(0));
lean_inc(x_260);
lean_inc(x_251);
x_262 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_262, 0, x_251);
lean_ctor_set(x_262, 1, x_260);
lean_ctor_set(x_262, 2, x_261);
x_263 = lean_mk_string_unchecked("Term", 4, 4);
x_264 = lean_mk_string_unchecked("attributes", 10, 10);
lean_inc(x_263);
lean_inc(x_253);
lean_inc(x_252);
x_265 = l_Lean_Name_mkStr4(x_252, x_253, x_263, x_264);
x_266 = lean_mk_string_unchecked("@[", 2, 2);
lean_inc(x_251);
x_267 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_267, 0, x_251);
lean_ctor_set(x_267, 1, x_266);
x_268 = lean_mk_string_unchecked("attrInstance", 12, 12);
lean_inc(x_263);
lean_inc(x_253);
lean_inc(x_252);
x_269 = l_Lean_Name_mkStr4(x_252, x_253, x_263, x_268);
x_270 = lean_mk_string_unchecked("attrKind", 8, 8);
lean_inc(x_263);
lean_inc(x_253);
lean_inc(x_252);
x_271 = l_Lean_Name_mkStr4(x_252, x_253, x_263, x_270);
lean_inc(x_262);
lean_inc(x_251);
x_272 = l_Lean_Syntax_node1(x_251, x_271, x_262);
x_273 = lean_mk_string_unchecked("Attr", 4, 4);
x_274 = lean_mk_string_unchecked("simple", 6, 6);
lean_inc(x_253);
lean_inc(x_252);
x_275 = l_Lean_Name_mkStr4(x_252, x_253, x_273, x_274);
x_276 = lean_mk_string_unchecked("term_parser", 11, 11);
lean_inc(x_276);
x_277 = l_String_toSubstring_x27(x_276);
x_278 = l_Lean_Name_mkStr1(x_276);
lean_inc(x_12);
lean_inc(x_240);
x_279 = l_Lean_addMacroScope(x_240, x_278, x_12);
x_280 = lean_box(0);
lean_inc(x_251);
x_281 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_281, 0, x_251);
lean_ctor_set(x_281, 1, x_277);
lean_ctor_set(x_281, 2, x_279);
lean_ctor_set(x_281, 3, x_280);
lean_inc(x_262);
lean_inc(x_251);
x_282 = l_Lean_Syntax_node2(x_251, x_275, x_281, x_262);
lean_inc(x_251);
x_283 = l_Lean_Syntax_node2(x_251, x_269, x_272, x_282);
lean_inc(x_260);
lean_inc(x_251);
x_284 = l_Lean_Syntax_node1(x_251, x_260, x_283);
x_285 = lean_mk_string_unchecked("]", 1, 1);
lean_inc(x_251);
lean_ctor_set_tag(x_10, 2);
lean_ctor_set(x_10, 1, x_285);
lean_ctor_set(x_10, 0, x_251);
lean_inc(x_251);
x_286 = l_Lean_Syntax_node3(x_251, x_265, x_267, x_284, x_10);
lean_inc(x_260);
lean_inc(x_251);
x_287 = l_Lean_Syntax_node1(x_251, x_260, x_286);
lean_inc_n(x_262, 5);
lean_inc(x_251);
x_288 = l_Lean_Syntax_node6(x_251, x_258, x_262, x_287, x_262, x_262, x_262, x_262);
x_289 = lean_mk_string_unchecked("definition", 10, 10);
lean_inc(x_254);
lean_inc(x_253);
lean_inc(x_252);
x_290 = l_Lean_Name_mkStr4(x_252, x_253, x_254, x_289);
x_291 = lean_mk_string_unchecked("def", 3, 3);
lean_inc(x_251);
lean_ctor_set_tag(x_6, 2);
lean_ctor_set(x_6, 1, x_291);
lean_ctor_set(x_6, 0, x_251);
x_292 = lean_mk_string_unchecked("declId", 6, 6);
lean_inc(x_254);
lean_inc(x_253);
lean_inc(x_252);
x_293 = l_Lean_Name_mkStr4(x_252, x_253, x_254, x_292);
lean_inc(x_249);
x_294 = lean_mk_syntax_ident(x_249);
x_295 = lean_unsigned_to_nat(0u);
x_296 = lean_mk_empty_array_with_capacity(x_295);
x_297 = lean_box(2);
lean_inc(x_260);
x_298 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_298, 0, x_297);
lean_ctor_set(x_298, 1, x_260);
lean_ctor_set(x_298, 2, x_296);
x_299 = lean_unsigned_to_nat(2u);
x_300 = lean_mk_empty_array_with_capacity(x_299);
x_301 = lean_array_push(x_300, x_294);
x_302 = lean_array_push(x_301, x_298);
x_303 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_303, 0, x_297);
lean_ctor_set(x_303, 1, x_293);
lean_ctor_set(x_303, 2, x_302);
x_304 = lean_mk_string_unchecked("optDeclSig", 10, 10);
lean_inc(x_254);
lean_inc(x_253);
lean_inc(x_252);
x_305 = l_Lean_Name_mkStr4(x_252, x_253, x_254, x_304);
x_306 = lean_mk_string_unchecked("typeSpec", 8, 8);
lean_inc(x_263);
lean_inc(x_253);
lean_inc(x_252);
x_307 = l_Lean_Name_mkStr4(x_252, x_253, x_263, x_306);
x_308 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_251);
x_309 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_309, 0, x_251);
lean_ctor_set(x_309, 1, x_308);
x_310 = lean_mk_string_unchecked("Lean.ParserDescr", 16, 16);
x_311 = l_String_toSubstring_x27(x_310);
x_312 = lean_mk_string_unchecked("ParserDescr", 11, 11);
lean_inc(x_312);
lean_inc(x_252);
x_313 = l_Lean_Name_mkStr2(x_252, x_312);
lean_inc(x_12);
lean_inc(x_313);
lean_inc(x_240);
x_314 = l_Lean_addMacroScope(x_240, x_313, x_12);
x_315 = lean_box(0);
lean_inc(x_313);
x_316 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_316, 0, x_313);
lean_ctor_set(x_316, 1, x_315);
x_317 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_317, 0, x_313);
x_318 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_318, 0, x_317);
lean_ctor_set(x_318, 1, x_280);
x_319 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_319, 0, x_316);
lean_ctor_set(x_319, 1, x_318);
lean_inc(x_251);
x_320 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_320, 0, x_251);
lean_ctor_set(x_320, 1, x_311);
lean_ctor_set(x_320, 2, x_314);
lean_ctor_set(x_320, 3, x_319);
lean_inc(x_251);
x_321 = l_Lean_Syntax_node2(x_251, x_307, x_309, x_320);
lean_inc(x_260);
lean_inc(x_251);
x_322 = l_Lean_Syntax_node1(x_251, x_260, x_321);
lean_inc(x_262);
lean_inc(x_251);
x_323 = l_Lean_Syntax_node2(x_251, x_305, x_262, x_322);
x_324 = lean_mk_string_unchecked("declValSimple", 13, 13);
lean_inc(x_253);
lean_inc(x_252);
x_325 = l_Lean_Name_mkStr4(x_252, x_253, x_254, x_324);
x_326 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_251);
x_327 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_327, 0, x_251);
lean_ctor_set(x_327, 1, x_326);
x_328 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_263);
lean_inc(x_253);
lean_inc(x_252);
x_329 = l_Lean_Name_mkStr4(x_252, x_253, x_263, x_328);
x_330 = lean_mk_string_unchecked("Lean.ParserDescr.node", 21, 21);
x_331 = l_String_toSubstring_x27(x_330);
x_332 = lean_mk_string_unchecked("node", 4, 4);
lean_inc(x_312);
lean_inc(x_252);
x_333 = l_Lean_Name_mkStr3(x_252, x_312, x_332);
lean_inc(x_12);
lean_inc(x_333);
lean_inc(x_240);
x_334 = l_Lean_addMacroScope(x_240, x_333, x_12);
lean_inc(x_333);
x_335 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_335, 0, x_333);
lean_ctor_set(x_335, 1, x_315);
x_336 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_336, 0, x_333);
x_337 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_337, 0, x_336);
lean_ctor_set(x_337, 1, x_280);
x_338 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_338, 0, x_335);
lean_ctor_set(x_338, 1, x_337);
lean_inc(x_251);
x_339 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_339, 0, x_251);
lean_ctor_set(x_339, 1, x_331);
lean_ctor_set(x_339, 2, x_334);
lean_ctor_set(x_339, 3, x_338);
x_340 = lean_mk_string_unchecked("quotedName", 10, 10);
lean_inc(x_263);
lean_inc(x_253);
lean_inc(x_252);
x_341 = l_Lean_Name_mkStr4(x_252, x_253, x_263, x_340);
x_342 = lean_mk_string_unchecked("name", 4, 4);
x_343 = l_Lean_Name_mkStr1(x_342);
x_344 = lean_mk_string_unchecked("`Lean.Parser.Term.quot", 22, 22);
lean_inc(x_251);
x_345 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_345, 0, x_251);
lean_ctor_set(x_345, 1, x_344);
lean_inc(x_343);
lean_inc(x_251);
x_346 = l_Lean_Syntax_node1(x_251, x_343, x_345);
lean_inc(x_341);
lean_inc(x_251);
x_347 = l_Lean_Syntax_node1(x_251, x_341, x_346);
x_348 = lean_unsigned_to_nat(1024u);
x_349 = l___private_Init_Data_Repr_0__Nat_reprFast(x_348);
x_350 = l_Lean_Syntax_mkNumLit(x_349, x_297);
x_351 = lean_mk_string_unchecked("paren", 5, 5);
lean_inc(x_253);
lean_inc(x_252);
x_352 = l_Lean_Name_mkStr4(x_252, x_253, x_263, x_351);
x_353 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_251);
x_354 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_354, 0, x_251);
lean_ctor_set(x_354, 1, x_353);
lean_inc(x_249);
x_453 = l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(x_315, x_249);
if (lean_obj_tag(x_453) == 0)
{
lean_object* x_454; 
x_454 = l_Lean_quoteNameMk(x_249);
x_399 = x_454;
goto block_452;
}
else
{
lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; 
lean_dec(x_249);
x_455 = lean_ctor_get(x_453, 0);
lean_inc(x_455);
lean_dec(x_453);
x_456 = lean_mk_string_unchecked("`", 1, 1);
x_457 = lean_mk_string_unchecked(".", 1, 1);
x_458 = l_String_intercalate(x_457, x_455);
lean_dec(x_457);
x_459 = lean_string_append(x_456, x_458);
lean_dec(x_458);
x_460 = l_Lean_Syntax_mkNameLit(x_459, x_297);
x_461 = lean_unsigned_to_nat(1u);
x_462 = lean_mk_empty_array_with_capacity(x_461);
x_463 = lean_array_push(x_462, x_460);
lean_inc(x_341);
x_464 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_464, 0, x_297);
lean_ctor_set(x_464, 1, x_341);
lean_ctor_set(x_464, 2, x_463);
x_399 = x_464;
goto block_452;
}
block_398:
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; 
x_363 = lean_mk_string_unchecked("num", 3, 3);
x_364 = l_Lean_Name_mkStr1(x_363);
x_365 = lean_mk_string_unchecked("0", 1, 1);
lean_inc(x_251);
x_366 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_366, 0, x_251);
lean_ctor_set(x_366, 1, x_365);
lean_inc(x_251);
x_367 = l_Lean_Syntax_node1(x_251, x_364, x_366);
lean_inc(x_260);
lean_inc(x_251);
x_368 = l_Lean_Syntax_node2(x_251, x_260, x_362, x_367);
lean_inc(x_329);
lean_inc(x_251);
x_369 = l_Lean_Syntax_node2(x_251, x_329, x_359, x_368);
lean_inc(x_360);
lean_inc(x_354);
lean_inc(x_352);
lean_inc(x_251);
x_370 = l_Lean_Syntax_node3(x_251, x_352, x_354, x_369, x_360);
x_371 = lean_mk_string_unchecked("str", 3, 3);
x_372 = l_Lean_Name_mkStr1(x_371);
x_373 = lean_mk_string_unchecked("\")\"", 3, 3);
lean_inc(x_251);
x_374 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_374, 0, x_251);
lean_ctor_set(x_374, 1, x_373);
lean_inc(x_251);
x_375 = l_Lean_Syntax_node1(x_251, x_372, x_374);
lean_inc(x_260);
lean_inc(x_251);
x_376 = l_Lean_Syntax_node1(x_251, x_260, x_375);
lean_inc(x_329);
lean_inc(x_251);
x_377 = l_Lean_Syntax_node2(x_251, x_329, x_361, x_376);
lean_inc(x_360);
lean_inc(x_354);
lean_inc(x_352);
lean_inc(x_251);
x_378 = l_Lean_Syntax_node3(x_251, x_352, x_354, x_377, x_360);
lean_inc(x_358);
lean_inc(x_260);
lean_inc(x_251);
x_379 = l_Lean_Syntax_node3(x_251, x_260, x_358, x_370, x_378);
lean_inc(x_357);
lean_inc(x_329);
lean_inc(x_251);
x_380 = l_Lean_Syntax_node2(x_251, x_329, x_357, x_379);
lean_inc(x_360);
lean_inc(x_354);
lean_inc(x_352);
lean_inc(x_251);
x_381 = l_Lean_Syntax_node3(x_251, x_352, x_354, x_380, x_360);
lean_inc(x_260);
lean_inc(x_251);
x_382 = l_Lean_Syntax_node3(x_251, x_260, x_358, x_356, x_381);
lean_inc(x_329);
lean_inc(x_251);
x_383 = l_Lean_Syntax_node2(x_251, x_329, x_357, x_382);
lean_inc(x_360);
lean_inc(x_354);
lean_inc(x_352);
lean_inc(x_251);
x_384 = l_Lean_Syntax_node3(x_251, x_352, x_354, x_383, x_360);
lean_inc(x_350);
lean_inc(x_260);
lean_inc(x_251);
x_385 = l_Lean_Syntax_node3(x_251, x_260, x_355, x_350, x_384);
lean_inc(x_339);
lean_inc(x_329);
lean_inc(x_251);
x_386 = l_Lean_Syntax_node2(x_251, x_329, x_339, x_385);
lean_inc(x_251);
x_387 = l_Lean_Syntax_node3(x_251, x_352, x_354, x_386, x_360);
lean_inc(x_251);
x_388 = l_Lean_Syntax_node3(x_251, x_260, x_347, x_350, x_387);
lean_inc(x_251);
x_389 = l_Lean_Syntax_node2(x_251, x_329, x_339, x_388);
x_390 = lean_mk_string_unchecked("Termination", 11, 11);
x_391 = lean_mk_string_unchecked("suffix", 6, 6);
x_392 = l_Lean_Name_mkStr4(x_252, x_253, x_390, x_391);
lean_inc_n(x_262, 2);
lean_inc(x_251);
x_393 = l_Lean_Syntax_node2(x_251, x_392, x_262, x_262);
lean_inc(x_262);
lean_inc(x_251);
x_394 = l_Lean_Syntax_node4(x_251, x_325, x_327, x_389, x_393, x_262);
lean_inc(x_251);
x_395 = l_Lean_Syntax_node5(x_251, x_290, x_6, x_303, x_323, x_394, x_262);
x_396 = l_Lean_Syntax_node2(x_251, x_256, x_288, x_395);
x_397 = l_Lean_Elab_Command_elabCommand(x_396, x_2, x_3, x_241);
return x_397;
}
block_452:
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; 
x_400 = lean_mk_string_unchecked("Lean.ParserDescr.binary", 23, 23);
x_401 = l_String_toSubstring_x27(x_400);
x_402 = lean_mk_string_unchecked("binary", 6, 6);
lean_inc(x_312);
lean_inc(x_252);
x_403 = l_Lean_Name_mkStr3(x_252, x_312, x_402);
lean_inc(x_12);
lean_inc(x_403);
lean_inc(x_240);
x_404 = l_Lean_addMacroScope(x_240, x_403, x_12);
lean_inc(x_403);
x_405 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_405, 0, x_403);
lean_ctor_set(x_405, 1, x_315);
x_406 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_406, 0, x_403);
x_407 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_407, 0, x_406);
lean_ctor_set(x_407, 1, x_280);
x_408 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_408, 0, x_405);
lean_ctor_set(x_408, 1, x_407);
lean_inc(x_251);
x_409 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_409, 0, x_251);
lean_ctor_set(x_409, 1, x_401);
lean_ctor_set(x_409, 2, x_404);
lean_ctor_set(x_409, 3, x_408);
x_410 = lean_mk_string_unchecked("`andthen", 8, 8);
lean_inc(x_251);
x_411 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_411, 0, x_251);
lean_ctor_set(x_411, 1, x_410);
lean_inc(x_251);
x_412 = l_Lean_Syntax_node1(x_251, x_343, x_411);
lean_inc(x_341);
lean_inc(x_251);
x_413 = l_Lean_Syntax_node1(x_251, x_341, x_412);
x_414 = lean_mk_string_unchecked("Lean.ParserDescr.symbol", 23, 23);
x_415 = l_String_toSubstring_x27(x_414);
x_416 = lean_mk_string_unchecked("symbol", 6, 6);
lean_inc(x_312);
lean_inc(x_252);
x_417 = l_Lean_Name_mkStr3(x_252, x_312, x_416);
lean_inc(x_12);
lean_inc(x_417);
lean_inc(x_240);
x_418 = l_Lean_addMacroScope(x_240, x_417, x_12);
lean_inc(x_417);
x_419 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_419, 0, x_417);
lean_ctor_set(x_419, 1, x_315);
x_420 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_420, 0, x_417);
x_421 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_421, 0, x_420);
lean_ctor_set(x_421, 1, x_280);
x_422 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_422, 0, x_419);
lean_ctor_set(x_422, 1, x_421);
lean_inc(x_251);
x_423 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_423, 0, x_251);
lean_ctor_set(x_423, 1, x_415);
lean_ctor_set(x_423, 2, x_418);
lean_ctor_set(x_423, 3, x_422);
x_424 = l_Lean_Syntax_mkStrLit(x_248, x_297);
lean_dec(x_248);
lean_inc(x_260);
lean_inc(x_251);
x_425 = l_Lean_Syntax_node1(x_251, x_260, x_424);
lean_inc(x_423);
lean_inc(x_329);
lean_inc(x_251);
x_426 = l_Lean_Syntax_node2(x_251, x_329, x_423, x_425);
x_427 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_251);
x_428 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_428, 0, x_251);
lean_ctor_set(x_428, 1, x_427);
lean_inc(x_428);
lean_inc(x_354);
lean_inc(x_352);
lean_inc(x_251);
x_429 = l_Lean_Syntax_node3(x_251, x_352, x_354, x_426, x_428);
x_430 = lean_mk_string_unchecked("Lean.ParserDescr.cat", 20, 20);
x_431 = l_String_toSubstring_x27(x_430);
x_432 = lean_mk_string_unchecked("cat", 3, 3);
lean_inc(x_252);
x_433 = l_Lean_Name_mkStr3(x_252, x_312, x_432);
lean_inc(x_433);
x_434 = l_Lean_addMacroScope(x_240, x_433, x_12);
lean_inc(x_433);
x_435 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_435, 0, x_433);
lean_ctor_set(x_435, 1, x_315);
x_436 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_436, 0, x_433);
x_437 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_437, 0, x_436);
lean_ctor_set(x_437, 1, x_280);
x_438 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_438, 0, x_435);
lean_ctor_set(x_438, 1, x_437);
lean_inc(x_251);
x_439 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_439, 0, x_251);
lean_ctor_set(x_439, 1, x_431);
lean_ctor_set(x_439, 2, x_434);
lean_ctor_set(x_439, 3, x_438);
lean_inc(x_1);
x_440 = l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(x_315, x_1);
if (lean_obj_tag(x_440) == 0)
{
lean_object* x_441; 
lean_dec(x_341);
x_441 = l_Lean_quoteNameMk(x_1);
x_355 = x_399;
x_356 = x_429;
x_357 = x_409;
x_358 = x_413;
x_359 = x_439;
x_360 = x_428;
x_361 = x_423;
x_362 = x_441;
goto block_398;
}
else
{
lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; 
lean_dec(x_1);
x_442 = lean_ctor_get(x_440, 0);
lean_inc(x_442);
lean_dec(x_440);
x_443 = lean_mk_string_unchecked("`", 1, 1);
x_444 = lean_mk_string_unchecked(".", 1, 1);
x_445 = l_String_intercalate(x_444, x_442);
lean_dec(x_444);
x_446 = lean_string_append(x_443, x_445);
lean_dec(x_445);
x_447 = l_Lean_Syntax_mkNameLit(x_446, x_297);
x_448 = lean_unsigned_to_nat(1u);
x_449 = lean_mk_empty_array_with_capacity(x_448);
x_450 = lean_array_push(x_449, x_447);
x_451 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_451, 0, x_297);
lean_ctor_set(x_451, 1, x_341);
lean_ctor_set(x_451, 2, x_450);
x_355 = x_399;
x_356 = x_429;
x_357 = x_409;
x_358 = x_413;
x_359 = x_439;
x_360 = x_428;
x_361 = x_423;
x_362 = x_451;
goto block_398;
}
}
}
}
else
{
lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; uint8_t x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_629; lean_object* x_683; 
x_465 = lean_ctor_get(x_10, 0);
x_466 = lean_ctor_get(x_10, 1);
lean_inc(x_466);
lean_inc(x_465);
lean_dec(x_10);
x_467 = l_Lean_Elab_Command_getMainModule___redArg(x_3, x_466);
x_468 = lean_ctor_get(x_467, 0);
lean_inc(x_468);
x_469 = lean_ctor_get(x_467, 1);
lean_inc(x_469);
if (lean_is_exclusive(x_467)) {
 lean_ctor_release(x_467, 0);
 lean_ctor_release(x_467, 1);
 x_470 = x_467;
} else {
 lean_dec_ref(x_467);
 x_470 = lean_box(0);
}
x_471 = lean_mk_string_unchecked("`(", 2, 2);
x_472 = lean_mk_string_unchecked("quot", 4, 4);
x_473 = lean_string_append(x_471, x_5);
lean_dec(x_5);
x_474 = lean_mk_string_unchecked("| ", 2, 2);
x_475 = l_Lean_Name_mkStr1(x_472);
x_476 = lean_box(0);
x_477 = lean_string_append(x_473, x_474);
lean_dec(x_474);
lean_inc(x_1);
x_478 = l_Lean_Name_append(x_1, x_475);
x_479 = lean_unbox(x_476);
x_480 = l_Lean_SourceInfo_fromRef(x_8, x_479);
lean_dec(x_8);
x_481 = lean_mk_string_unchecked("Lean", 4, 4);
x_482 = lean_mk_string_unchecked("Parser", 6, 6);
x_483 = lean_mk_string_unchecked("Command", 7, 7);
x_484 = lean_mk_string_unchecked("declaration", 11, 11);
lean_inc(x_483);
lean_inc(x_482);
lean_inc(x_481);
x_485 = l_Lean_Name_mkStr4(x_481, x_482, x_483, x_484);
x_486 = lean_mk_string_unchecked("declModifiers", 13, 13);
lean_inc(x_483);
lean_inc(x_482);
lean_inc(x_481);
x_487 = l_Lean_Name_mkStr4(x_481, x_482, x_483, x_486);
x_488 = lean_mk_string_unchecked("null", 4, 4);
x_489 = l_Lean_Name_mkStr1(x_488);
x_490 = l_Array_mkArray0(lean_box(0));
lean_inc(x_489);
lean_inc(x_480);
x_491 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_491, 0, x_480);
lean_ctor_set(x_491, 1, x_489);
lean_ctor_set(x_491, 2, x_490);
x_492 = lean_mk_string_unchecked("Term", 4, 4);
x_493 = lean_mk_string_unchecked("attributes", 10, 10);
lean_inc(x_492);
lean_inc(x_482);
lean_inc(x_481);
x_494 = l_Lean_Name_mkStr4(x_481, x_482, x_492, x_493);
x_495 = lean_mk_string_unchecked("@[", 2, 2);
lean_inc(x_480);
if (lean_is_scalar(x_470)) {
 x_496 = lean_alloc_ctor(2, 2, 0);
} else {
 x_496 = x_470;
 lean_ctor_set_tag(x_496, 2);
}
lean_ctor_set(x_496, 0, x_480);
lean_ctor_set(x_496, 1, x_495);
x_497 = lean_mk_string_unchecked("attrInstance", 12, 12);
lean_inc(x_492);
lean_inc(x_482);
lean_inc(x_481);
x_498 = l_Lean_Name_mkStr4(x_481, x_482, x_492, x_497);
x_499 = lean_mk_string_unchecked("attrKind", 8, 8);
lean_inc(x_492);
lean_inc(x_482);
lean_inc(x_481);
x_500 = l_Lean_Name_mkStr4(x_481, x_482, x_492, x_499);
lean_inc(x_491);
lean_inc(x_480);
x_501 = l_Lean_Syntax_node1(x_480, x_500, x_491);
x_502 = lean_mk_string_unchecked("Attr", 4, 4);
x_503 = lean_mk_string_unchecked("simple", 6, 6);
lean_inc(x_482);
lean_inc(x_481);
x_504 = l_Lean_Name_mkStr4(x_481, x_482, x_502, x_503);
x_505 = lean_mk_string_unchecked("term_parser", 11, 11);
lean_inc(x_505);
x_506 = l_String_toSubstring_x27(x_505);
x_507 = l_Lean_Name_mkStr1(x_505);
lean_inc(x_465);
lean_inc(x_468);
x_508 = l_Lean_addMacroScope(x_468, x_507, x_465);
x_509 = lean_box(0);
lean_inc(x_480);
x_510 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_510, 0, x_480);
lean_ctor_set(x_510, 1, x_506);
lean_ctor_set(x_510, 2, x_508);
lean_ctor_set(x_510, 3, x_509);
lean_inc(x_491);
lean_inc(x_480);
x_511 = l_Lean_Syntax_node2(x_480, x_504, x_510, x_491);
lean_inc(x_480);
x_512 = l_Lean_Syntax_node2(x_480, x_498, x_501, x_511);
lean_inc(x_489);
lean_inc(x_480);
x_513 = l_Lean_Syntax_node1(x_480, x_489, x_512);
x_514 = lean_mk_string_unchecked("]", 1, 1);
lean_inc(x_480);
x_515 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_515, 0, x_480);
lean_ctor_set(x_515, 1, x_514);
lean_inc(x_480);
x_516 = l_Lean_Syntax_node3(x_480, x_494, x_496, x_513, x_515);
lean_inc(x_489);
lean_inc(x_480);
x_517 = l_Lean_Syntax_node1(x_480, x_489, x_516);
lean_inc_n(x_491, 5);
lean_inc(x_480);
x_518 = l_Lean_Syntax_node6(x_480, x_487, x_491, x_517, x_491, x_491, x_491, x_491);
x_519 = lean_mk_string_unchecked("definition", 10, 10);
lean_inc(x_483);
lean_inc(x_482);
lean_inc(x_481);
x_520 = l_Lean_Name_mkStr4(x_481, x_482, x_483, x_519);
x_521 = lean_mk_string_unchecked("def", 3, 3);
lean_inc(x_480);
lean_ctor_set_tag(x_6, 2);
lean_ctor_set(x_6, 1, x_521);
lean_ctor_set(x_6, 0, x_480);
x_522 = lean_mk_string_unchecked("declId", 6, 6);
lean_inc(x_483);
lean_inc(x_482);
lean_inc(x_481);
x_523 = l_Lean_Name_mkStr4(x_481, x_482, x_483, x_522);
lean_inc(x_478);
x_524 = lean_mk_syntax_ident(x_478);
x_525 = lean_unsigned_to_nat(0u);
x_526 = lean_mk_empty_array_with_capacity(x_525);
x_527 = lean_box(2);
lean_inc(x_489);
x_528 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_528, 0, x_527);
lean_ctor_set(x_528, 1, x_489);
lean_ctor_set(x_528, 2, x_526);
x_529 = lean_unsigned_to_nat(2u);
x_530 = lean_mk_empty_array_with_capacity(x_529);
x_531 = lean_array_push(x_530, x_524);
x_532 = lean_array_push(x_531, x_528);
x_533 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_533, 0, x_527);
lean_ctor_set(x_533, 1, x_523);
lean_ctor_set(x_533, 2, x_532);
x_534 = lean_mk_string_unchecked("optDeclSig", 10, 10);
lean_inc(x_483);
lean_inc(x_482);
lean_inc(x_481);
x_535 = l_Lean_Name_mkStr4(x_481, x_482, x_483, x_534);
x_536 = lean_mk_string_unchecked("typeSpec", 8, 8);
lean_inc(x_492);
lean_inc(x_482);
lean_inc(x_481);
x_537 = l_Lean_Name_mkStr4(x_481, x_482, x_492, x_536);
x_538 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_480);
x_539 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_539, 0, x_480);
lean_ctor_set(x_539, 1, x_538);
x_540 = lean_mk_string_unchecked("Lean.ParserDescr", 16, 16);
x_541 = l_String_toSubstring_x27(x_540);
x_542 = lean_mk_string_unchecked("ParserDescr", 11, 11);
lean_inc(x_542);
lean_inc(x_481);
x_543 = l_Lean_Name_mkStr2(x_481, x_542);
lean_inc(x_465);
lean_inc(x_543);
lean_inc(x_468);
x_544 = l_Lean_addMacroScope(x_468, x_543, x_465);
x_545 = lean_box(0);
lean_inc(x_543);
x_546 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_546, 0, x_543);
lean_ctor_set(x_546, 1, x_545);
x_547 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_547, 0, x_543);
x_548 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_548, 0, x_547);
lean_ctor_set(x_548, 1, x_509);
x_549 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_549, 0, x_546);
lean_ctor_set(x_549, 1, x_548);
lean_inc(x_480);
x_550 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_550, 0, x_480);
lean_ctor_set(x_550, 1, x_541);
lean_ctor_set(x_550, 2, x_544);
lean_ctor_set(x_550, 3, x_549);
lean_inc(x_480);
x_551 = l_Lean_Syntax_node2(x_480, x_537, x_539, x_550);
lean_inc(x_489);
lean_inc(x_480);
x_552 = l_Lean_Syntax_node1(x_480, x_489, x_551);
lean_inc(x_491);
lean_inc(x_480);
x_553 = l_Lean_Syntax_node2(x_480, x_535, x_491, x_552);
x_554 = lean_mk_string_unchecked("declValSimple", 13, 13);
lean_inc(x_482);
lean_inc(x_481);
x_555 = l_Lean_Name_mkStr4(x_481, x_482, x_483, x_554);
x_556 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_480);
x_557 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_557, 0, x_480);
lean_ctor_set(x_557, 1, x_556);
x_558 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_492);
lean_inc(x_482);
lean_inc(x_481);
x_559 = l_Lean_Name_mkStr4(x_481, x_482, x_492, x_558);
x_560 = lean_mk_string_unchecked("Lean.ParserDescr.node", 21, 21);
x_561 = l_String_toSubstring_x27(x_560);
x_562 = lean_mk_string_unchecked("node", 4, 4);
lean_inc(x_542);
lean_inc(x_481);
x_563 = l_Lean_Name_mkStr3(x_481, x_542, x_562);
lean_inc(x_465);
lean_inc(x_563);
lean_inc(x_468);
x_564 = l_Lean_addMacroScope(x_468, x_563, x_465);
lean_inc(x_563);
x_565 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_565, 0, x_563);
lean_ctor_set(x_565, 1, x_545);
x_566 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_566, 0, x_563);
x_567 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_567, 0, x_566);
lean_ctor_set(x_567, 1, x_509);
x_568 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_568, 0, x_565);
lean_ctor_set(x_568, 1, x_567);
lean_inc(x_480);
x_569 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_569, 0, x_480);
lean_ctor_set(x_569, 1, x_561);
lean_ctor_set(x_569, 2, x_564);
lean_ctor_set(x_569, 3, x_568);
x_570 = lean_mk_string_unchecked("quotedName", 10, 10);
lean_inc(x_492);
lean_inc(x_482);
lean_inc(x_481);
x_571 = l_Lean_Name_mkStr4(x_481, x_482, x_492, x_570);
x_572 = lean_mk_string_unchecked("name", 4, 4);
x_573 = l_Lean_Name_mkStr1(x_572);
x_574 = lean_mk_string_unchecked("`Lean.Parser.Term.quot", 22, 22);
lean_inc(x_480);
x_575 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_575, 0, x_480);
lean_ctor_set(x_575, 1, x_574);
lean_inc(x_573);
lean_inc(x_480);
x_576 = l_Lean_Syntax_node1(x_480, x_573, x_575);
lean_inc(x_571);
lean_inc(x_480);
x_577 = l_Lean_Syntax_node1(x_480, x_571, x_576);
x_578 = lean_unsigned_to_nat(1024u);
x_579 = l___private_Init_Data_Repr_0__Nat_reprFast(x_578);
x_580 = l_Lean_Syntax_mkNumLit(x_579, x_527);
x_581 = lean_mk_string_unchecked("paren", 5, 5);
lean_inc(x_482);
lean_inc(x_481);
x_582 = l_Lean_Name_mkStr4(x_481, x_482, x_492, x_581);
x_583 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_480);
x_584 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_584, 0, x_480);
lean_ctor_set(x_584, 1, x_583);
lean_inc(x_478);
x_683 = l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(x_545, x_478);
if (lean_obj_tag(x_683) == 0)
{
lean_object* x_684; 
x_684 = l_Lean_quoteNameMk(x_478);
x_629 = x_684;
goto block_682;
}
else
{
lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; 
lean_dec(x_478);
x_685 = lean_ctor_get(x_683, 0);
lean_inc(x_685);
lean_dec(x_683);
x_686 = lean_mk_string_unchecked("`", 1, 1);
x_687 = lean_mk_string_unchecked(".", 1, 1);
x_688 = l_String_intercalate(x_687, x_685);
lean_dec(x_687);
x_689 = lean_string_append(x_686, x_688);
lean_dec(x_688);
x_690 = l_Lean_Syntax_mkNameLit(x_689, x_527);
x_691 = lean_unsigned_to_nat(1u);
x_692 = lean_mk_empty_array_with_capacity(x_691);
x_693 = lean_array_push(x_692, x_690);
lean_inc(x_571);
x_694 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_694, 0, x_527);
lean_ctor_set(x_694, 1, x_571);
lean_ctor_set(x_694, 2, x_693);
x_629 = x_694;
goto block_682;
}
block_628:
{
lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; 
x_593 = lean_mk_string_unchecked("num", 3, 3);
x_594 = l_Lean_Name_mkStr1(x_593);
x_595 = lean_mk_string_unchecked("0", 1, 1);
lean_inc(x_480);
x_596 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_596, 0, x_480);
lean_ctor_set(x_596, 1, x_595);
lean_inc(x_480);
x_597 = l_Lean_Syntax_node1(x_480, x_594, x_596);
lean_inc(x_489);
lean_inc(x_480);
x_598 = l_Lean_Syntax_node2(x_480, x_489, x_592, x_597);
lean_inc(x_559);
lean_inc(x_480);
x_599 = l_Lean_Syntax_node2(x_480, x_559, x_589, x_598);
lean_inc(x_590);
lean_inc(x_584);
lean_inc(x_582);
lean_inc(x_480);
x_600 = l_Lean_Syntax_node3(x_480, x_582, x_584, x_599, x_590);
x_601 = lean_mk_string_unchecked("str", 3, 3);
x_602 = l_Lean_Name_mkStr1(x_601);
x_603 = lean_mk_string_unchecked("\")\"", 3, 3);
lean_inc(x_480);
x_604 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_604, 0, x_480);
lean_ctor_set(x_604, 1, x_603);
lean_inc(x_480);
x_605 = l_Lean_Syntax_node1(x_480, x_602, x_604);
lean_inc(x_489);
lean_inc(x_480);
x_606 = l_Lean_Syntax_node1(x_480, x_489, x_605);
lean_inc(x_559);
lean_inc(x_480);
x_607 = l_Lean_Syntax_node2(x_480, x_559, x_591, x_606);
lean_inc(x_590);
lean_inc(x_584);
lean_inc(x_582);
lean_inc(x_480);
x_608 = l_Lean_Syntax_node3(x_480, x_582, x_584, x_607, x_590);
lean_inc(x_588);
lean_inc(x_489);
lean_inc(x_480);
x_609 = l_Lean_Syntax_node3(x_480, x_489, x_588, x_600, x_608);
lean_inc(x_587);
lean_inc(x_559);
lean_inc(x_480);
x_610 = l_Lean_Syntax_node2(x_480, x_559, x_587, x_609);
lean_inc(x_590);
lean_inc(x_584);
lean_inc(x_582);
lean_inc(x_480);
x_611 = l_Lean_Syntax_node3(x_480, x_582, x_584, x_610, x_590);
lean_inc(x_489);
lean_inc(x_480);
x_612 = l_Lean_Syntax_node3(x_480, x_489, x_588, x_586, x_611);
lean_inc(x_559);
lean_inc(x_480);
x_613 = l_Lean_Syntax_node2(x_480, x_559, x_587, x_612);
lean_inc(x_590);
lean_inc(x_584);
lean_inc(x_582);
lean_inc(x_480);
x_614 = l_Lean_Syntax_node3(x_480, x_582, x_584, x_613, x_590);
lean_inc(x_580);
lean_inc(x_489);
lean_inc(x_480);
x_615 = l_Lean_Syntax_node3(x_480, x_489, x_585, x_580, x_614);
lean_inc(x_569);
lean_inc(x_559);
lean_inc(x_480);
x_616 = l_Lean_Syntax_node2(x_480, x_559, x_569, x_615);
lean_inc(x_480);
x_617 = l_Lean_Syntax_node3(x_480, x_582, x_584, x_616, x_590);
lean_inc(x_480);
x_618 = l_Lean_Syntax_node3(x_480, x_489, x_577, x_580, x_617);
lean_inc(x_480);
x_619 = l_Lean_Syntax_node2(x_480, x_559, x_569, x_618);
x_620 = lean_mk_string_unchecked("Termination", 11, 11);
x_621 = lean_mk_string_unchecked("suffix", 6, 6);
x_622 = l_Lean_Name_mkStr4(x_481, x_482, x_620, x_621);
lean_inc_n(x_491, 2);
lean_inc(x_480);
x_623 = l_Lean_Syntax_node2(x_480, x_622, x_491, x_491);
lean_inc(x_491);
lean_inc(x_480);
x_624 = l_Lean_Syntax_node4(x_480, x_555, x_557, x_619, x_623, x_491);
lean_inc(x_480);
x_625 = l_Lean_Syntax_node5(x_480, x_520, x_6, x_533, x_553, x_624, x_491);
x_626 = l_Lean_Syntax_node2(x_480, x_485, x_518, x_625);
x_627 = l_Lean_Elab_Command_elabCommand(x_626, x_2, x_3, x_469);
return x_627;
}
block_682:
{
lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; 
x_630 = lean_mk_string_unchecked("Lean.ParserDescr.binary", 23, 23);
x_631 = l_String_toSubstring_x27(x_630);
x_632 = lean_mk_string_unchecked("binary", 6, 6);
lean_inc(x_542);
lean_inc(x_481);
x_633 = l_Lean_Name_mkStr3(x_481, x_542, x_632);
lean_inc(x_465);
lean_inc(x_633);
lean_inc(x_468);
x_634 = l_Lean_addMacroScope(x_468, x_633, x_465);
lean_inc(x_633);
x_635 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_635, 0, x_633);
lean_ctor_set(x_635, 1, x_545);
x_636 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_636, 0, x_633);
x_637 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_637, 0, x_636);
lean_ctor_set(x_637, 1, x_509);
x_638 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_638, 0, x_635);
lean_ctor_set(x_638, 1, x_637);
lean_inc(x_480);
x_639 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_639, 0, x_480);
lean_ctor_set(x_639, 1, x_631);
lean_ctor_set(x_639, 2, x_634);
lean_ctor_set(x_639, 3, x_638);
x_640 = lean_mk_string_unchecked("`andthen", 8, 8);
lean_inc(x_480);
x_641 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_641, 0, x_480);
lean_ctor_set(x_641, 1, x_640);
lean_inc(x_480);
x_642 = l_Lean_Syntax_node1(x_480, x_573, x_641);
lean_inc(x_571);
lean_inc(x_480);
x_643 = l_Lean_Syntax_node1(x_480, x_571, x_642);
x_644 = lean_mk_string_unchecked("Lean.ParserDescr.symbol", 23, 23);
x_645 = l_String_toSubstring_x27(x_644);
x_646 = lean_mk_string_unchecked("symbol", 6, 6);
lean_inc(x_542);
lean_inc(x_481);
x_647 = l_Lean_Name_mkStr3(x_481, x_542, x_646);
lean_inc(x_465);
lean_inc(x_647);
lean_inc(x_468);
x_648 = l_Lean_addMacroScope(x_468, x_647, x_465);
lean_inc(x_647);
x_649 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_649, 0, x_647);
lean_ctor_set(x_649, 1, x_545);
x_650 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_650, 0, x_647);
x_651 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_651, 0, x_650);
lean_ctor_set(x_651, 1, x_509);
x_652 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_652, 0, x_649);
lean_ctor_set(x_652, 1, x_651);
lean_inc(x_480);
x_653 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_653, 0, x_480);
lean_ctor_set(x_653, 1, x_645);
lean_ctor_set(x_653, 2, x_648);
lean_ctor_set(x_653, 3, x_652);
x_654 = l_Lean_Syntax_mkStrLit(x_477, x_527);
lean_dec(x_477);
lean_inc(x_489);
lean_inc(x_480);
x_655 = l_Lean_Syntax_node1(x_480, x_489, x_654);
lean_inc(x_653);
lean_inc(x_559);
lean_inc(x_480);
x_656 = l_Lean_Syntax_node2(x_480, x_559, x_653, x_655);
x_657 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_480);
x_658 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_658, 0, x_480);
lean_ctor_set(x_658, 1, x_657);
lean_inc(x_658);
lean_inc(x_584);
lean_inc(x_582);
lean_inc(x_480);
x_659 = l_Lean_Syntax_node3(x_480, x_582, x_584, x_656, x_658);
x_660 = lean_mk_string_unchecked("Lean.ParserDescr.cat", 20, 20);
x_661 = l_String_toSubstring_x27(x_660);
x_662 = lean_mk_string_unchecked("cat", 3, 3);
lean_inc(x_481);
x_663 = l_Lean_Name_mkStr3(x_481, x_542, x_662);
lean_inc(x_663);
x_664 = l_Lean_addMacroScope(x_468, x_663, x_465);
lean_inc(x_663);
x_665 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_665, 0, x_663);
lean_ctor_set(x_665, 1, x_545);
x_666 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_666, 0, x_663);
x_667 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_667, 0, x_666);
lean_ctor_set(x_667, 1, x_509);
x_668 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_668, 0, x_665);
lean_ctor_set(x_668, 1, x_667);
lean_inc(x_480);
x_669 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_669, 0, x_480);
lean_ctor_set(x_669, 1, x_661);
lean_ctor_set(x_669, 2, x_664);
lean_ctor_set(x_669, 3, x_668);
lean_inc(x_1);
x_670 = l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(x_545, x_1);
if (lean_obj_tag(x_670) == 0)
{
lean_object* x_671; 
lean_dec(x_571);
x_671 = l_Lean_quoteNameMk(x_1);
x_585 = x_629;
x_586 = x_659;
x_587 = x_639;
x_588 = x_643;
x_589 = x_669;
x_590 = x_658;
x_591 = x_653;
x_592 = x_671;
goto block_628;
}
else
{
lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; 
lean_dec(x_1);
x_672 = lean_ctor_get(x_670, 0);
lean_inc(x_672);
lean_dec(x_670);
x_673 = lean_mk_string_unchecked("`", 1, 1);
x_674 = lean_mk_string_unchecked(".", 1, 1);
x_675 = l_String_intercalate(x_674, x_672);
lean_dec(x_674);
x_676 = lean_string_append(x_673, x_675);
lean_dec(x_675);
x_677 = l_Lean_Syntax_mkNameLit(x_676, x_527);
x_678 = lean_unsigned_to_nat(1u);
x_679 = lean_mk_empty_array_with_capacity(x_678);
x_680 = lean_array_push(x_679, x_677);
x_681 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_681, 0, x_527);
lean_ctor_set(x_681, 1, x_571);
lean_ctor_set(x_681, 2, x_680);
x_585 = x_629;
x_586 = x_659;
x_587 = x_639;
x_588 = x_643;
x_589 = x_669;
x_590 = x_658;
x_591 = x_653;
x_592 = x_681;
goto block_628;
}
}
}
}
else
{
lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; uint8_t x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; lean_object* x_822; lean_object* x_823; lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_864; lean_object* x_918; 
x_695 = lean_ctor_get(x_6, 0);
x_696 = lean_ctor_get(x_6, 1);
lean_inc(x_696);
lean_inc(x_695);
lean_dec(x_6);
x_697 = l_Lean_Elab_Command_getCurrMacroScope(x_2, x_3, x_696);
x_698 = lean_ctor_get(x_697, 0);
lean_inc(x_698);
x_699 = lean_ctor_get(x_697, 1);
lean_inc(x_699);
if (lean_is_exclusive(x_697)) {
 lean_ctor_release(x_697, 0);
 lean_ctor_release(x_697, 1);
 x_700 = x_697;
} else {
 lean_dec_ref(x_697);
 x_700 = lean_box(0);
}
x_701 = l_Lean_Elab_Command_getMainModule___redArg(x_3, x_699);
x_702 = lean_ctor_get(x_701, 0);
lean_inc(x_702);
x_703 = lean_ctor_get(x_701, 1);
lean_inc(x_703);
if (lean_is_exclusive(x_701)) {
 lean_ctor_release(x_701, 0);
 lean_ctor_release(x_701, 1);
 x_704 = x_701;
} else {
 lean_dec_ref(x_701);
 x_704 = lean_box(0);
}
x_705 = lean_mk_string_unchecked("`(", 2, 2);
x_706 = lean_mk_string_unchecked("quot", 4, 4);
x_707 = lean_string_append(x_705, x_5);
lean_dec(x_5);
x_708 = lean_mk_string_unchecked("| ", 2, 2);
x_709 = l_Lean_Name_mkStr1(x_706);
x_710 = lean_box(0);
x_711 = lean_string_append(x_707, x_708);
lean_dec(x_708);
lean_inc(x_1);
x_712 = l_Lean_Name_append(x_1, x_709);
x_713 = lean_unbox(x_710);
x_714 = l_Lean_SourceInfo_fromRef(x_695, x_713);
lean_dec(x_695);
x_715 = lean_mk_string_unchecked("Lean", 4, 4);
x_716 = lean_mk_string_unchecked("Parser", 6, 6);
x_717 = lean_mk_string_unchecked("Command", 7, 7);
x_718 = lean_mk_string_unchecked("declaration", 11, 11);
lean_inc(x_717);
lean_inc(x_716);
lean_inc(x_715);
x_719 = l_Lean_Name_mkStr4(x_715, x_716, x_717, x_718);
x_720 = lean_mk_string_unchecked("declModifiers", 13, 13);
lean_inc(x_717);
lean_inc(x_716);
lean_inc(x_715);
x_721 = l_Lean_Name_mkStr4(x_715, x_716, x_717, x_720);
x_722 = lean_mk_string_unchecked("null", 4, 4);
x_723 = l_Lean_Name_mkStr1(x_722);
x_724 = l_Array_mkArray0(lean_box(0));
lean_inc(x_723);
lean_inc(x_714);
x_725 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_725, 0, x_714);
lean_ctor_set(x_725, 1, x_723);
lean_ctor_set(x_725, 2, x_724);
x_726 = lean_mk_string_unchecked("Term", 4, 4);
x_727 = lean_mk_string_unchecked("attributes", 10, 10);
lean_inc(x_726);
lean_inc(x_716);
lean_inc(x_715);
x_728 = l_Lean_Name_mkStr4(x_715, x_716, x_726, x_727);
x_729 = lean_mk_string_unchecked("@[", 2, 2);
lean_inc(x_714);
if (lean_is_scalar(x_704)) {
 x_730 = lean_alloc_ctor(2, 2, 0);
} else {
 x_730 = x_704;
 lean_ctor_set_tag(x_730, 2);
}
lean_ctor_set(x_730, 0, x_714);
lean_ctor_set(x_730, 1, x_729);
x_731 = lean_mk_string_unchecked("attrInstance", 12, 12);
lean_inc(x_726);
lean_inc(x_716);
lean_inc(x_715);
x_732 = l_Lean_Name_mkStr4(x_715, x_716, x_726, x_731);
x_733 = lean_mk_string_unchecked("attrKind", 8, 8);
lean_inc(x_726);
lean_inc(x_716);
lean_inc(x_715);
x_734 = l_Lean_Name_mkStr4(x_715, x_716, x_726, x_733);
lean_inc(x_725);
lean_inc(x_714);
x_735 = l_Lean_Syntax_node1(x_714, x_734, x_725);
x_736 = lean_mk_string_unchecked("Attr", 4, 4);
x_737 = lean_mk_string_unchecked("simple", 6, 6);
lean_inc(x_716);
lean_inc(x_715);
x_738 = l_Lean_Name_mkStr4(x_715, x_716, x_736, x_737);
x_739 = lean_mk_string_unchecked("term_parser", 11, 11);
lean_inc(x_739);
x_740 = l_String_toSubstring_x27(x_739);
x_741 = l_Lean_Name_mkStr1(x_739);
lean_inc(x_698);
lean_inc(x_702);
x_742 = l_Lean_addMacroScope(x_702, x_741, x_698);
x_743 = lean_box(0);
lean_inc(x_714);
x_744 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_744, 0, x_714);
lean_ctor_set(x_744, 1, x_740);
lean_ctor_set(x_744, 2, x_742);
lean_ctor_set(x_744, 3, x_743);
lean_inc(x_725);
lean_inc(x_714);
x_745 = l_Lean_Syntax_node2(x_714, x_738, x_744, x_725);
lean_inc(x_714);
x_746 = l_Lean_Syntax_node2(x_714, x_732, x_735, x_745);
lean_inc(x_723);
lean_inc(x_714);
x_747 = l_Lean_Syntax_node1(x_714, x_723, x_746);
x_748 = lean_mk_string_unchecked("]", 1, 1);
lean_inc(x_714);
if (lean_is_scalar(x_700)) {
 x_749 = lean_alloc_ctor(2, 2, 0);
} else {
 x_749 = x_700;
 lean_ctor_set_tag(x_749, 2);
}
lean_ctor_set(x_749, 0, x_714);
lean_ctor_set(x_749, 1, x_748);
lean_inc(x_714);
x_750 = l_Lean_Syntax_node3(x_714, x_728, x_730, x_747, x_749);
lean_inc(x_723);
lean_inc(x_714);
x_751 = l_Lean_Syntax_node1(x_714, x_723, x_750);
lean_inc_n(x_725, 5);
lean_inc(x_714);
x_752 = l_Lean_Syntax_node6(x_714, x_721, x_725, x_751, x_725, x_725, x_725, x_725);
x_753 = lean_mk_string_unchecked("definition", 10, 10);
lean_inc(x_717);
lean_inc(x_716);
lean_inc(x_715);
x_754 = l_Lean_Name_mkStr4(x_715, x_716, x_717, x_753);
x_755 = lean_mk_string_unchecked("def", 3, 3);
lean_inc(x_714);
x_756 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_756, 0, x_714);
lean_ctor_set(x_756, 1, x_755);
x_757 = lean_mk_string_unchecked("declId", 6, 6);
lean_inc(x_717);
lean_inc(x_716);
lean_inc(x_715);
x_758 = l_Lean_Name_mkStr4(x_715, x_716, x_717, x_757);
lean_inc(x_712);
x_759 = lean_mk_syntax_ident(x_712);
x_760 = lean_unsigned_to_nat(0u);
x_761 = lean_mk_empty_array_with_capacity(x_760);
x_762 = lean_box(2);
lean_inc(x_723);
x_763 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_763, 0, x_762);
lean_ctor_set(x_763, 1, x_723);
lean_ctor_set(x_763, 2, x_761);
x_764 = lean_unsigned_to_nat(2u);
x_765 = lean_mk_empty_array_with_capacity(x_764);
x_766 = lean_array_push(x_765, x_759);
x_767 = lean_array_push(x_766, x_763);
x_768 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_768, 0, x_762);
lean_ctor_set(x_768, 1, x_758);
lean_ctor_set(x_768, 2, x_767);
x_769 = lean_mk_string_unchecked("optDeclSig", 10, 10);
lean_inc(x_717);
lean_inc(x_716);
lean_inc(x_715);
x_770 = l_Lean_Name_mkStr4(x_715, x_716, x_717, x_769);
x_771 = lean_mk_string_unchecked("typeSpec", 8, 8);
lean_inc(x_726);
lean_inc(x_716);
lean_inc(x_715);
x_772 = l_Lean_Name_mkStr4(x_715, x_716, x_726, x_771);
x_773 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_714);
x_774 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_774, 0, x_714);
lean_ctor_set(x_774, 1, x_773);
x_775 = lean_mk_string_unchecked("Lean.ParserDescr", 16, 16);
x_776 = l_String_toSubstring_x27(x_775);
x_777 = lean_mk_string_unchecked("ParserDescr", 11, 11);
lean_inc(x_777);
lean_inc(x_715);
x_778 = l_Lean_Name_mkStr2(x_715, x_777);
lean_inc(x_698);
lean_inc(x_778);
lean_inc(x_702);
x_779 = l_Lean_addMacroScope(x_702, x_778, x_698);
x_780 = lean_box(0);
lean_inc(x_778);
x_781 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_781, 0, x_778);
lean_ctor_set(x_781, 1, x_780);
x_782 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_782, 0, x_778);
x_783 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_783, 0, x_782);
lean_ctor_set(x_783, 1, x_743);
x_784 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_784, 0, x_781);
lean_ctor_set(x_784, 1, x_783);
lean_inc(x_714);
x_785 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_785, 0, x_714);
lean_ctor_set(x_785, 1, x_776);
lean_ctor_set(x_785, 2, x_779);
lean_ctor_set(x_785, 3, x_784);
lean_inc(x_714);
x_786 = l_Lean_Syntax_node2(x_714, x_772, x_774, x_785);
lean_inc(x_723);
lean_inc(x_714);
x_787 = l_Lean_Syntax_node1(x_714, x_723, x_786);
lean_inc(x_725);
lean_inc(x_714);
x_788 = l_Lean_Syntax_node2(x_714, x_770, x_725, x_787);
x_789 = lean_mk_string_unchecked("declValSimple", 13, 13);
lean_inc(x_716);
lean_inc(x_715);
x_790 = l_Lean_Name_mkStr4(x_715, x_716, x_717, x_789);
x_791 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_714);
x_792 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_792, 0, x_714);
lean_ctor_set(x_792, 1, x_791);
x_793 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_726);
lean_inc(x_716);
lean_inc(x_715);
x_794 = l_Lean_Name_mkStr4(x_715, x_716, x_726, x_793);
x_795 = lean_mk_string_unchecked("Lean.ParserDescr.node", 21, 21);
x_796 = l_String_toSubstring_x27(x_795);
x_797 = lean_mk_string_unchecked("node", 4, 4);
lean_inc(x_777);
lean_inc(x_715);
x_798 = l_Lean_Name_mkStr3(x_715, x_777, x_797);
lean_inc(x_698);
lean_inc(x_798);
lean_inc(x_702);
x_799 = l_Lean_addMacroScope(x_702, x_798, x_698);
lean_inc(x_798);
x_800 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_800, 0, x_798);
lean_ctor_set(x_800, 1, x_780);
x_801 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_801, 0, x_798);
x_802 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_802, 0, x_801);
lean_ctor_set(x_802, 1, x_743);
x_803 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_803, 0, x_800);
lean_ctor_set(x_803, 1, x_802);
lean_inc(x_714);
x_804 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_804, 0, x_714);
lean_ctor_set(x_804, 1, x_796);
lean_ctor_set(x_804, 2, x_799);
lean_ctor_set(x_804, 3, x_803);
x_805 = lean_mk_string_unchecked("quotedName", 10, 10);
lean_inc(x_726);
lean_inc(x_716);
lean_inc(x_715);
x_806 = l_Lean_Name_mkStr4(x_715, x_716, x_726, x_805);
x_807 = lean_mk_string_unchecked("name", 4, 4);
x_808 = l_Lean_Name_mkStr1(x_807);
x_809 = lean_mk_string_unchecked("`Lean.Parser.Term.quot", 22, 22);
lean_inc(x_714);
x_810 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_810, 0, x_714);
lean_ctor_set(x_810, 1, x_809);
lean_inc(x_808);
lean_inc(x_714);
x_811 = l_Lean_Syntax_node1(x_714, x_808, x_810);
lean_inc(x_806);
lean_inc(x_714);
x_812 = l_Lean_Syntax_node1(x_714, x_806, x_811);
x_813 = lean_unsigned_to_nat(1024u);
x_814 = l___private_Init_Data_Repr_0__Nat_reprFast(x_813);
x_815 = l_Lean_Syntax_mkNumLit(x_814, x_762);
x_816 = lean_mk_string_unchecked("paren", 5, 5);
lean_inc(x_716);
lean_inc(x_715);
x_817 = l_Lean_Name_mkStr4(x_715, x_716, x_726, x_816);
x_818 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_714);
x_819 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_819, 0, x_714);
lean_ctor_set(x_819, 1, x_818);
lean_inc(x_712);
x_918 = l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(x_780, x_712);
if (lean_obj_tag(x_918) == 0)
{
lean_object* x_919; 
x_919 = l_Lean_quoteNameMk(x_712);
x_864 = x_919;
goto block_917;
}
else
{
lean_object* x_920; lean_object* x_921; lean_object* x_922; lean_object* x_923; lean_object* x_924; lean_object* x_925; lean_object* x_926; lean_object* x_927; lean_object* x_928; lean_object* x_929; 
lean_dec(x_712);
x_920 = lean_ctor_get(x_918, 0);
lean_inc(x_920);
lean_dec(x_918);
x_921 = lean_mk_string_unchecked("`", 1, 1);
x_922 = lean_mk_string_unchecked(".", 1, 1);
x_923 = l_String_intercalate(x_922, x_920);
lean_dec(x_922);
x_924 = lean_string_append(x_921, x_923);
lean_dec(x_923);
x_925 = l_Lean_Syntax_mkNameLit(x_924, x_762);
x_926 = lean_unsigned_to_nat(1u);
x_927 = lean_mk_empty_array_with_capacity(x_926);
x_928 = lean_array_push(x_927, x_925);
lean_inc(x_806);
x_929 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_929, 0, x_762);
lean_ctor_set(x_929, 1, x_806);
lean_ctor_set(x_929, 2, x_928);
x_864 = x_929;
goto block_917;
}
block_863:
{
lean_object* x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; lean_object* x_834; lean_object* x_835; lean_object* x_836; lean_object* x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; lean_object* x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; 
x_828 = lean_mk_string_unchecked("num", 3, 3);
x_829 = l_Lean_Name_mkStr1(x_828);
x_830 = lean_mk_string_unchecked("0", 1, 1);
lean_inc(x_714);
x_831 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_831, 0, x_714);
lean_ctor_set(x_831, 1, x_830);
lean_inc(x_714);
x_832 = l_Lean_Syntax_node1(x_714, x_829, x_831);
lean_inc(x_723);
lean_inc(x_714);
x_833 = l_Lean_Syntax_node2(x_714, x_723, x_827, x_832);
lean_inc(x_794);
lean_inc(x_714);
x_834 = l_Lean_Syntax_node2(x_714, x_794, x_824, x_833);
lean_inc(x_825);
lean_inc(x_819);
lean_inc(x_817);
lean_inc(x_714);
x_835 = l_Lean_Syntax_node3(x_714, x_817, x_819, x_834, x_825);
x_836 = lean_mk_string_unchecked("str", 3, 3);
x_837 = l_Lean_Name_mkStr1(x_836);
x_838 = lean_mk_string_unchecked("\")\"", 3, 3);
lean_inc(x_714);
x_839 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_839, 0, x_714);
lean_ctor_set(x_839, 1, x_838);
lean_inc(x_714);
x_840 = l_Lean_Syntax_node1(x_714, x_837, x_839);
lean_inc(x_723);
lean_inc(x_714);
x_841 = l_Lean_Syntax_node1(x_714, x_723, x_840);
lean_inc(x_794);
lean_inc(x_714);
x_842 = l_Lean_Syntax_node2(x_714, x_794, x_826, x_841);
lean_inc(x_825);
lean_inc(x_819);
lean_inc(x_817);
lean_inc(x_714);
x_843 = l_Lean_Syntax_node3(x_714, x_817, x_819, x_842, x_825);
lean_inc(x_823);
lean_inc(x_723);
lean_inc(x_714);
x_844 = l_Lean_Syntax_node3(x_714, x_723, x_823, x_835, x_843);
lean_inc(x_822);
lean_inc(x_794);
lean_inc(x_714);
x_845 = l_Lean_Syntax_node2(x_714, x_794, x_822, x_844);
lean_inc(x_825);
lean_inc(x_819);
lean_inc(x_817);
lean_inc(x_714);
x_846 = l_Lean_Syntax_node3(x_714, x_817, x_819, x_845, x_825);
lean_inc(x_723);
lean_inc(x_714);
x_847 = l_Lean_Syntax_node3(x_714, x_723, x_823, x_821, x_846);
lean_inc(x_794);
lean_inc(x_714);
x_848 = l_Lean_Syntax_node2(x_714, x_794, x_822, x_847);
lean_inc(x_825);
lean_inc(x_819);
lean_inc(x_817);
lean_inc(x_714);
x_849 = l_Lean_Syntax_node3(x_714, x_817, x_819, x_848, x_825);
lean_inc(x_815);
lean_inc(x_723);
lean_inc(x_714);
x_850 = l_Lean_Syntax_node3(x_714, x_723, x_820, x_815, x_849);
lean_inc(x_804);
lean_inc(x_794);
lean_inc(x_714);
x_851 = l_Lean_Syntax_node2(x_714, x_794, x_804, x_850);
lean_inc(x_714);
x_852 = l_Lean_Syntax_node3(x_714, x_817, x_819, x_851, x_825);
lean_inc(x_714);
x_853 = l_Lean_Syntax_node3(x_714, x_723, x_812, x_815, x_852);
lean_inc(x_714);
x_854 = l_Lean_Syntax_node2(x_714, x_794, x_804, x_853);
x_855 = lean_mk_string_unchecked("Termination", 11, 11);
x_856 = lean_mk_string_unchecked("suffix", 6, 6);
x_857 = l_Lean_Name_mkStr4(x_715, x_716, x_855, x_856);
lean_inc_n(x_725, 2);
lean_inc(x_714);
x_858 = l_Lean_Syntax_node2(x_714, x_857, x_725, x_725);
lean_inc(x_725);
lean_inc(x_714);
x_859 = l_Lean_Syntax_node4(x_714, x_790, x_792, x_854, x_858, x_725);
lean_inc(x_714);
x_860 = l_Lean_Syntax_node5(x_714, x_754, x_756, x_768, x_788, x_859, x_725);
x_861 = l_Lean_Syntax_node2(x_714, x_719, x_752, x_860);
x_862 = l_Lean_Elab_Command_elabCommand(x_861, x_2, x_3, x_703);
return x_862;
}
block_917:
{
lean_object* x_865; lean_object* x_866; lean_object* x_867; lean_object* x_868; lean_object* x_869; lean_object* x_870; lean_object* x_871; lean_object* x_872; lean_object* x_873; lean_object* x_874; lean_object* x_875; lean_object* x_876; lean_object* x_877; lean_object* x_878; lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; lean_object* x_884; lean_object* x_885; lean_object* x_886; lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; lean_object* x_891; lean_object* x_892; lean_object* x_893; lean_object* x_894; lean_object* x_895; lean_object* x_896; lean_object* x_897; lean_object* x_898; lean_object* x_899; lean_object* x_900; lean_object* x_901; lean_object* x_902; lean_object* x_903; lean_object* x_904; lean_object* x_905; 
x_865 = lean_mk_string_unchecked("Lean.ParserDescr.binary", 23, 23);
x_866 = l_String_toSubstring_x27(x_865);
x_867 = lean_mk_string_unchecked("binary", 6, 6);
lean_inc(x_777);
lean_inc(x_715);
x_868 = l_Lean_Name_mkStr3(x_715, x_777, x_867);
lean_inc(x_698);
lean_inc(x_868);
lean_inc(x_702);
x_869 = l_Lean_addMacroScope(x_702, x_868, x_698);
lean_inc(x_868);
x_870 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_870, 0, x_868);
lean_ctor_set(x_870, 1, x_780);
x_871 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_871, 0, x_868);
x_872 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_872, 0, x_871);
lean_ctor_set(x_872, 1, x_743);
x_873 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_873, 0, x_870);
lean_ctor_set(x_873, 1, x_872);
lean_inc(x_714);
x_874 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_874, 0, x_714);
lean_ctor_set(x_874, 1, x_866);
lean_ctor_set(x_874, 2, x_869);
lean_ctor_set(x_874, 3, x_873);
x_875 = lean_mk_string_unchecked("`andthen", 8, 8);
lean_inc(x_714);
x_876 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_876, 0, x_714);
lean_ctor_set(x_876, 1, x_875);
lean_inc(x_714);
x_877 = l_Lean_Syntax_node1(x_714, x_808, x_876);
lean_inc(x_806);
lean_inc(x_714);
x_878 = l_Lean_Syntax_node1(x_714, x_806, x_877);
x_879 = lean_mk_string_unchecked("Lean.ParserDescr.symbol", 23, 23);
x_880 = l_String_toSubstring_x27(x_879);
x_881 = lean_mk_string_unchecked("symbol", 6, 6);
lean_inc(x_777);
lean_inc(x_715);
x_882 = l_Lean_Name_mkStr3(x_715, x_777, x_881);
lean_inc(x_698);
lean_inc(x_882);
lean_inc(x_702);
x_883 = l_Lean_addMacroScope(x_702, x_882, x_698);
lean_inc(x_882);
x_884 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_884, 0, x_882);
lean_ctor_set(x_884, 1, x_780);
x_885 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_885, 0, x_882);
x_886 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_886, 0, x_885);
lean_ctor_set(x_886, 1, x_743);
x_887 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_887, 0, x_884);
lean_ctor_set(x_887, 1, x_886);
lean_inc(x_714);
x_888 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_888, 0, x_714);
lean_ctor_set(x_888, 1, x_880);
lean_ctor_set(x_888, 2, x_883);
lean_ctor_set(x_888, 3, x_887);
x_889 = l_Lean_Syntax_mkStrLit(x_711, x_762);
lean_dec(x_711);
lean_inc(x_723);
lean_inc(x_714);
x_890 = l_Lean_Syntax_node1(x_714, x_723, x_889);
lean_inc(x_888);
lean_inc(x_794);
lean_inc(x_714);
x_891 = l_Lean_Syntax_node2(x_714, x_794, x_888, x_890);
x_892 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_714);
x_893 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_893, 0, x_714);
lean_ctor_set(x_893, 1, x_892);
lean_inc(x_893);
lean_inc(x_819);
lean_inc(x_817);
lean_inc(x_714);
x_894 = l_Lean_Syntax_node3(x_714, x_817, x_819, x_891, x_893);
x_895 = lean_mk_string_unchecked("Lean.ParserDescr.cat", 20, 20);
x_896 = l_String_toSubstring_x27(x_895);
x_897 = lean_mk_string_unchecked("cat", 3, 3);
lean_inc(x_715);
x_898 = l_Lean_Name_mkStr3(x_715, x_777, x_897);
lean_inc(x_898);
x_899 = l_Lean_addMacroScope(x_702, x_898, x_698);
lean_inc(x_898);
x_900 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_900, 0, x_898);
lean_ctor_set(x_900, 1, x_780);
x_901 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_901, 0, x_898);
x_902 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_902, 0, x_901);
lean_ctor_set(x_902, 1, x_743);
x_903 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_903, 0, x_900);
lean_ctor_set(x_903, 1, x_902);
lean_inc(x_714);
x_904 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_904, 0, x_714);
lean_ctor_set(x_904, 1, x_896);
lean_ctor_set(x_904, 2, x_899);
lean_ctor_set(x_904, 3, x_903);
lean_inc(x_1);
x_905 = l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(x_780, x_1);
if (lean_obj_tag(x_905) == 0)
{
lean_object* x_906; 
lean_dec(x_806);
x_906 = l_Lean_quoteNameMk(x_1);
x_820 = x_864;
x_821 = x_894;
x_822 = x_874;
x_823 = x_878;
x_824 = x_904;
x_825 = x_893;
x_826 = x_888;
x_827 = x_906;
goto block_863;
}
else
{
lean_object* x_907; lean_object* x_908; lean_object* x_909; lean_object* x_910; lean_object* x_911; lean_object* x_912; lean_object* x_913; lean_object* x_914; lean_object* x_915; lean_object* x_916; 
lean_dec(x_1);
x_907 = lean_ctor_get(x_905, 0);
lean_inc(x_907);
lean_dec(x_905);
x_908 = lean_mk_string_unchecked("`", 1, 1);
x_909 = lean_mk_string_unchecked(".", 1, 1);
x_910 = l_String_intercalate(x_909, x_907);
lean_dec(x_909);
x_911 = lean_string_append(x_908, x_910);
lean_dec(x_910);
x_912 = l_Lean_Syntax_mkNameLit(x_911, x_762);
x_913 = lean_unsigned_to_nat(1u);
x_914 = lean_mk_empty_array_with_capacity(x_913);
x_915 = lean_array_push(x_914, x_912);
x_916 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_916, 0, x_762);
lean_ctor_set(x_916, 1, x_806);
lean_ctor_set(x_916, 2, x_915);
x_820 = x_864;
x_821 = x_894;
x_822 = x_874;
x_823 = x_878;
x_824 = x_904;
x_825 = x_893;
x_826 = x_888;
x_827 = x_916;
goto block_863;
}
}
}
}
else
{
lean_object* x_930; lean_object* x_931; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_930 = lean_box(0);
x_931 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_931, 0, x_930);
lean_ctor_set(x_931, 1, x_4);
return x_931;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabDeclareSyntaxCat(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; uint8_t x_116; lean_object* x_218; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
x_244 = lean_unsigned_to_nat(0u);
x_245 = l_Lean_Syntax_getArg(x_1, x_244);
x_246 = l_Lean_Syntax_getOptional_x3f(x_245);
lean_dec(x_245);
if (lean_obj_tag(x_246) == 0)
{
lean_object* x_247; 
x_247 = lean_box(0);
x_218 = x_247;
goto block_243;
}
else
{
uint8_t x_248; 
x_248 = !lean_is_exclusive(x_246);
if (x_248 == 0)
{
x_218 = x_246;
goto block_243;
}
else
{
lean_object* x_249; lean_object* x_250; 
x_249 = lean_ctor_get(x_246, 0);
lean_inc(x_249);
lean_dec(x_246);
x_250 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_250, 0, x_249);
x_218 = x_250;
goto block_243;
}
}
block_110:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_inc(x_8);
x_23 = l_Array_append(lean_box(0), x_8, x_22);
lean_dec(x_22);
lean_inc(x_20);
lean_inc(x_12);
x_24 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_24, 0, x_12);
lean_ctor_set(x_24, 1, x_20);
lean_ctor_set(x_24, 2, x_8);
x_25 = lean_mk_string_unchecked("definition", 10, 10);
x_26 = lean_mk_string_unchecked("def", 3, 3);
x_27 = lean_mk_string_unchecked("declId", 6, 6);
lean_inc(x_5);
lean_inc(x_10);
lean_inc(x_6);
x_28 = l_Lean_Name_mkStr4(x_6, x_10, x_5, x_27);
x_29 = lean_mk_string_unchecked("_root_", 6, 6);
x_30 = l_Lean_Name_mkStr1(x_29);
x_31 = l_Lean_Name_append(x_30, x_13);
x_32 = l_Lean_mkIdentFrom(x_11, x_31, x_14);
lean_dec(x_11);
x_33 = lean_unsigned_to_nat(0u);
x_34 = lean_mk_empty_array_with_capacity(x_33);
x_35 = lean_box(2);
lean_inc(x_20);
x_36 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_20);
lean_ctor_set(x_36, 2, x_34);
x_37 = lean_mk_empty_array_with_capacity(x_15);
x_38 = lean_array_push(x_37, x_32);
x_39 = lean_array_push(x_38, x_36);
x_40 = lean_mk_string_unchecked("optDeclSig", 10, 10);
lean_inc(x_5);
lean_inc(x_10);
lean_inc(x_6);
x_41 = l_Lean_Name_mkStr4(x_6, x_10, x_5, x_40);
x_42 = lean_mk_string_unchecked("Term", 4, 4);
x_43 = lean_mk_string_unchecked("typeSpec", 8, 8);
lean_inc(x_42);
lean_inc(x_10);
lean_inc(x_6);
x_44 = l_Lean_Name_mkStr4(x_6, x_10, x_42, x_43);
x_45 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_12);
x_46 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_46, 0, x_12);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_mk_string_unchecked("Lean.Parser.Category", 20, 20);
x_48 = l_String_toSubstring_x27(x_47);
lean_inc(x_9);
x_49 = l_Lean_addMacroScope(x_21, x_9, x_17);
x_50 = lean_box(0);
lean_inc(x_9);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_9);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_52, 0, x_9);
x_53 = lean_box(0);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_51);
lean_ctor_set(x_55, 1, x_54);
lean_inc(x_12);
x_56 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_56, 0, x_12);
lean_ctor_set(x_56, 1, x_48);
lean_ctor_set(x_56, 2, x_49);
lean_ctor_set(x_56, 3, x_55);
lean_inc(x_12);
x_57 = l_Lean_Syntax_node2(x_12, x_44, x_46, x_56);
lean_inc(x_20);
lean_inc(x_12);
x_58 = l_Lean_Syntax_node1(x_12, x_20, x_57);
x_59 = lean_mk_string_unchecked("declValSimple", 13, 13);
lean_inc(x_5);
lean_inc(x_10);
lean_inc(x_6);
x_60 = l_Lean_Name_mkStr4(x_6, x_10, x_5, x_59);
x_61 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_12);
x_62 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_62, 0, x_12);
lean_ctor_set(x_62, 1, x_61);
x_63 = lean_mk_string_unchecked("choice", 6, 6);
x_64 = l_Lean_Name_mkStr1(x_63);
x_65 = lean_mk_string_unchecked("term{}", 6, 6);
x_66 = l_Lean_Name_mkStr1(x_65);
x_67 = lean_mk_string_unchecked("{", 1, 1);
lean_inc(x_12);
x_68 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_68, 0, x_12);
lean_ctor_set(x_68, 1, x_67);
x_69 = lean_mk_string_unchecked("}", 1, 1);
lean_inc(x_12);
x_70 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_70, 0, x_12);
lean_ctor_set(x_70, 1, x_69);
lean_inc(x_70);
lean_inc(x_68);
lean_inc(x_12);
x_71 = l_Lean_Syntax_node2(x_12, x_66, x_68, x_70);
x_72 = lean_mk_string_unchecked("structInst", 10, 10);
lean_inc(x_42);
lean_inc(x_10);
lean_inc(x_6);
x_73 = l_Lean_Name_mkStr4(x_6, x_10, x_42, x_72);
x_74 = lean_mk_string_unchecked("structInstFields", 16, 16);
lean_inc(x_42);
lean_inc(x_10);
lean_inc(x_6);
x_75 = l_Lean_Name_mkStr4(x_6, x_10, x_42, x_74);
lean_inc(x_24);
lean_inc(x_12);
x_76 = l_Lean_Syntax_node1(x_12, x_75, x_24);
x_77 = lean_mk_string_unchecked("optEllipsis", 11, 11);
lean_inc(x_10);
lean_inc(x_6);
x_78 = l_Lean_Name_mkStr4(x_6, x_10, x_42, x_77);
lean_inc(x_24);
lean_inc(x_12);
x_79 = l_Lean_Syntax_node1(x_12, x_78, x_24);
lean_inc_n(x_24, 2);
lean_inc(x_12);
x_80 = l_Lean_Syntax_node6(x_12, x_73, x_68, x_24, x_76, x_79, x_24, x_70);
lean_inc(x_12);
x_81 = l_Lean_Syntax_node2(x_12, x_64, x_71, x_80);
x_82 = lean_mk_string_unchecked("Termination", 11, 11);
x_83 = lean_mk_string_unchecked("suffix", 6, 6);
lean_inc(x_10);
lean_inc(x_6);
x_84 = l_Lean_Name_mkStr4(x_6, x_10, x_82, x_83);
lean_inc_n(x_24, 2);
lean_inc(x_12);
x_85 = l_Lean_Syntax_node2(x_12, x_84, x_24, x_24);
lean_inc(x_3);
lean_inc(x_2);
x_86 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_declareSyntaxCatQuotParser(x_16, x_2, x_3, x_18);
if (lean_obj_tag(x_86) == 0)
{
uint8_t x_87; 
x_87 = !lean_is_exclusive(x_86);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_88 = lean_ctor_get(x_86, 1);
x_89 = lean_ctor_get(x_86, 0);
lean_dec(x_89);
lean_inc(x_12);
x_90 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_90, 0, x_12);
lean_ctor_set(x_90, 1, x_20);
lean_ctor_set(x_90, 2, x_23);
x_91 = l_Lean_Name_mkStr4(x_6, x_10, x_5, x_25);
lean_inc(x_12);
lean_ctor_set_tag(x_86, 2);
lean_ctor_set(x_86, 1, x_26);
lean_ctor_set(x_86, 0, x_12);
x_92 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_92, 0, x_35);
lean_ctor_set(x_92, 1, x_28);
lean_ctor_set(x_92, 2, x_39);
lean_inc(x_24);
lean_inc(x_12);
x_93 = l_Lean_Syntax_node2(x_12, x_41, x_24, x_58);
lean_inc(x_24);
lean_inc(x_12);
x_94 = l_Lean_Syntax_node4(x_12, x_60, x_62, x_81, x_85, x_24);
lean_inc_n(x_24, 5);
lean_inc(x_12);
x_95 = l_Lean_Syntax_node6(x_12, x_19, x_90, x_24, x_24, x_24, x_24, x_24);
lean_inc(x_12);
x_96 = l_Lean_Syntax_node5(x_12, x_91, x_86, x_92, x_93, x_94, x_24);
x_97 = l_Lean_Syntax_node2(x_12, x_7, x_95, x_96);
x_98 = l_Lean_Elab_Command_elabCommand(x_97, x_2, x_3, x_88);
return x_98;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_99 = lean_ctor_get(x_86, 1);
lean_inc(x_99);
lean_dec(x_86);
lean_inc(x_12);
x_100 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_100, 0, x_12);
lean_ctor_set(x_100, 1, x_20);
lean_ctor_set(x_100, 2, x_23);
x_101 = l_Lean_Name_mkStr4(x_6, x_10, x_5, x_25);
lean_inc(x_12);
x_102 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_102, 0, x_12);
lean_ctor_set(x_102, 1, x_26);
x_103 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_103, 0, x_35);
lean_ctor_set(x_103, 1, x_28);
lean_ctor_set(x_103, 2, x_39);
lean_inc(x_24);
lean_inc(x_12);
x_104 = l_Lean_Syntax_node2(x_12, x_41, x_24, x_58);
lean_inc(x_24);
lean_inc(x_12);
x_105 = l_Lean_Syntax_node4(x_12, x_60, x_62, x_81, x_85, x_24);
lean_inc_n(x_24, 5);
lean_inc(x_12);
x_106 = l_Lean_Syntax_node6(x_12, x_19, x_100, x_24, x_24, x_24, x_24, x_24);
lean_inc(x_12);
x_107 = l_Lean_Syntax_node5(x_12, x_101, x_102, x_103, x_104, x_105, x_24);
x_108 = l_Lean_Syntax_node2(x_12, x_7, x_106, x_107);
x_109 = l_Lean_Elab_Command_elabCommand(x_108, x_2, x_3, x_99);
return x_109;
}
}
else
{
lean_dec(x_85);
lean_dec(x_81);
lean_dec(x_62);
lean_dec(x_60);
lean_dec(x_58);
lean_dec(x_41);
lean_dec(x_39);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_86;
}
}
block_217:
{
lean_object* x_117; uint8_t x_118; 
x_117 = lean_st_ref_get(x_3, x_4);
x_118 = !lean_is_exclusive(x_117);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_119 = lean_ctor_get(x_117, 0);
x_120 = lean_ctor_get(x_117, 1);
x_121 = lean_mk_string_unchecked("_parser", 7, 7);
x_122 = lean_mk_string_unchecked("Category", 8, 8);
lean_inc(x_112);
x_123 = lean_name_append_after(x_112, x_121);
x_124 = lean_mk_string_unchecked("Lean", 4, 4);
x_125 = lean_mk_string_unchecked("Parser", 6, 6);
lean_inc(x_125);
lean_inc(x_124);
x_126 = l_Lean_Name_mkStr3(x_124, x_125, x_122);
lean_inc(x_112);
lean_inc(x_126);
x_127 = l_Lean_Name_append(x_126, x_112);
x_128 = lean_ctor_get(x_119, 0);
lean_inc(x_128);
lean_dec(x_119);
lean_inc(x_127);
lean_inc(x_112);
x_129 = l_Lean_Parser_registerParserCategory(x_128, x_123, x_112, x_116, x_127, x_120);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_free_object(x_117);
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
lean_dec(x_129);
x_132 = l_Lean_setEnv___at___Lean_withEnv___at___Lean_Elab_Command_runLintersAsync_spec__0_spec__0___redArg(x_130, x_3, x_131);
x_133 = lean_ctor_get(x_132, 1);
lean_inc(x_133);
lean_dec(x_132);
x_134 = l_Lean_Elab_Command_getRef(x_2, x_3, x_133);
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_134, 1);
lean_inc(x_136);
lean_dec(x_134);
x_137 = l_Lean_Elab_Command_getCurrMacroScope(x_2, x_3, x_136);
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_137, 1);
lean_inc(x_139);
lean_dec(x_137);
x_140 = l_Lean_Elab_Command_getMainModule___redArg(x_3, x_139);
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_140, 1);
lean_inc(x_142);
lean_dec(x_140);
x_143 = lean_box(0);
x_144 = lean_unbox(x_143);
x_145 = l_Lean_SourceInfo_fromRef(x_135, x_144);
lean_dec(x_135);
x_146 = lean_mk_string_unchecked("Command", 7, 7);
x_147 = lean_mk_string_unchecked("declaration", 11, 11);
lean_inc(x_146);
lean_inc(x_125);
lean_inc(x_124);
x_148 = l_Lean_Name_mkStr4(x_124, x_125, x_146, x_147);
x_149 = lean_mk_string_unchecked("declModifiers", 13, 13);
lean_inc(x_146);
lean_inc(x_125);
lean_inc(x_124);
x_150 = l_Lean_Name_mkStr4(x_124, x_125, x_146, x_149);
x_151 = lean_mk_string_unchecked("null", 4, 4);
x_152 = l_Lean_Name_mkStr1(x_151);
x_153 = l_Array_mkArray0(lean_box(0));
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_154; 
x_154 = l_Array_empty(lean_box(0));
x_5 = x_146;
x_6 = x_124;
x_7 = x_148;
x_8 = x_153;
x_9 = x_126;
x_10 = x_125;
x_11 = x_114;
x_12 = x_145;
x_13 = x_127;
x_14 = x_115;
x_15 = x_111;
x_16 = x_112;
x_17 = x_138;
x_18 = x_142;
x_19 = x_150;
x_20 = x_152;
x_21 = x_141;
x_22 = x_154;
goto block_110;
}
else
{
lean_object* x_155; lean_object* x_156; 
x_155 = lean_ctor_get(x_113, 0);
lean_inc(x_155);
lean_dec(x_113);
x_156 = l_Array_mkArray1___redArg(x_155);
x_5 = x_146;
x_6 = x_124;
x_7 = x_148;
x_8 = x_153;
x_9 = x_126;
x_10 = x_125;
x_11 = x_114;
x_12 = x_145;
x_13 = x_127;
x_14 = x_115;
x_15 = x_111;
x_16 = x_112;
x_17 = x_138;
x_18 = x_142;
x_19 = x_150;
x_20 = x_152;
x_21 = x_141;
x_22 = x_156;
goto block_110;
}
}
else
{
uint8_t x_157; 
lean_dec(x_127);
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_124);
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_3);
x_157 = !lean_is_exclusive(x_129);
if (x_157 == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_158 = lean_ctor_get(x_129, 0);
x_159 = lean_ctor_get(x_2, 6);
lean_inc(x_159);
lean_dec(x_2);
x_160 = lean_io_error_to_string(x_158);
x_161 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_161, 0, x_160);
x_162 = l_Lean_MessageData_ofFormat(x_161);
lean_ctor_set(x_117, 1, x_162);
lean_ctor_set(x_117, 0, x_159);
lean_ctor_set(x_129, 0, x_117);
return x_129;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_163 = lean_ctor_get(x_129, 0);
x_164 = lean_ctor_get(x_129, 1);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_129);
x_165 = lean_ctor_get(x_2, 6);
lean_inc(x_165);
lean_dec(x_2);
x_166 = lean_io_error_to_string(x_163);
x_167 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_167, 0, x_166);
x_168 = l_Lean_MessageData_ofFormat(x_167);
lean_ctor_set(x_117, 1, x_168);
lean_ctor_set(x_117, 0, x_165);
x_169 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_169, 0, x_117);
lean_ctor_set(x_169, 1, x_164);
return x_169;
}
}
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_170 = lean_ctor_get(x_117, 0);
x_171 = lean_ctor_get(x_117, 1);
lean_inc(x_171);
lean_inc(x_170);
lean_dec(x_117);
x_172 = lean_mk_string_unchecked("_parser", 7, 7);
x_173 = lean_mk_string_unchecked("Category", 8, 8);
lean_inc(x_112);
x_174 = lean_name_append_after(x_112, x_172);
x_175 = lean_mk_string_unchecked("Lean", 4, 4);
x_176 = lean_mk_string_unchecked("Parser", 6, 6);
lean_inc(x_176);
lean_inc(x_175);
x_177 = l_Lean_Name_mkStr3(x_175, x_176, x_173);
lean_inc(x_112);
lean_inc(x_177);
x_178 = l_Lean_Name_append(x_177, x_112);
x_179 = lean_ctor_get(x_170, 0);
lean_inc(x_179);
lean_dec(x_170);
lean_inc(x_178);
lean_inc(x_112);
x_180 = l_Lean_Parser_registerParserCategory(x_179, x_174, x_112, x_116, x_178, x_171);
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; uint8_t x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_180, 1);
lean_inc(x_182);
lean_dec(x_180);
x_183 = l_Lean_setEnv___at___Lean_withEnv___at___Lean_Elab_Command_runLintersAsync_spec__0_spec__0___redArg(x_181, x_3, x_182);
x_184 = lean_ctor_get(x_183, 1);
lean_inc(x_184);
lean_dec(x_183);
x_185 = l_Lean_Elab_Command_getRef(x_2, x_3, x_184);
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_185, 1);
lean_inc(x_187);
lean_dec(x_185);
x_188 = l_Lean_Elab_Command_getCurrMacroScope(x_2, x_3, x_187);
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_188, 1);
lean_inc(x_190);
lean_dec(x_188);
x_191 = l_Lean_Elab_Command_getMainModule___redArg(x_3, x_190);
x_192 = lean_ctor_get(x_191, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_191, 1);
lean_inc(x_193);
lean_dec(x_191);
x_194 = lean_box(0);
x_195 = lean_unbox(x_194);
x_196 = l_Lean_SourceInfo_fromRef(x_186, x_195);
lean_dec(x_186);
x_197 = lean_mk_string_unchecked("Command", 7, 7);
x_198 = lean_mk_string_unchecked("declaration", 11, 11);
lean_inc(x_197);
lean_inc(x_176);
lean_inc(x_175);
x_199 = l_Lean_Name_mkStr4(x_175, x_176, x_197, x_198);
x_200 = lean_mk_string_unchecked("declModifiers", 13, 13);
lean_inc(x_197);
lean_inc(x_176);
lean_inc(x_175);
x_201 = l_Lean_Name_mkStr4(x_175, x_176, x_197, x_200);
x_202 = lean_mk_string_unchecked("null", 4, 4);
x_203 = l_Lean_Name_mkStr1(x_202);
x_204 = l_Array_mkArray0(lean_box(0));
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_205; 
x_205 = l_Array_empty(lean_box(0));
x_5 = x_197;
x_6 = x_175;
x_7 = x_199;
x_8 = x_204;
x_9 = x_177;
x_10 = x_176;
x_11 = x_114;
x_12 = x_196;
x_13 = x_178;
x_14 = x_115;
x_15 = x_111;
x_16 = x_112;
x_17 = x_189;
x_18 = x_193;
x_19 = x_201;
x_20 = x_203;
x_21 = x_192;
x_22 = x_205;
goto block_110;
}
else
{
lean_object* x_206; lean_object* x_207; 
x_206 = lean_ctor_get(x_113, 0);
lean_inc(x_206);
lean_dec(x_113);
x_207 = l_Array_mkArray1___redArg(x_206);
x_5 = x_197;
x_6 = x_175;
x_7 = x_199;
x_8 = x_204;
x_9 = x_177;
x_10 = x_176;
x_11 = x_114;
x_12 = x_196;
x_13 = x_178;
x_14 = x_115;
x_15 = x_111;
x_16 = x_112;
x_17 = x_189;
x_18 = x_193;
x_19 = x_201;
x_20 = x_203;
x_21 = x_192;
x_22 = x_207;
goto block_110;
}
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
lean_dec(x_178);
lean_dec(x_177);
lean_dec(x_176);
lean_dec(x_175);
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_3);
x_208 = lean_ctor_get(x_180, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_180, 1);
lean_inc(x_209);
if (lean_is_exclusive(x_180)) {
 lean_ctor_release(x_180, 0);
 lean_ctor_release(x_180, 1);
 x_210 = x_180;
} else {
 lean_dec_ref(x_180);
 x_210 = lean_box(0);
}
x_211 = lean_ctor_get(x_2, 6);
lean_inc(x_211);
lean_dec(x_2);
x_212 = lean_io_error_to_string(x_208);
x_213 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_213, 0, x_212);
x_214 = l_Lean_MessageData_ofFormat(x_213);
x_215 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_215, 0, x_211);
lean_ctor_set(x_215, 1, x_214);
if (lean_is_scalar(x_210)) {
 x_216 = lean_alloc_ctor(1, 2, 0);
} else {
 x_216 = x_210;
}
lean_ctor_set(x_216, 0, x_215);
lean_ctor_set(x_216, 1, x_209);
return x_216;
}
}
}
block_243:
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; uint8_t x_224; lean_object* x_225; 
x_219 = lean_unsigned_to_nat(2u);
x_220 = l_Lean_Syntax_getArg(x_1, x_219);
x_221 = l_Lean_Syntax_getId(x_220);
x_222 = lean_unsigned_to_nat(3u);
x_223 = l_Lean_Syntax_getArg(x_1, x_222);
x_224 = l_Lean_Syntax_isNone(x_223);
x_225 = lean_box(1);
if (x_224 == 0)
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; uint8_t x_233; 
x_226 = l_Lean_Syntax_getArg(x_223, x_222);
lean_dec(x_223);
x_227 = l_Lean_Syntax_getKind(x_226);
x_228 = lean_mk_string_unchecked("Lean", 4, 4);
x_229 = lean_mk_string_unchecked("Parser", 6, 6);
x_230 = lean_mk_string_unchecked("Command", 7, 7);
x_231 = lean_mk_string_unchecked("catBehaviorBoth", 15, 15);
x_232 = l_Lean_Name_mkStr4(x_228, x_229, x_230, x_231);
x_233 = lean_name_eq(x_227, x_232);
lean_dec(x_232);
lean_dec(x_227);
if (x_233 == 0)
{
lean_object* x_234; uint8_t x_235; uint8_t x_236; 
x_234 = lean_box(1);
x_235 = lean_unbox(x_225);
x_236 = lean_unbox(x_234);
x_111 = x_219;
x_112 = x_221;
x_113 = x_218;
x_114 = x_220;
x_115 = x_235;
x_116 = x_236;
goto block_217;
}
else
{
lean_object* x_237; uint8_t x_238; uint8_t x_239; 
x_237 = lean_box(2);
x_238 = lean_unbox(x_225);
x_239 = lean_unbox(x_237);
x_111 = x_219;
x_112 = x_221;
x_113 = x_218;
x_114 = x_220;
x_115 = x_238;
x_116 = x_239;
goto block_217;
}
}
else
{
lean_object* x_240; uint8_t x_241; uint8_t x_242; 
lean_dec(x_223);
x_240 = lean_box(0);
x_241 = lean_unbox(x_225);
x_242 = lean_unbox(x_240);
x_111 = x_219;
x_112 = x_221;
x_113 = x_218;
x_114 = x_220;
x_115 = x_241;
x_116 = x_242;
goto block_217;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabDeclareSyntaxCat___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_elabDeclareSyntaxCat(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabDeclareSyntaxCat__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Command", 7, 7);
x_6 = lean_mk_string_unchecked("syntaxCat", 9, 9);
lean_inc(x_5);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("Elab", 4, 4);
x_9 = lean_mk_string_unchecked("elabDeclareSyntaxCat", 20, 20);
x_10 = l_Lean_Name_mkStr4(x_3, x_8, x_5, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabDeclareSyntaxCat___boxed), 4, 0);
x_12 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_10, x_11, x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabDeclareSyntaxCat_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("Command", 7, 7);
x_5 = lean_mk_string_unchecked("elabDeclareSyntaxCat", 20, 20);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(281u);
x_8 = lean_unsigned_to_nat(34u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(296u);
x_11 = lean_unsigned_to_nat(17u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_11);
x_14 = lean_unsigned_to_nat(38u);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_unsigned_to_nat(58u);
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Command_mkNameFromParserSyntax_visit_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Lean_Elab_Command_mkNameFromParserSyntax_visit(x_6, x_4);
lean_dec(x_6);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_usize_of_nat(x_8);
x_10 = lean_usize_add(x_2, x_9);
x_2 = x_10;
x_4 = x_7;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___Lean_Elab_Command_mkNameFromParserSyntax_visit_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint8_t x_11; 
x_11 = lean_string_utf8_at_end(x_2, x_1);
if (x_11 == 0)
{
uint32_t x_12; uint8_t x_13; uint8_t x_15; lean_object* x_23; uint32_t x_24; uint8_t x_25; 
x_12 = lean_string_utf8_get(x_2, x_1);
x_23 = lean_unsigned_to_nat(32u);
x_24 = l_Char_ofNat(x_23);
x_25 = l_instDecidableEqChar(x_12, x_24);
if (x_25 == 0)
{
lean_object* x_26; uint32_t x_27; uint8_t x_28; 
x_26 = lean_unsigned_to_nat(9u);
x_27 = l_Char_ofNat(x_26);
x_28 = l_instDecidableEqChar(x_12, x_27);
x_15 = x_28;
goto block_22;
}
else
{
x_15 = x_25;
goto block_22;
}
block_14:
{
if (x_13 == 0)
{
x_3 = x_12;
goto block_7;
}
else
{
goto block_10;
}
}
block_22:
{
if (x_15 == 0)
{
lean_object* x_16; uint32_t x_17; uint8_t x_18; 
x_16 = lean_unsigned_to_nat(13u);
x_17 = l_Char_ofNat(x_16);
x_18 = l_instDecidableEqChar(x_12, x_17);
if (x_18 == 0)
{
lean_object* x_19; uint32_t x_20; uint8_t x_21; 
x_19 = lean_unsigned_to_nat(10u);
x_20 = l_Char_ofNat(x_19);
x_21 = l_instDecidableEqChar(x_12, x_20);
x_13 = x_21;
goto block_14;
}
else
{
x_13 = x_18;
goto block_14;
}
}
else
{
goto block_10;
}
}
}
else
{
lean_dec(x_1);
return x_2;
}
block_7:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_string_utf8_set(x_2, x_1, x_3);
x_5 = lean_string_utf8_next(x_4, x_1);
lean_dec(x_1);
x_1 = x_5;
x_2 = x_4;
goto _start;
}
block_10:
{
lean_object* x_8; uint32_t x_9; 
x_8 = lean_unsigned_to_nat(95u);
x_9 = l_Char_ofNat(x_8);
x_3 = x_9;
goto block_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkNameFromParserSyntax_visit(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_isStrLit_x3f(x_1);
if (lean_obj_tag(x_3) == 0)
{
switch (lean_obj_tag(x_1)) {
case 0:
{
return x_2;
}
case 1:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("Parser", 6, 6);
x_8 = lean_mk_string_unchecked("Syntax", 6, 6);
x_9 = lean_mk_string_unchecked("cat", 3, 3);
x_10 = l_Lean_Name_mkStr4(x_6, x_7, x_8, x_9);
x_11 = lean_name_eq(x_4, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_get_size(x_5);
x_14 = lean_nat_dec_lt(x_12, x_13);
if (x_14 == 0)
{
lean_dec(x_13);
return x_2;
}
else
{
uint8_t x_15; 
x_15 = lean_nat_dec_le(x_13, x_13);
if (x_15 == 0)
{
lean_dec(x_13);
return x_2;
}
else
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = lean_usize_of_nat(x_12);
x_17 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_18 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_Command_mkNameFromParserSyntax_visit_spec__0(x_5, x_16, x_17, x_2);
return x_18;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_mk_string_unchecked("_", 1, 1);
x_20 = lean_string_append(x_2, x_19);
lean_dec(x_19);
return x_20;
}
}
default: 
{
return x_2;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint32_t x_28; uint32_t x_29; lean_object* x_30; lean_object* x_31; 
x_21 = lean_ctor_get(x_3, 0);
lean_inc(x_21);
lean_dec(x_3);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_string_utf8_byte_size(x_21);
x_24 = l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(x_21, x_23, x_22);
x_25 = l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(x_21, x_24, x_23);
x_26 = lean_string_utf8_extract(x_21, x_24, x_25);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_21);
x_27 = l_String_mapAux___at___Lean_Elab_Command_mkNameFromParserSyntax_visit_spec__1(x_22, x_26);
x_28 = lean_string_utf8_get(x_27, x_22);
x_29 = l_Char_toUpper(x_28);
x_30 = lean_string_utf8_set(x_27, x_22, x_29);
x_31 = lean_string_append(x_2, x_30);
lean_dec(x_30);
return x_31;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Command_mkNameFromParserSyntax_visit_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_Command_mkNameFromParserSyntax_visit_spec__0(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkNameFromParserSyntax_visit___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Command_mkNameFromParserSyntax_visit(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkNameFromParserSyntax_appendCatName(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_string_append(x_3, x_2);
return x_4;
}
else
{
lean_dec(x_1);
lean_inc(x_2);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkNameFromParserSyntax_appendCatName___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Command_mkNameFromParserSyntax_appendCatName(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkNameFromParserSyntax(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_mk_string_unchecked("", 0, 0);
x_6 = l_Lean_Elab_Command_mkNameFromParserSyntax_visit(x_2, x_5);
x_7 = l_Lean_Elab_Command_mkNameFromParserSyntax_appendCatName(x_1, x_6);
lean_dec(x_6);
x_8 = lean_box(0);
x_9 = l_Lean_Name_str___override(x_8, x_7);
x_10 = l_Lean_Elab_mkUnusedBaseName(x_9, x_3, x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkNameFromParserSyntax___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_mkNameFromParserSyntax(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_isAtomLikeSyntax(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
lean_inc(x_1);
x_2 = l_Lean_Syntax_getKind(x_1);
x_3 = lean_mk_string_unchecked("null", 4, 4);
x_4 = l_Lean_Name_mkStr1(x_3);
x_5 = lean_name_eq(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_mk_string_unchecked("choice", 6, 6);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = lean_name_eq(x_2, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_9 = lean_mk_string_unchecked("Lean", 4, 4);
x_10 = lean_mk_string_unchecked("Parser", 6, 6);
x_11 = lean_mk_string_unchecked("Syntax", 6, 6);
x_12 = lean_mk_string_unchecked("paren", 5, 5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_13 = l_Lean_Name_mkStr4(x_9, x_10, x_11, x_12);
x_14 = lean_name_eq(x_2, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
lean_dec(x_1);
x_15 = lean_mk_string_unchecked("atom", 4, 4);
x_16 = l_Lean_Name_mkStr4(x_9, x_10, x_11, x_15);
x_17 = lean_name_eq(x_2, x_16);
lean_dec(x_16);
lean_dec(x_2);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_2);
x_18 = lean_unsigned_to_nat(1u);
x_19 = l_Lean_Syntax_getArg(x_1, x_18);
lean_dec(x_1);
x_1 = x_19;
goto _start;
}
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_2);
x_21 = lean_unsigned_to_nat(0u);
x_22 = l_Lean_Syntax_getArg(x_1, x_21);
lean_dec(x_1);
x_1 = x_22;
goto _start;
}
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
lean_dec(x_2);
x_24 = lean_unsigned_to_nat(0u);
x_25 = l_Lean_Syntax_getArg(x_1, x_24);
x_26 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_isAtomLikeSyntax(x_25);
if (x_26 == 0)
{
lean_dec(x_1);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = l_Lean_Syntax_getNumArgs(x_1);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_sub(x_27, x_28);
lean_dec(x_27);
x_30 = l_Lean_Syntax_getArg(x_1, x_29);
lean_dec(x_29);
lean_dec(x_1);
x_1 = x_30;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_isAtomLikeSyntax___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_isAtomLikeSyntax(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind___at___Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___Lean_Elab_Command_resolveSyntaxKind_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_1);
x_10 = l_Lean_Parser_isValidSyntaxNodeKind(x_9, x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_free_object(x_5);
lean_dec(x_1);
x_11 = lean_mk_string_unchecked("failed", 6, 6);
x_12 = l_Lean_stringToMessageData(x_11);
lean_dec(x_11);
x_13 = l_Lean_throwError___at_____private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing_spec__0___redArg(x_12, x_2, x_3, x_8);
return x_13;
}
else
{
lean_dec(x_2);
lean_ctor_set(x_5, 0, x_1);
return x_5;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_5, 0);
x_15 = lean_ctor_get(x_5, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_5);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_1);
x_17 = l_Lean_Parser_isValidSyntaxNodeKind(x_16, x_1);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_1);
x_18 = lean_mk_string_unchecked("failed", 6, 6);
x_19 = l_Lean_stringToMessageData(x_18);
lean_dec(x_18);
x_20 = l_Lean_throwError___at_____private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing_spec__0___redArg(x_19, x_2, x_3, x_15);
return x_20;
}
else
{
lean_object* x_21; 
lean_dec(x_2);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_15);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___Lean_Elab_Command_resolveSyntaxKind_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_checkSyntaxNodeKind___at___Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___Lean_Elab_Command_resolveSyntaxKind_spec__0_spec__0(x_1, x_3, x_4, x_5);
return x_6;
}
case 1:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_inc(x_1);
x_8 = l_Lean_Name_append(x_2, x_1);
lean_inc(x_3);
x_9 = l_Lean_Elab_checkSyntaxNodeKind___at___Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___Lean_Elab_Command_resolveSyntaxKind_spec__0_spec__0(x_8, x_3, x_4, x_5);
if (lean_obj_tag(x_9) == 0)
{
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
x_12 = l_Lean_Exception_isInterrupt(x_10);
lean_dec(x_10);
if (x_12 == 0)
{
lean_dec(x_9);
x_2 = x_7;
x_5 = x_11;
goto _start;
}
else
{
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
}
default: 
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_mk_string_unchecked("failed", 6, 6);
x_15 = l_Lean_stringToMessageData(x_14);
lean_dec(x_14);
x_16 = l_Lean_throwError___at_____private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing_spec__0___redArg(x_15, x_3, x_4, x_5);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_resolveSyntaxKind(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Elab_Command_getScope___redArg(x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = lean_ctor_get(x_7, 2);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_2);
lean_inc(x_1);
x_10 = l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___Lean_Elab_Command_resolveSyntaxKind_spec__0(x_1, x_9, x_2, x_3, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_free_object(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
x_13 = l_Lean_Exception_isInterrupt(x_11);
lean_dec(x_11);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_15 = lean_ctor_get(x_10, 1);
lean_dec(x_15);
x_16 = lean_ctor_get(x_10, 0);
lean_dec(x_16);
x_17 = lean_mk_string_unchecked("invalid syntax node kind '", 26, 26);
x_18 = l_Lean_stringToMessageData(x_17);
lean_dec(x_17);
x_19 = l_Lean_MessageData_ofName(x_1);
lean_ctor_set_tag(x_10, 7);
lean_ctor_set(x_10, 1, x_19);
lean_ctor_set(x_10, 0, x_18);
x_20 = lean_mk_string_unchecked("'", 1, 1);
x_21 = l_Lean_stringToMessageData(x_20);
lean_dec(x_20);
lean_ctor_set_tag(x_5, 7);
lean_ctor_set(x_5, 1, x_21);
lean_ctor_set(x_5, 0, x_10);
x_22 = l_Lean_throwError___at_____private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing_spec__0___redArg(x_5, x_2, x_3, x_12);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_10);
x_23 = lean_mk_string_unchecked("invalid syntax node kind '", 26, 26);
x_24 = l_Lean_stringToMessageData(x_23);
lean_dec(x_23);
x_25 = l_Lean_MessageData_ofName(x_1);
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_mk_string_unchecked("'", 1, 1);
x_28 = l_Lean_stringToMessageData(x_27);
lean_dec(x_27);
lean_ctor_set_tag(x_5, 7);
lean_ctor_set(x_5, 1, x_28);
lean_ctor_set(x_5, 0, x_26);
x_29 = l_Lean_throwError___at_____private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing_spec__0___redArg(x_5, x_2, x_3, x_12);
return x_29;
}
}
else
{
lean_dec(x_12);
lean_free_object(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_5, 0);
x_31 = lean_ctor_get(x_5, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_5);
x_32 = lean_ctor_get(x_30, 2);
lean_inc(x_32);
lean_dec(x_30);
lean_inc(x_2);
lean_inc(x_1);
x_33 = l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___Lean_Elab_Command_resolveSyntaxKind_spec__0(x_1, x_32, x_2, x_3, x_31);
if (lean_obj_tag(x_33) == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
x_36 = l_Lean_Exception_isInterrupt(x_34);
lean_dec(x_34);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_37 = x_33;
} else {
 lean_dec_ref(x_33);
 x_37 = lean_box(0);
}
x_38 = lean_mk_string_unchecked("invalid syntax node kind '", 26, 26);
x_39 = l_Lean_stringToMessageData(x_38);
lean_dec(x_38);
x_40 = l_Lean_MessageData_ofName(x_1);
if (lean_is_scalar(x_37)) {
 x_41 = lean_alloc_ctor(7, 2, 0);
} else {
 x_41 = x_37;
 lean_ctor_set_tag(x_41, 7);
}
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_mk_string_unchecked("'", 1, 1);
x_43 = l_Lean_stringToMessageData(x_42);
lean_dec(x_42);
x_44 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Lean_throwError___at_____private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing_spec__0___redArg(x_44, x_2, x_3, x_35);
return x_45;
}
else
{
lean_dec(x_35);
lean_dec(x_2);
lean_dec(x_1);
return x_33;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKind___at___Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___Lean_Elab_Command_resolveSyntaxKind_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_checkSyntaxNodeKind___at___Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___Lean_Elab_Command_resolveSyntaxKind_spec__0_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___Lean_Elab_Command_resolveSyntaxKind_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___Lean_Elab_Command_resolveSyntaxKind_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_resolveSyntaxKind___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_resolveSyntaxKind(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Command_isLocalAttrKind(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Term", 4, 4);
x_5 = lean_mk_string_unchecked("attrKind", 8, 8);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
lean_inc(x_1);
x_7 = l_Lean_Syntax_isOfKind(x_1, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
lean_dec(x_1);
x_10 = lean_unsigned_to_nat(1u);
lean_inc(x_9);
x_11 = l_Lean_Syntax_matchesNull(x_9, x_10);
if (x_11 == 0)
{
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = l_Lean_Syntax_getArg(x_9, x_8);
lean_dec(x_9);
x_13 = lean_mk_string_unchecked("local", 5, 5);
x_14 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_13);
x_15 = l_Lean_Syntax_isOfKind(x_12, x_14);
lean_dec(x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_isLocalAttrKind___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Command_isLocalAttrKind(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_addMacroScopeIfLocal___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_addMacroScope(x_1, x_2, x_4);
x_6 = lean_apply_2(x_3, lean_box(0), x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_addMacroScopeIfLocal___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_alloc_closure((void*)(l_Lean_Elab_Command_addMacroScopeIfLocal___redArg___lam__0), 4, 3);
lean_closure_set(x_6, 0, x_5);
lean_closure_set(x_6, 1, x_1);
lean_closure_set(x_6, 2, x_2);
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_7, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_addMacroScopeIfLocal___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_9; uint8_t x_17; 
x_17 = l_Lean_Elab_Command_isLocalAttrKind(x_4);
if (x_17 == 0)
{
x_9 = x_17;
goto block_16;
}
else
{
uint8_t x_18; 
x_18 = l_Lean_Name_hasMacroScopes(x_3);
if (x_18 == 0)
{
x_9 = x_17;
goto block_16;
}
else
{
lean_dec(x_1);
goto block_8;
}
}
block_8:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_apply_2(x_6, lean_box(0), x_3);
return x_7;
}
block_16:
{
if (x_9 == 0)
{
lean_dec(x_1);
goto block_8;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
lean_dec(x_2);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
lean_inc(x_10);
x_14 = lean_alloc_closure((void*)(l_Lean_Elab_Command_addMacroScopeIfLocal___redArg___lam__1), 5, 4);
lean_closure_set(x_14, 0, x_3);
lean_closure_set(x_14, 1, x_13);
lean_closure_set(x_14, 2, x_1);
lean_closure_set(x_14, 3, x_10);
x_15 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_11, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_addMacroScopeIfLocal(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Command_addMacroScopeIfLocal___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Command_elabSyntax_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_6 = lean_box(0);
lean_inc(x_3);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = lean_array_uget(x_3, x_2);
lean_dec(x_3);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Command_addMacroScopeIfLocal___at___Lean_Elab_Command_elabSyntax_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; uint8_t x_20; 
x_20 = l_Lean_Elab_Command_isLocalAttrKind(x_2);
if (x_20 == 0)
{
x_6 = x_20;
goto block_19;
}
else
{
uint8_t x_21; 
x_21 = l_Lean_Name_hasMacroScopes(x_1);
if (x_21 == 0)
{
x_6 = x_20;
goto block_19;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_5);
return x_22;
}
}
block_19:
{
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = l_Lean_Elab_Command_getMainModule___redArg(x_4, x_5);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Elab_Command_getCurrMacroScope(x_3, x_4, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = l_Lean_addMacroScope(x_9, x_1, x_13);
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
x_17 = l_Lean_addMacroScope(x_9, x_1, x_15);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSyntax___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Elab_Command_getRef(x_1, x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_box(0);
x_8 = lean_unbox(x_7);
x_9 = l_Lean_SourceInfo_fromRef(x_6, x_8);
lean_dec(x_6);
lean_ctor_set(x_4, 0, x_9);
return x_4;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_4);
x_12 = lean_box(0);
x_13 = lean_unbox(x_12);
x_14 = l_Lean_SourceInfo_fromRef(x_10, x_13);
lean_dec(x_10);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSyntax___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Term_toParserDescr(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSyntax(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_289; lean_object* x_290; uint8_t x_291; 
x_27 = lean_mk_string_unchecked("Lean", 4, 4);
x_28 = lean_mk_string_unchecked("Parser", 6, 6);
x_96 = lean_mk_string_unchecked("Command", 7, 7);
x_289 = lean_mk_string_unchecked("syntax", 6, 6);
lean_inc(x_96);
lean_inc(x_28);
lean_inc(x_27);
x_290 = l_Lean_Name_mkStr4(x_27, x_28, x_96, x_289);
lean_inc(x_1);
x_291 = l_Lean_Syntax_isOfKind(x_1, x_290);
lean_dec(x_290);
if (x_291 == 0)
{
lean_object* x_292; 
lean_dec(x_96);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_1);
x_292 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_292;
}
else
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; uint8_t x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_714; uint8_t x_715; 
x_346 = lean_unsigned_to_nat(0u);
x_714 = l_Lean_Syntax_getArg(x_1, x_346);
x_715 = l_Lean_Syntax_isNone(x_714);
if (x_715 == 0)
{
lean_object* x_716; uint8_t x_717; 
x_716 = lean_unsigned_to_nat(1u);
lean_inc(x_714);
x_717 = l_Lean_Syntax_matchesNull(x_714, x_716);
if (x_717 == 0)
{
lean_object* x_718; 
lean_dec(x_714);
lean_dec(x_96);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_1);
x_718 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_718;
}
else
{
lean_object* x_719; lean_object* x_720; lean_object* x_721; uint8_t x_722; 
x_719 = l_Lean_Syntax_getArg(x_714, x_346);
lean_dec(x_714);
x_720 = lean_mk_string_unchecked("docComment", 10, 10);
lean_inc(x_96);
lean_inc(x_28);
lean_inc(x_27);
x_721 = l_Lean_Name_mkStr4(x_27, x_28, x_96, x_720);
lean_inc(x_719);
x_722 = l_Lean_Syntax_isOfKind(x_719, x_721);
lean_dec(x_721);
if (x_722 == 0)
{
lean_object* x_723; 
lean_dec(x_719);
lean_dec(x_96);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_1);
x_723 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_723;
}
else
{
lean_object* x_724; 
x_724 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_724, 0, x_719);
x_694 = x_724;
x_695 = x_2;
x_696 = x_3;
x_697 = x_4;
goto block_713;
}
}
}
else
{
lean_object* x_725; 
lean_dec(x_714);
x_725 = lean_box(0);
x_694 = x_725;
x_695 = x_2;
x_696 = x_3;
x_697 = x_4;
goto block_713;
}
block_345:
{
lean_object* x_309; 
x_309 = lean_mk_string_unchecked(",", 1, 1);
if (lean_obj_tag(x_303) == 0)
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; 
x_310 = l_Lean_Elab_Command_elabSyntax___lam__0(x_304, x_296, x_301);
x_311 = lean_ctor_get(x_310, 0);
lean_inc(x_311);
x_312 = lean_ctor_get(x_310, 1);
lean_inc(x_312);
lean_dec(x_310);
x_313 = l_Lean_Elab_Command_getCurrMacroScope(x_304, x_296, x_312);
x_314 = lean_ctor_get(x_313, 0);
lean_inc(x_314);
x_315 = lean_ctor_get(x_313, 1);
lean_inc(x_315);
lean_dec(x_313);
x_316 = l_Lean_Elab_Command_getMainModule___redArg(x_296, x_315);
x_317 = lean_ctor_get(x_316, 0);
lean_inc(x_317);
x_318 = lean_ctor_get(x_316, 1);
lean_inc(x_318);
lean_dec(x_316);
x_319 = lean_mk_string_unchecked("declaration", 11, 11);
lean_inc(x_96);
lean_inc(x_28);
lean_inc(x_27);
x_320 = l_Lean_Name_mkStr4(x_27, x_28, x_96, x_319);
x_321 = lean_mk_string_unchecked("declModifiers", 13, 13);
lean_inc(x_96);
lean_inc(x_28);
lean_inc(x_27);
x_322 = l_Lean_Name_mkStr4(x_27, x_28, x_96, x_321);
x_323 = l_Array_mkArray0(lean_box(0));
if (lean_obj_tag(x_307) == 0)
{
lean_object* x_324; 
x_324 = l_Array_empty(lean_box(0));
x_97 = x_293;
x_98 = x_309;
x_99 = x_320;
x_100 = x_294;
x_101 = x_295;
x_102 = x_296;
x_103 = x_318;
x_104 = x_297;
x_105 = x_298;
x_106 = x_308;
x_107 = x_299;
x_108 = x_300;
x_109 = x_302;
x_110 = x_317;
x_111 = x_304;
x_112 = x_305;
x_113 = x_323;
x_114 = x_306;
x_115 = x_314;
x_116 = x_311;
x_117 = x_322;
x_118 = x_324;
goto block_192;
}
else
{
lean_object* x_325; lean_object* x_326; 
x_325 = lean_ctor_get(x_307, 0);
lean_inc(x_325);
lean_dec(x_307);
x_326 = l_Array_mkArray1___redArg(x_325);
x_97 = x_293;
x_98 = x_309;
x_99 = x_320;
x_100 = x_294;
x_101 = x_295;
x_102 = x_296;
x_103 = x_318;
x_104 = x_297;
x_105 = x_298;
x_106 = x_308;
x_107 = x_299;
x_108 = x_300;
x_109 = x_302;
x_110 = x_317;
x_111 = x_304;
x_112 = x_305;
x_113 = x_323;
x_114 = x_306;
x_115 = x_314;
x_116 = x_311;
x_117 = x_322;
x_118 = x_326;
goto block_192;
}
}
else
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; 
x_327 = lean_ctor_get(x_303, 0);
lean_inc(x_327);
lean_dec(x_303);
x_328 = l_Lean_Elab_Command_elabSyntax___lam__0(x_304, x_296, x_301);
x_329 = lean_ctor_get(x_328, 0);
lean_inc(x_329);
x_330 = lean_ctor_get(x_328, 1);
lean_inc(x_330);
lean_dec(x_328);
x_331 = l_Lean_Elab_Command_getCurrMacroScope(x_304, x_296, x_330);
x_332 = lean_ctor_get(x_331, 0);
lean_inc(x_332);
x_333 = lean_ctor_get(x_331, 1);
lean_inc(x_333);
lean_dec(x_331);
x_334 = l_Lean_Elab_Command_getMainModule___redArg(x_296, x_333);
x_335 = lean_ctor_get(x_334, 0);
lean_inc(x_335);
x_336 = lean_ctor_get(x_334, 1);
lean_inc(x_336);
lean_dec(x_334);
x_337 = lean_mk_string_unchecked("declaration", 11, 11);
lean_inc(x_96);
lean_inc(x_28);
lean_inc(x_27);
x_338 = l_Lean_Name_mkStr4(x_27, x_28, x_96, x_337);
x_339 = lean_mk_string_unchecked("declModifiers", 13, 13);
lean_inc(x_96);
lean_inc(x_28);
lean_inc(x_27);
x_340 = l_Lean_Name_mkStr4(x_27, x_28, x_96, x_339);
x_341 = l_Array_mkArray0(lean_box(0));
if (lean_obj_tag(x_307) == 0)
{
lean_object* x_342; 
x_342 = l_Array_empty(lean_box(0));
x_193 = x_293;
x_194 = x_309;
x_195 = x_295;
x_196 = x_294;
x_197 = x_296;
x_198 = x_332;
x_199 = x_297;
x_200 = x_298;
x_201 = x_308;
x_202 = x_299;
x_203 = x_340;
x_204 = x_335;
x_205 = x_300;
x_206 = x_341;
x_207 = x_302;
x_208 = x_327;
x_209 = x_338;
x_210 = x_304;
x_211 = x_305;
x_212 = x_329;
x_213 = x_306;
x_214 = x_336;
x_215 = x_342;
goto block_288;
}
else
{
lean_object* x_343; lean_object* x_344; 
x_343 = lean_ctor_get(x_307, 0);
lean_inc(x_343);
lean_dec(x_307);
x_344 = l_Array_mkArray1___redArg(x_343);
x_193 = x_293;
x_194 = x_309;
x_195 = x_295;
x_196 = x_294;
x_197 = x_296;
x_198 = x_332;
x_199 = x_297;
x_200 = x_298;
x_201 = x_308;
x_202 = x_299;
x_203 = x_340;
x_204 = x_335;
x_205 = x_300;
x_206 = x_341;
x_207 = x_302;
x_208 = x_327;
x_209 = x_338;
x_210 = x_304;
x_211 = x_305;
x_212 = x_329;
x_213 = x_306;
x_214 = x_336;
x_215 = x_344;
goto block_288;
}
}
}
block_406:
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; uint8_t x_373; 
x_367 = l_Lean_Elab_Command_getRef(x_360, x_351, x_352);
x_368 = lean_ctor_get(x_367, 0);
lean_inc(x_368);
x_369 = lean_ctor_get(x_367, 1);
lean_inc(x_369);
lean_dec(x_367);
x_370 = l_Lean_Elab_Command_getCurrMacroScope(x_360, x_351, x_369);
x_371 = lean_ctor_get(x_370, 1);
lean_inc(x_371);
lean_dec(x_370);
x_372 = l_Lean_Elab_Command_getMainModule___redArg(x_351, x_371);
x_373 = !lean_is_exclusive(x_372);
if (x_373 == 0)
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; 
x_374 = lean_ctor_get(x_372, 1);
x_375 = lean_ctor_get(x_372, 0);
lean_dec(x_375);
x_376 = l_Lean_SourceInfo_fromRef(x_368, x_355);
lean_dec(x_368);
x_377 = lean_mk_string_unchecked("attrInstance", 12, 12);
lean_inc(x_349);
lean_inc(x_28);
lean_inc(x_27);
x_378 = l_Lean_Name_mkStr4(x_27, x_28, x_349, x_377);
lean_inc(x_378);
lean_ctor_set_tag(x_372, 1);
lean_ctor_set(x_372, 1, x_362);
lean_ctor_set(x_372, 0, x_378);
x_379 = lean_mk_string_unchecked("Attr", 4, 4);
x_380 = lean_mk_string_unchecked("simple", 6, 6);
lean_inc(x_28);
lean_inc(x_27);
x_381 = l_Lean_Name_mkStr4(x_27, x_28, x_379, x_380);
x_382 = l_Lean_mkIdentFrom(x_350, x_359, x_355);
lean_dec(x_350);
x_383 = l___private_Init_Data_Repr_0__Nat_reprFast(x_364);
lean_inc(x_356);
x_384 = l_Lean_Syntax_mkNumLit(x_383, x_356);
lean_inc(x_353);
lean_inc(x_376);
x_385 = l_Lean_Syntax_node1(x_376, x_353, x_384);
lean_inc(x_376);
x_386 = l_Lean_Syntax_node2(x_376, x_381, x_382, x_385);
x_387 = l_Lean_Syntax_node2(x_376, x_378, x_357, x_386);
if (lean_obj_tag(x_365) == 0)
{
lean_object* x_388; 
x_388 = lean_mk_empty_array_with_capacity(x_346);
x_293 = x_347;
x_294 = x_348;
x_295 = x_349;
x_296 = x_351;
x_297 = x_353;
x_298 = x_354;
x_299 = x_356;
x_300 = x_387;
x_301 = x_374;
x_302 = x_372;
x_303 = x_358;
x_304 = x_360;
x_305 = x_361;
x_306 = x_366;
x_307 = x_363;
x_308 = x_388;
goto block_345;
}
else
{
lean_object* x_389; 
x_389 = lean_ctor_get(x_365, 0);
lean_inc(x_389);
lean_dec(x_365);
x_293 = x_347;
x_294 = x_348;
x_295 = x_349;
x_296 = x_351;
x_297 = x_353;
x_298 = x_354;
x_299 = x_356;
x_300 = x_387;
x_301 = x_374;
x_302 = x_372;
x_303 = x_358;
x_304 = x_360;
x_305 = x_361;
x_306 = x_366;
x_307 = x_363;
x_308 = x_389;
goto block_345;
}
}
else
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; 
x_390 = lean_ctor_get(x_372, 1);
lean_inc(x_390);
lean_dec(x_372);
x_391 = l_Lean_SourceInfo_fromRef(x_368, x_355);
lean_dec(x_368);
x_392 = lean_mk_string_unchecked("attrInstance", 12, 12);
lean_inc(x_349);
lean_inc(x_28);
lean_inc(x_27);
x_393 = l_Lean_Name_mkStr4(x_27, x_28, x_349, x_392);
lean_inc(x_393);
x_394 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_394, 0, x_393);
lean_ctor_set(x_394, 1, x_362);
x_395 = lean_mk_string_unchecked("Attr", 4, 4);
x_396 = lean_mk_string_unchecked("simple", 6, 6);
lean_inc(x_28);
lean_inc(x_27);
x_397 = l_Lean_Name_mkStr4(x_27, x_28, x_395, x_396);
x_398 = l_Lean_mkIdentFrom(x_350, x_359, x_355);
lean_dec(x_350);
x_399 = l___private_Init_Data_Repr_0__Nat_reprFast(x_364);
lean_inc(x_356);
x_400 = l_Lean_Syntax_mkNumLit(x_399, x_356);
lean_inc(x_353);
lean_inc(x_391);
x_401 = l_Lean_Syntax_node1(x_391, x_353, x_400);
lean_inc(x_391);
x_402 = l_Lean_Syntax_node2(x_391, x_397, x_398, x_401);
x_403 = l_Lean_Syntax_node2(x_391, x_393, x_357, x_402);
if (lean_obj_tag(x_365) == 0)
{
lean_object* x_404; 
x_404 = lean_mk_empty_array_with_capacity(x_346);
x_293 = x_347;
x_294 = x_348;
x_295 = x_349;
x_296 = x_351;
x_297 = x_353;
x_298 = x_354;
x_299 = x_356;
x_300 = x_403;
x_301 = x_390;
x_302 = x_394;
x_303 = x_358;
x_304 = x_360;
x_305 = x_361;
x_306 = x_366;
x_307 = x_363;
x_308 = x_404;
goto block_345;
}
else
{
lean_object* x_405; 
x_405 = lean_ctor_get(x_365, 0);
lean_inc(x_405);
lean_dec(x_365);
x_293 = x_347;
x_294 = x_348;
x_295 = x_349;
x_296 = x_351;
x_297 = x_353;
x_298 = x_354;
x_299 = x_356;
x_300 = x_403;
x_301 = x_390;
x_302 = x_394;
x_303 = x_358;
x_304 = x_360;
x_305 = x_361;
x_306 = x_366;
x_307 = x_363;
x_308 = x_405;
goto block_345;
}
}
}
block_446:
{
lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; 
x_425 = l_Lean_Elab_Command_getScope___redArg(x_409, x_423);
x_426 = lean_ctor_get(x_425, 0);
lean_inc(x_426);
x_427 = lean_ctor_get(x_425, 1);
lean_inc(x_427);
lean_dec(x_425);
x_428 = l_Lean_Elab_Command_runTermElabM___redArg(x_421, x_414, x_409, x_427);
if (lean_obj_tag(x_428) == 0)
{
lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; 
x_429 = lean_ctor_get(x_428, 0);
lean_inc(x_429);
x_430 = lean_ctor_get(x_428, 1);
lean_inc(x_430);
lean_dec(x_428);
x_431 = lean_ctor_get(x_429, 0);
lean_inc(x_431);
x_432 = lean_ctor_get(x_429, 1);
lean_inc(x_432);
lean_dec(x_429);
x_433 = lean_mk_string_unchecked("_parser", 7, 7);
x_434 = lean_ctor_get(x_426, 2);
lean_inc(x_434);
lean_dec(x_426);
x_435 = lean_name_append_after(x_413, x_433);
x_436 = lean_box(0);
lean_inc(x_416);
x_437 = l_Lean_Name_append(x_434, x_416);
if (lean_obj_tag(x_417) == 0)
{
lean_object* x_438; uint8_t x_439; 
x_438 = l_Lean_mkIdentFrom(x_424, x_416, x_291);
x_439 = lean_unbox(x_436);
x_347 = x_407;
x_348 = x_431;
x_349 = x_408;
x_350 = x_424;
x_351 = x_409;
x_352 = x_430;
x_353 = x_410;
x_354 = x_437;
x_355 = x_439;
x_356 = x_411;
x_357 = x_412;
x_358 = x_432;
x_359 = x_435;
x_360 = x_414;
x_361 = x_415;
x_362 = x_418;
x_363 = x_419;
x_364 = x_420;
x_365 = x_422;
x_366 = x_438;
goto block_406;
}
else
{
lean_object* x_440; uint8_t x_441; 
lean_dec(x_416);
x_440 = lean_ctor_get(x_417, 0);
lean_inc(x_440);
lean_dec(x_417);
x_441 = lean_unbox(x_436);
x_347 = x_407;
x_348 = x_431;
x_349 = x_408;
x_350 = x_424;
x_351 = x_409;
x_352 = x_430;
x_353 = x_410;
x_354 = x_437;
x_355 = x_441;
x_356 = x_411;
x_357 = x_412;
x_358 = x_432;
x_359 = x_435;
x_360 = x_414;
x_361 = x_415;
x_362 = x_418;
x_363 = x_419;
x_364 = x_420;
x_365 = x_422;
x_366 = x_440;
goto block_406;
}
}
else
{
uint8_t x_442; 
lean_dec(x_426);
lean_dec(x_424);
lean_dec(x_422);
lean_dec(x_420);
lean_dec(x_419);
lean_dec(x_418);
lean_dec(x_417);
lean_dec(x_416);
lean_dec(x_415);
lean_dec(x_414);
lean_dec(x_413);
lean_dec(x_412);
lean_dec(x_411);
lean_dec(x_410);
lean_dec(x_409);
lean_dec(x_408);
lean_dec(x_96);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_1);
x_442 = !lean_is_exclusive(x_428);
if (x_442 == 0)
{
return x_428;
}
else
{
lean_object* x_443; lean_object* x_444; lean_object* x_445; 
x_443 = lean_ctor_get(x_428, 0);
x_444 = lean_ctor_get(x_428, 1);
lean_inc(x_444);
lean_inc(x_443);
lean_dec(x_428);
x_445 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_445, 0, x_443);
lean_ctor_set(x_445, 1, x_444);
return x_445;
}
}
}
block_476:
{
lean_object* x_465; lean_object* x_466; 
x_465 = lean_alloc_closure((void*)(l_Lean_evalOptPrio___boxed), 3, 1);
lean_closure_set(x_465, 0, x_453);
x_466 = l_Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1(lean_box(0), x_465, x_462, x_463, x_464);
if (lean_obj_tag(x_466) == 0)
{
if (lean_obj_tag(x_455) == 0)
{
lean_object* x_467; lean_object* x_468; 
x_467 = lean_ctor_get(x_466, 0);
lean_inc(x_467);
x_468 = lean_ctor_get(x_466, 1);
lean_inc(x_468);
lean_dec(x_466);
x_407 = x_447;
x_408 = x_448;
x_409 = x_463;
x_410 = x_449;
x_411 = x_450;
x_412 = x_451;
x_413 = x_452;
x_414 = x_462;
x_415 = x_454;
x_416 = x_461;
x_417 = x_455;
x_418 = x_456;
x_419 = x_458;
x_420 = x_467;
x_421 = x_459;
x_422 = x_460;
x_423 = x_468;
x_424 = x_457;
goto block_446;
}
else
{
lean_object* x_469; lean_object* x_470; lean_object* x_471; 
lean_dec(x_457);
x_469 = lean_ctor_get(x_466, 0);
lean_inc(x_469);
x_470 = lean_ctor_get(x_466, 1);
lean_inc(x_470);
lean_dec(x_466);
x_471 = lean_ctor_get(x_455, 0);
lean_inc(x_471);
x_407 = x_447;
x_408 = x_448;
x_409 = x_463;
x_410 = x_449;
x_411 = x_450;
x_412 = x_451;
x_413 = x_452;
x_414 = x_462;
x_415 = x_454;
x_416 = x_461;
x_417 = x_455;
x_418 = x_456;
x_419 = x_458;
x_420 = x_469;
x_421 = x_459;
x_422 = x_460;
x_423 = x_470;
x_424 = x_471;
goto block_446;
}
}
else
{
uint8_t x_472; 
lean_dec(x_463);
lean_dec(x_462);
lean_dec(x_461);
lean_dec(x_460);
lean_dec(x_459);
lean_dec(x_458);
lean_dec(x_457);
lean_dec(x_456);
lean_dec(x_455);
lean_dec(x_454);
lean_dec(x_452);
lean_dec(x_451);
lean_dec(x_450);
lean_dec(x_449);
lean_dec(x_448);
lean_dec(x_96);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_1);
x_472 = !lean_is_exclusive(x_466);
if (x_472 == 0)
{
return x_466;
}
else
{
lean_object* x_473; lean_object* x_474; lean_object* x_475; 
x_473 = lean_ctor_get(x_466, 0);
x_474 = lean_ctor_get(x_466, 1);
lean_inc(x_474);
lean_inc(x_473);
lean_dec(x_466);
x_475 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_475, 0, x_473);
lean_ctor_set(x_475, 1, x_474);
return x_475;
}
}
}
block_508:
{
if (lean_obj_tag(x_485) == 0)
{
lean_object* x_495; lean_object* x_496; 
lean_inc(x_483);
x_495 = lean_alloc_closure((void*)(l_Lean_Elab_Command_mkNameFromParserSyntax___boxed), 4, 2);
lean_closure_set(x_495, 0, x_483);
lean_closure_set(x_495, 1, x_482);
x_496 = l_Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1(lean_box(0), x_495, x_492, x_493, x_494);
if (lean_obj_tag(x_496) == 0)
{
lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; 
x_497 = lean_ctor_get(x_496, 0);
lean_inc(x_497);
x_498 = lean_ctor_get(x_496, 1);
lean_inc(x_498);
lean_dec(x_496);
lean_inc(x_481);
x_499 = l_Lean_Elab_Command_addMacroScopeIfLocal___at___Lean_Elab_Command_elabSyntax_spec__1(x_497, x_481, x_492, x_493, x_498);
x_500 = lean_ctor_get(x_499, 0);
lean_inc(x_500);
x_501 = lean_ctor_get(x_499, 1);
lean_inc(x_501);
lean_dec(x_499);
x_447 = x_477;
x_448 = x_478;
x_449 = x_479;
x_450 = x_480;
x_451 = x_481;
x_452 = x_483;
x_453 = x_484;
x_454 = x_491;
x_455 = x_485;
x_456 = x_486;
x_457 = x_487;
x_458 = x_488;
x_459 = x_489;
x_460 = x_490;
x_461 = x_500;
x_462 = x_492;
x_463 = x_493;
x_464 = x_501;
goto block_476;
}
else
{
uint8_t x_502; 
lean_dec(x_493);
lean_dec(x_492);
lean_dec(x_491);
lean_dec(x_490);
lean_dec(x_489);
lean_dec(x_488);
lean_dec(x_487);
lean_dec(x_486);
lean_dec(x_484);
lean_dec(x_483);
lean_dec(x_481);
lean_dec(x_480);
lean_dec(x_479);
lean_dec(x_478);
lean_dec(x_96);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_1);
x_502 = !lean_is_exclusive(x_496);
if (x_502 == 0)
{
return x_496;
}
else
{
lean_object* x_503; lean_object* x_504; lean_object* x_505; 
x_503 = lean_ctor_get(x_496, 0);
x_504 = lean_ctor_get(x_496, 1);
lean_inc(x_504);
lean_inc(x_503);
lean_dec(x_496);
x_505 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_505, 0, x_503);
lean_ctor_set(x_505, 1, x_504);
return x_505;
}
}
}
else
{
lean_object* x_506; lean_object* x_507; 
lean_dec(x_482);
x_506 = lean_ctor_get(x_485, 0);
lean_inc(x_506);
x_507 = l_Lean_Syntax_getId(x_506);
lean_dec(x_506);
x_447 = x_477;
x_448 = x_478;
x_449 = x_479;
x_450 = x_480;
x_451 = x_481;
x_452 = x_483;
x_453 = x_484;
x_454 = x_491;
x_455 = x_485;
x_456 = x_486;
x_457 = x_487;
x_458 = x_488;
x_459 = x_489;
x_460 = x_490;
x_461 = x_507;
x_462 = x_492;
x_463 = x_493;
x_464 = x_494;
goto block_476;
}
}
block_537:
{
if (lean_obj_tag(x_525) == 0)
{
x_477 = x_509;
x_478 = x_510;
x_479 = x_512;
x_480 = x_515;
x_481 = x_516;
x_482 = x_517;
x_483 = x_518;
x_484 = x_519;
x_485 = x_521;
x_486 = x_520;
x_487 = x_523;
x_488 = x_522;
x_489 = x_524;
x_490 = x_526;
x_491 = x_527;
x_492 = x_514;
x_493 = x_511;
x_494 = x_513;
goto block_508;
}
else
{
lean_object* x_528; lean_object* x_529; lean_object* x_530; 
lean_dec(x_527);
x_528 = lean_ctor_get(x_525, 0);
lean_inc(x_528);
lean_dec(x_525);
x_529 = lean_alloc_closure((void*)(l_Lean_evalPrec___boxed), 3, 1);
lean_closure_set(x_529, 0, x_528);
x_530 = l_Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1(lean_box(0), x_529, x_514, x_511, x_513);
if (lean_obj_tag(x_530) == 0)
{
lean_object* x_531; lean_object* x_532; 
x_531 = lean_ctor_get(x_530, 0);
lean_inc(x_531);
x_532 = lean_ctor_get(x_530, 1);
lean_inc(x_532);
lean_dec(x_530);
x_477 = x_509;
x_478 = x_510;
x_479 = x_512;
x_480 = x_515;
x_481 = x_516;
x_482 = x_517;
x_483 = x_518;
x_484 = x_519;
x_485 = x_521;
x_486 = x_520;
x_487 = x_523;
x_488 = x_522;
x_489 = x_524;
x_490 = x_526;
x_491 = x_531;
x_492 = x_514;
x_493 = x_511;
x_494 = x_532;
goto block_508;
}
else
{
uint8_t x_533; 
lean_dec(x_526);
lean_dec(x_524);
lean_dec(x_523);
lean_dec(x_522);
lean_dec(x_521);
lean_dec(x_520);
lean_dec(x_519);
lean_dec(x_518);
lean_dec(x_517);
lean_dec(x_516);
lean_dec(x_515);
lean_dec(x_514);
lean_dec(x_512);
lean_dec(x_511);
lean_dec(x_510);
lean_dec(x_96);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_1);
x_533 = !lean_is_exclusive(x_530);
if (x_533 == 0)
{
return x_530;
}
else
{
lean_object* x_534; lean_object* x_535; lean_object* x_536; 
x_534 = lean_ctor_get(x_530, 0);
x_535 = lean_ctor_get(x_530, 1);
lean_inc(x_535);
lean_inc(x_534);
lean_dec(x_530);
x_536 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_536, 0, x_534);
lean_ctor_set(x_536, 1, x_535);
return x_536;
}
}
}
}
block_616:
{
lean_object* x_550; lean_object* x_551; lean_object* x_552; size_t x_553; size_t x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; uint8_t x_558; 
x_550 = lean_unsigned_to_nat(7u);
x_551 = l_Lean_Syntax_getArg(x_1, x_550);
x_552 = l_Lean_Syntax_getArgs(x_551);
lean_dec(x_551);
x_553 = lean_array_size(x_552);
x_554 = lean_usize_of_nat(x_346);
x_555 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_elabSyntax_spec__0(x_553, x_554, x_552);
x_556 = lean_ctor_get(x_555, 0);
lean_inc(x_556);
lean_dec(x_555);
x_557 = lean_st_ref_get(x_548, x_549);
x_558 = !lean_is_exclusive(x_557);
if (x_558 == 0)
{
lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; uint8_t x_568; 
x_559 = lean_ctor_get(x_557, 0);
x_560 = lean_ctor_get(x_557, 1);
x_561 = lean_unsigned_to_nat(9u);
x_562 = l_Lean_Syntax_getArg(x_1, x_561);
x_563 = lean_box(0);
x_564 = l_Lean_Syntax_getId(x_562);
x_565 = l_Lean_Syntax_getArg(x_1, x_542);
x_566 = lean_erase_macro_scopes(x_564);
x_567 = lean_ctor_get(x_559, 0);
lean_inc(x_567);
lean_dec(x_559);
x_568 = l_Lean_Parser_isParserCategory(x_567, x_566);
if (x_568 == 0)
{
lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; 
lean_dec(x_565);
lean_dec(x_556);
lean_dec(x_546);
lean_dec(x_545);
lean_dec(x_544);
lean_dec(x_543);
lean_dec(x_541);
lean_dec(x_540);
lean_dec(x_539);
lean_dec(x_96);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_1);
x_569 = lean_mk_string_unchecked("unknown category '", 18, 18);
x_570 = l_Lean_stringToMessageData(x_569);
lean_dec(x_569);
x_571 = l_Lean_MessageData_ofName(x_566);
lean_ctor_set_tag(x_557, 7);
lean_ctor_set(x_557, 1, x_571);
lean_ctor_set(x_557, 0, x_570);
x_572 = lean_mk_string_unchecked("'", 1, 1);
x_573 = l_Lean_stringToMessageData(x_572);
lean_dec(x_572);
x_574 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_574, 0, x_557);
lean_ctor_set(x_574, 1, x_573);
x_575 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__3___redArg(x_562, x_574, x_547, x_548, x_560);
lean_dec(x_548);
lean_dec(x_547);
lean_dec(x_562);
return x_575;
}
else
{
lean_object* x_576; lean_object* x_577; 
lean_free_object(x_557);
lean_inc(x_566);
x_576 = lean_alloc_closure((void*)(l_Lean_Elab_Term_addCategoryInfo), 9, 2);
lean_closure_set(x_576, 0, x_562);
lean_closure_set(x_576, 1, x_566);
x_577 = l_Lean_Elab_Command_liftTermElabM___redArg(x_576, x_547, x_548, x_560);
if (lean_obj_tag(x_577) == 0)
{
lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; uint8_t x_584; 
x_578 = lean_ctor_get(x_577, 1);
lean_inc(x_578);
lean_dec(x_577);
x_579 = lean_mk_string_unchecked("null", 4, 4);
x_580 = l_Lean_Name_mkStr1(x_579);
x_581 = lean_box(2);
lean_inc(x_580);
x_582 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_582, 0, x_581);
lean_ctor_set(x_582, 1, x_580);
lean_ctor_set(x_582, 2, x_556);
lean_inc(x_566);
lean_inc(x_582);
x_583 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabSyntax___lam__1___boxed), 10, 2);
lean_closure_set(x_583, 0, x_582);
lean_closure_set(x_583, 1, x_566);
lean_inc(x_582);
x_584 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_isAtomLikeSyntax(x_582);
if (x_584 == 0)
{
lean_object* x_585; 
x_585 = lean_unsigned_to_nat(1022u);
x_509 = x_538;
x_510 = x_539;
x_511 = x_548;
x_512 = x_580;
x_513 = x_578;
x_514 = x_547;
x_515 = x_581;
x_516 = x_543;
x_517 = x_582;
x_518 = x_566;
x_519 = x_546;
x_520 = x_563;
x_521 = x_540;
x_522 = x_541;
x_523 = x_565;
x_524 = x_583;
x_525 = x_544;
x_526 = x_545;
x_527 = x_585;
goto block_537;
}
else
{
lean_object* x_586; 
x_586 = lean_unsigned_to_nat(1024u);
x_509 = x_538;
x_510 = x_539;
x_511 = x_548;
x_512 = x_580;
x_513 = x_578;
x_514 = x_547;
x_515 = x_581;
x_516 = x_543;
x_517 = x_582;
x_518 = x_566;
x_519 = x_546;
x_520 = x_563;
x_521 = x_540;
x_522 = x_541;
x_523 = x_565;
x_524 = x_583;
x_525 = x_544;
x_526 = x_545;
x_527 = x_586;
goto block_537;
}
}
else
{
lean_dec(x_566);
lean_dec(x_565);
lean_dec(x_556);
lean_dec(x_548);
lean_dec(x_547);
lean_dec(x_546);
lean_dec(x_545);
lean_dec(x_544);
lean_dec(x_543);
lean_dec(x_541);
lean_dec(x_540);
lean_dec(x_539);
lean_dec(x_96);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_1);
return x_577;
}
}
}
else
{
lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; uint8_t x_596; 
x_587 = lean_ctor_get(x_557, 0);
x_588 = lean_ctor_get(x_557, 1);
lean_inc(x_588);
lean_inc(x_587);
lean_dec(x_557);
x_589 = lean_unsigned_to_nat(9u);
x_590 = l_Lean_Syntax_getArg(x_1, x_589);
x_591 = lean_box(0);
x_592 = l_Lean_Syntax_getId(x_590);
x_593 = l_Lean_Syntax_getArg(x_1, x_542);
x_594 = lean_erase_macro_scopes(x_592);
x_595 = lean_ctor_get(x_587, 0);
lean_inc(x_595);
lean_dec(x_587);
x_596 = l_Lean_Parser_isParserCategory(x_595, x_594);
if (x_596 == 0)
{
lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; 
lean_dec(x_593);
lean_dec(x_556);
lean_dec(x_546);
lean_dec(x_545);
lean_dec(x_544);
lean_dec(x_543);
lean_dec(x_541);
lean_dec(x_540);
lean_dec(x_539);
lean_dec(x_96);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_1);
x_597 = lean_mk_string_unchecked("unknown category '", 18, 18);
x_598 = l_Lean_stringToMessageData(x_597);
lean_dec(x_597);
x_599 = l_Lean_MessageData_ofName(x_594);
x_600 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_600, 0, x_598);
lean_ctor_set(x_600, 1, x_599);
x_601 = lean_mk_string_unchecked("'", 1, 1);
x_602 = l_Lean_stringToMessageData(x_601);
lean_dec(x_601);
x_603 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_603, 0, x_600);
lean_ctor_set(x_603, 1, x_602);
x_604 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__3___redArg(x_590, x_603, x_547, x_548, x_588);
lean_dec(x_548);
lean_dec(x_547);
lean_dec(x_590);
return x_604;
}
else
{
lean_object* x_605; lean_object* x_606; 
lean_inc(x_594);
x_605 = lean_alloc_closure((void*)(l_Lean_Elab_Term_addCategoryInfo), 9, 2);
lean_closure_set(x_605, 0, x_590);
lean_closure_set(x_605, 1, x_594);
x_606 = l_Lean_Elab_Command_liftTermElabM___redArg(x_605, x_547, x_548, x_588);
if (lean_obj_tag(x_606) == 0)
{
lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; uint8_t x_613; 
x_607 = lean_ctor_get(x_606, 1);
lean_inc(x_607);
lean_dec(x_606);
x_608 = lean_mk_string_unchecked("null", 4, 4);
x_609 = l_Lean_Name_mkStr1(x_608);
x_610 = lean_box(2);
lean_inc(x_609);
x_611 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_611, 0, x_610);
lean_ctor_set(x_611, 1, x_609);
lean_ctor_set(x_611, 2, x_556);
lean_inc(x_594);
lean_inc(x_611);
x_612 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabSyntax___lam__1___boxed), 10, 2);
lean_closure_set(x_612, 0, x_611);
lean_closure_set(x_612, 1, x_594);
lean_inc(x_611);
x_613 = l___private_Lean_Elab_Syntax_0__Lean_Elab_Command_isAtomLikeSyntax(x_611);
if (x_613 == 0)
{
lean_object* x_614; 
x_614 = lean_unsigned_to_nat(1022u);
x_509 = x_538;
x_510 = x_539;
x_511 = x_548;
x_512 = x_609;
x_513 = x_607;
x_514 = x_547;
x_515 = x_610;
x_516 = x_543;
x_517 = x_611;
x_518 = x_594;
x_519 = x_546;
x_520 = x_591;
x_521 = x_540;
x_522 = x_541;
x_523 = x_593;
x_524 = x_612;
x_525 = x_544;
x_526 = x_545;
x_527 = x_614;
goto block_537;
}
else
{
lean_object* x_615; 
x_615 = lean_unsigned_to_nat(1024u);
x_509 = x_538;
x_510 = x_539;
x_511 = x_548;
x_512 = x_609;
x_513 = x_607;
x_514 = x_547;
x_515 = x_610;
x_516 = x_543;
x_517 = x_611;
x_518 = x_594;
x_519 = x_546;
x_520 = x_591;
x_521 = x_540;
x_522 = x_541;
x_523 = x_593;
x_524 = x_612;
x_525 = x_544;
x_526 = x_545;
x_527 = x_615;
goto block_537;
}
}
else
{
lean_dec(x_594);
lean_dec(x_593);
lean_dec(x_556);
lean_dec(x_548);
lean_dec(x_547);
lean_dec(x_546);
lean_dec(x_545);
lean_dec(x_544);
lean_dec(x_543);
lean_dec(x_541);
lean_dec(x_540);
lean_dec(x_539);
lean_dec(x_96);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_1);
return x_606;
}
}
}
}
block_641:
{
lean_object* x_628; lean_object* x_629; uint8_t x_630; 
x_628 = lean_unsigned_to_nat(6u);
x_629 = l_Lean_Syntax_getArg(x_1, x_628);
x_630 = l_Lean_Syntax_isNone(x_629);
if (x_630 == 0)
{
uint8_t x_631; 
lean_inc(x_629);
x_631 = l_Lean_Syntax_matchesNull(x_629, x_617);
if (x_631 == 0)
{
lean_object* x_632; 
lean_dec(x_629);
lean_dec(x_624);
lean_dec(x_623);
lean_dec(x_622);
lean_dec(x_621);
lean_dec(x_620);
lean_dec(x_618);
lean_dec(x_96);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_1);
x_632 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_625, x_626, x_627);
lean_dec(x_626);
lean_dec(x_625);
return x_632;
}
else
{
lean_object* x_633; lean_object* x_634; lean_object* x_635; uint8_t x_636; 
x_633 = l_Lean_Syntax_getArg(x_629, x_346);
lean_dec(x_629);
x_634 = lean_mk_string_unchecked("namedPrio", 9, 9);
lean_inc(x_96);
lean_inc(x_28);
lean_inc(x_27);
x_635 = l_Lean_Name_mkStr4(x_27, x_28, x_96, x_634);
lean_inc(x_633);
x_636 = l_Lean_Syntax_isOfKind(x_633, x_635);
lean_dec(x_635);
if (x_636 == 0)
{
lean_object* x_637; 
lean_dec(x_633);
lean_dec(x_624);
lean_dec(x_623);
lean_dec(x_622);
lean_dec(x_621);
lean_dec(x_620);
lean_dec(x_618);
lean_dec(x_96);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_1);
x_637 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_625, x_626, x_627);
lean_dec(x_626);
lean_dec(x_625);
return x_637;
}
else
{
lean_object* x_638; lean_object* x_639; 
x_638 = l_Lean_Syntax_getArg(x_633, x_619);
lean_dec(x_633);
x_639 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_639, 0, x_638);
x_538 = x_617;
x_539 = x_618;
x_540 = x_624;
x_541 = x_620;
x_542 = x_619;
x_543 = x_621;
x_544 = x_622;
x_545 = x_623;
x_546 = x_639;
x_547 = x_625;
x_548 = x_626;
x_549 = x_627;
goto block_616;
}
}
}
else
{
lean_object* x_640; 
lean_dec(x_629);
x_640 = lean_box(0);
x_538 = x_617;
x_539 = x_618;
x_540 = x_624;
x_541 = x_620;
x_542 = x_619;
x_543 = x_621;
x_544 = x_622;
x_545 = x_623;
x_546 = x_640;
x_547 = x_625;
x_548 = x_626;
x_549 = x_627;
goto block_616;
}
}
block_665:
{
lean_object* x_652; lean_object* x_653; uint8_t x_654; 
x_652 = lean_unsigned_to_nat(5u);
x_653 = l_Lean_Syntax_getArg(x_1, x_652);
x_654 = l_Lean_Syntax_isNone(x_653);
if (x_654 == 0)
{
uint8_t x_655; 
lean_inc(x_653);
x_655 = l_Lean_Syntax_matchesNull(x_653, x_642);
if (x_655 == 0)
{
lean_object* x_656; 
lean_dec(x_653);
lean_dec(x_648);
lean_dec(x_647);
lean_dec(x_646);
lean_dec(x_644);
lean_dec(x_643);
lean_dec(x_96);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_1);
x_656 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_649, x_650, x_651);
lean_dec(x_650);
lean_dec(x_649);
return x_656;
}
else
{
lean_object* x_657; lean_object* x_658; lean_object* x_659; uint8_t x_660; 
x_657 = l_Lean_Syntax_getArg(x_653, x_346);
lean_dec(x_653);
x_658 = lean_mk_string_unchecked("namedName", 9, 9);
lean_inc(x_96);
lean_inc(x_28);
lean_inc(x_27);
x_659 = l_Lean_Name_mkStr4(x_27, x_28, x_96, x_658);
lean_inc(x_657);
x_660 = l_Lean_Syntax_isOfKind(x_657, x_659);
lean_dec(x_659);
if (x_660 == 0)
{
lean_object* x_661; 
lean_dec(x_657);
lean_dec(x_648);
lean_dec(x_647);
lean_dec(x_646);
lean_dec(x_644);
lean_dec(x_643);
lean_dec(x_96);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_1);
x_661 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_649, x_650, x_651);
lean_dec(x_650);
lean_dec(x_649);
return x_661;
}
else
{
lean_object* x_662; lean_object* x_663; 
x_662 = l_Lean_Syntax_getArg(x_657, x_645);
lean_dec(x_657);
x_663 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_663, 0, x_662);
x_617 = x_642;
x_618 = x_643;
x_619 = x_645;
x_620 = x_644;
x_621 = x_646;
x_622 = x_648;
x_623 = x_647;
x_624 = x_663;
x_625 = x_649;
x_626 = x_650;
x_627 = x_651;
goto block_641;
}
}
}
else
{
lean_object* x_664; 
lean_dec(x_653);
x_664 = lean_box(0);
x_617 = x_642;
x_618 = x_643;
x_619 = x_645;
x_620 = x_644;
x_621 = x_646;
x_622 = x_648;
x_623 = x_647;
x_624 = x_664;
x_625 = x_649;
x_626 = x_650;
x_627 = x_651;
goto block_641;
}
}
block_693:
{
lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; uint8_t x_677; 
x_672 = lean_unsigned_to_nat(2u);
x_673 = l_Lean_Syntax_getArg(x_1, x_672);
x_674 = lean_mk_string_unchecked("Term", 4, 4);
x_675 = lean_mk_string_unchecked("attrKind", 8, 8);
lean_inc(x_674);
lean_inc(x_28);
lean_inc(x_27);
x_676 = l_Lean_Name_mkStr4(x_27, x_28, x_674, x_675);
lean_inc(x_673);
x_677 = l_Lean_Syntax_isOfKind(x_673, x_676);
lean_dec(x_676);
if (x_677 == 0)
{
lean_object* x_678; 
lean_dec(x_674);
lean_dec(x_673);
lean_dec(x_668);
lean_dec(x_667);
lean_dec(x_96);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_1);
x_678 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_669, x_670, x_671);
lean_dec(x_670);
lean_dec(x_669);
return x_678;
}
else
{
lean_object* x_679; lean_object* x_680; lean_object* x_681; uint8_t x_682; 
x_679 = lean_unsigned_to_nat(3u);
x_680 = lean_unsigned_to_nat(4u);
x_681 = l_Lean_Syntax_getArg(x_1, x_680);
x_682 = l_Lean_Syntax_isNone(x_681);
if (x_682 == 0)
{
uint8_t x_683; 
lean_inc(x_681);
x_683 = l_Lean_Syntax_matchesNull(x_681, x_666);
if (x_683 == 0)
{
lean_object* x_684; 
lean_dec(x_681);
lean_dec(x_674);
lean_dec(x_673);
lean_dec(x_668);
lean_dec(x_667);
lean_dec(x_96);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_1);
x_684 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_669, x_670, x_671);
lean_dec(x_670);
lean_dec(x_669);
return x_684;
}
else
{
lean_object* x_685; lean_object* x_686; lean_object* x_687; uint8_t x_688; 
x_685 = l_Lean_Syntax_getArg(x_681, x_346);
lean_dec(x_681);
x_686 = lean_mk_string_unchecked("precedence", 10, 10);
lean_inc(x_28);
lean_inc(x_27);
x_687 = l_Lean_Name_mkStr3(x_27, x_28, x_686);
lean_inc(x_685);
x_688 = l_Lean_Syntax_isOfKind(x_685, x_687);
lean_dec(x_687);
if (x_688 == 0)
{
lean_object* x_689; 
lean_dec(x_685);
lean_dec(x_674);
lean_dec(x_673);
lean_dec(x_668);
lean_dec(x_667);
lean_dec(x_96);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_1);
x_689 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_669, x_670, x_671);
lean_dec(x_670);
lean_dec(x_669);
return x_689;
}
else
{
lean_object* x_690; lean_object* x_691; 
x_690 = l_Lean_Syntax_getArg(x_685, x_666);
lean_dec(x_685);
x_691 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_691, 0, x_690);
x_642 = x_666;
x_643 = x_674;
x_644 = x_667;
x_645 = x_679;
x_646 = x_673;
x_647 = x_668;
x_648 = x_691;
x_649 = x_669;
x_650 = x_670;
x_651 = x_671;
goto block_665;
}
}
}
else
{
lean_object* x_692; 
lean_dec(x_681);
x_692 = lean_box(0);
x_642 = x_666;
x_643 = x_674;
x_644 = x_667;
x_645 = x_679;
x_646 = x_673;
x_647 = x_668;
x_648 = x_692;
x_649 = x_669;
x_650 = x_670;
x_651 = x_671;
goto block_665;
}
}
}
block_713:
{
lean_object* x_698; lean_object* x_699; uint8_t x_700; 
x_698 = lean_unsigned_to_nat(1u);
x_699 = l_Lean_Syntax_getArg(x_1, x_698);
x_700 = l_Lean_Syntax_isNone(x_699);
if (x_700 == 0)
{
uint8_t x_701; 
lean_inc(x_699);
x_701 = l_Lean_Syntax_matchesNull(x_699, x_698);
if (x_701 == 0)
{
lean_object* x_702; 
lean_dec(x_699);
lean_dec(x_694);
lean_dec(x_96);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_1);
x_702 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_695, x_696, x_697);
lean_dec(x_696);
lean_dec(x_695);
return x_702;
}
else
{
lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; uint8_t x_707; 
x_703 = l_Lean_Syntax_getArg(x_699, x_346);
lean_dec(x_699);
x_704 = lean_mk_string_unchecked("Term", 4, 4);
x_705 = lean_mk_string_unchecked("attributes", 10, 10);
lean_inc(x_28);
lean_inc(x_27);
x_706 = l_Lean_Name_mkStr4(x_27, x_28, x_704, x_705);
lean_inc(x_703);
x_707 = l_Lean_Syntax_isOfKind(x_703, x_706);
lean_dec(x_706);
if (x_707 == 0)
{
lean_object* x_708; 
lean_dec(x_703);
lean_dec(x_694);
lean_dec(x_96);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_1);
x_708 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_695, x_696, x_697);
lean_dec(x_696);
lean_dec(x_695);
return x_708;
}
else
{
lean_object* x_709; lean_object* x_710; lean_object* x_711; 
x_709 = l_Lean_Syntax_getArg(x_703, x_698);
lean_dec(x_703);
x_710 = l_Lean_Syntax_getArgs(x_709);
lean_dec(x_709);
x_711 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_711, 0, x_710);
x_666 = x_698;
x_667 = x_694;
x_668 = x_711;
x_669 = x_695;
x_670 = x_696;
x_671 = x_697;
goto block_693;
}
}
}
else
{
lean_object* x_712; 
lean_dec(x_699);
x_712 = lean_box(0);
x_666 = x_698;
x_667 = x_694;
x_668 = x_712;
x_669 = x_695;
x_670 = x_696;
x_671 = x_697;
goto block_693;
}
}
}
block_11:
{
lean_object* x_9; lean_object* x_10; 
lean_inc(x_7);
x_9 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand), 4, 1);
lean_closure_set(x_9, 0, x_7);
x_10 = l_Lean_Elab_Command_withMacroExpansion(lean_box(0), x_1, x_7, x_9, x_5, x_6, x_8);
return x_10;
}
block_26:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_mk_string_unchecked("Elab", 4, 4);
x_17 = l_Lean_Name_mkStr1(x_16);
lean_inc(x_17);
x_18 = l_Lean_isTracingEnabledFor___at___Lean_withTraceNode___at___Lean_Elab_Command_runLinters_spec__6_spec__6___redArg(x_17, x_14, x_15);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_17);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_5 = x_13;
x_6 = x_14;
x_7 = x_12;
x_8 = x_21;
goto block_11;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_dec(x_18);
lean_inc(x_12);
x_23 = l_Lean_MessageData_ofSyntax(x_12);
x_24 = l_Lean_addTrace___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__1(x_17, x_23, x_13, x_14, x_22);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_5 = x_13;
x_6 = x_14;
x_7 = x_12;
x_8 = x_25;
goto block_11;
}
}
block_60:
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_49 = l___private_Init_Data_Repr_0__Nat_reprFast(x_42);
x_50 = l_Lean_Syntax_mkNumLit(x_49, x_37);
lean_inc(x_45);
x_51 = l_Lean_Syntax_node3(x_45, x_34, x_48, x_50, x_30);
lean_inc(x_45);
x_52 = l_Lean_Syntax_node2(x_45, x_43, x_35, x_51);
x_53 = lean_mk_string_unchecked("Termination", 11, 11);
x_54 = lean_mk_string_unchecked("suffix", 6, 6);
x_55 = l_Lean_Name_mkStr4(x_27, x_28, x_53, x_54);
lean_inc_n(x_40, 2);
lean_inc(x_45);
x_56 = l_Lean_Syntax_node2(x_45, x_55, x_40, x_40);
lean_inc(x_40);
lean_inc(x_45);
x_57 = l_Lean_Syntax_node4(x_45, x_46, x_36, x_52, x_56, x_40);
lean_inc(x_45);
x_58 = l_Lean_Syntax_node5(x_45, x_44, x_38, x_32, x_39, x_57, x_40);
x_59 = l_Lean_Syntax_node2(x_45, x_29, x_47, x_58);
x_12 = x_59;
x_13 = x_41;
x_14 = x_31;
x_15 = x_33;
goto block_26;
}
block_95:
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_82 = l___private_Init_Data_Repr_0__Nat_reprFast(x_76);
lean_inc(x_66);
x_83 = l_Lean_Syntax_mkNumLit(x_82, x_66);
x_84 = l___private_Init_Data_Repr_0__Nat_reprFast(x_71);
x_85 = l_Lean_Syntax_mkNumLit(x_84, x_66);
lean_inc(x_77);
x_86 = l_Lean_Syntax_node4(x_77, x_64, x_81, x_83, x_85, x_61);
lean_inc(x_77);
x_87 = l_Lean_Syntax_node2(x_77, x_67, x_78, x_86);
x_88 = lean_mk_string_unchecked("Termination", 11, 11);
x_89 = lean_mk_string_unchecked("suffix", 6, 6);
x_90 = l_Lean_Name_mkStr4(x_27, x_28, x_88, x_89);
lean_inc_n(x_62, 2);
lean_inc(x_77);
x_91 = l_Lean_Syntax_node2(x_77, x_90, x_62, x_62);
lean_inc(x_62);
lean_inc(x_77);
x_92 = l_Lean_Syntax_node4(x_77, x_80, x_70, x_87, x_91, x_62);
lean_inc(x_77);
x_93 = l_Lean_Syntax_node5(x_77, x_73, x_65, x_75, x_69, x_92, x_62);
x_94 = l_Lean_Syntax_node2(x_77, x_72, x_68, x_93);
x_12 = x_94;
x_13 = x_74;
x_14 = x_63;
x_15 = x_79;
goto block_26;
}
block_192:
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
lean_inc(x_113);
x_119 = l_Array_append(lean_box(0), x_113, x_118);
lean_dec(x_118);
lean_inc(x_104);
lean_inc(x_116);
x_120 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_120, 0, x_116);
lean_ctor_set(x_120, 1, x_104);
lean_ctor_set(x_120, 2, x_119);
x_121 = lean_mk_string_unchecked("attributes", 10, 10);
lean_inc(x_101);
lean_inc(x_28);
lean_inc(x_27);
x_122 = l_Lean_Name_mkStr4(x_27, x_28, x_101, x_121);
x_123 = lean_mk_string_unchecked("@[", 2, 2);
lean_inc(x_116);
x_124 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_124, 0, x_116);
lean_ctor_set(x_124, 1, x_123);
x_125 = l_Lean_Syntax_TSepArray_push(x_109, x_98, x_106, x_108);
lean_dec(x_109);
lean_inc(x_113);
x_126 = l_Array_append(lean_box(0), x_113, x_125);
lean_dec(x_125);
lean_inc(x_104);
lean_inc(x_116);
x_127 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_127, 0, x_116);
lean_ctor_set(x_127, 1, x_104);
lean_ctor_set(x_127, 2, x_126);
x_128 = lean_mk_string_unchecked("]", 1, 1);
lean_inc(x_116);
x_129 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_129, 0, x_116);
lean_ctor_set(x_129, 1, x_128);
lean_inc(x_116);
x_130 = l_Lean_Syntax_node3(x_116, x_122, x_124, x_127, x_129);
lean_inc(x_104);
lean_inc(x_116);
x_131 = l_Lean_Syntax_node1(x_116, x_104, x_130);
lean_inc(x_104);
lean_inc(x_116);
x_132 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_132, 0, x_116);
lean_ctor_set(x_132, 1, x_104);
lean_ctor_set(x_132, 2, x_113);
lean_inc_n(x_132, 4);
lean_inc(x_116);
x_133 = l_Lean_Syntax_node6(x_116, x_117, x_120, x_131, x_132, x_132, x_132, x_132);
x_134 = lean_mk_string_unchecked("definition", 10, 10);
lean_inc(x_96);
lean_inc(x_28);
lean_inc(x_27);
x_135 = l_Lean_Name_mkStr4(x_27, x_28, x_96, x_134);
x_136 = lean_mk_string_unchecked("def", 3, 3);
lean_inc(x_116);
x_137 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_137, 0, x_116);
lean_ctor_set(x_137, 1, x_136);
x_138 = lean_mk_string_unchecked("declId", 6, 6);
lean_inc(x_96);
lean_inc(x_28);
lean_inc(x_27);
x_139 = l_Lean_Name_mkStr4(x_27, x_28, x_96, x_138);
lean_inc(x_132);
lean_inc(x_116);
x_140 = l_Lean_Syntax_node2(x_116, x_139, x_114, x_132);
x_141 = lean_mk_string_unchecked("optDeclSig", 10, 10);
lean_inc(x_96);
lean_inc(x_28);
lean_inc(x_27);
x_142 = l_Lean_Name_mkStr4(x_27, x_28, x_96, x_141);
x_143 = lean_mk_string_unchecked("typeSpec", 8, 8);
lean_inc(x_101);
lean_inc(x_28);
lean_inc(x_27);
x_144 = l_Lean_Name_mkStr4(x_27, x_28, x_101, x_143);
x_145 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_116);
x_146 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_146, 0, x_116);
lean_ctor_set(x_146, 1, x_145);
x_147 = lean_mk_string_unchecked("Lean.ParserDescr", 16, 16);
x_148 = l_String_toSubstring_x27(x_147);
x_149 = lean_mk_string_unchecked("ParserDescr", 11, 11);
lean_inc(x_149);
lean_inc(x_27);
x_150 = l_Lean_Name_mkStr2(x_27, x_149);
lean_inc(x_115);
lean_inc(x_150);
lean_inc(x_110);
x_151 = l_Lean_addMacroScope(x_110, x_150, x_115);
x_152 = lean_box(0);
lean_inc(x_150);
x_153 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_153, 0, x_150);
lean_ctor_set(x_153, 1, x_152);
x_154 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_154, 0, x_150);
x_155 = lean_box(0);
x_156 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_156, 0, x_154);
lean_ctor_set(x_156, 1, x_155);
x_157 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_157, 0, x_153);
lean_ctor_set(x_157, 1, x_156);
lean_inc(x_116);
x_158 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_158, 0, x_116);
lean_ctor_set(x_158, 1, x_148);
lean_ctor_set(x_158, 2, x_151);
lean_ctor_set(x_158, 3, x_157);
lean_inc(x_116);
x_159 = l_Lean_Syntax_node2(x_116, x_144, x_146, x_158);
lean_inc(x_104);
lean_inc(x_116);
x_160 = l_Lean_Syntax_node1(x_116, x_104, x_159);
lean_inc(x_132);
lean_inc(x_116);
x_161 = l_Lean_Syntax_node2(x_116, x_142, x_132, x_160);
x_162 = lean_mk_string_unchecked("declValSimple", 13, 13);
lean_inc(x_28);
lean_inc(x_27);
x_163 = l_Lean_Name_mkStr4(x_27, x_28, x_96, x_162);
x_164 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_116);
x_165 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_165, 0, x_116);
lean_ctor_set(x_165, 1, x_164);
x_166 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_101);
lean_inc(x_28);
lean_inc(x_27);
x_167 = l_Lean_Name_mkStr4(x_27, x_28, x_101, x_166);
x_168 = lean_mk_string_unchecked("ParserDescr.node", 16, 16);
x_169 = l_String_toSubstring_x27(x_168);
x_170 = lean_mk_string_unchecked("node", 4, 4);
lean_inc(x_170);
lean_inc(x_149);
x_171 = l_Lean_Name_mkStr2(x_149, x_170);
x_172 = l_Lean_addMacroScope(x_110, x_171, x_115);
lean_inc(x_27);
x_173 = l_Lean_Name_mkStr3(x_27, x_149, x_170);
lean_inc(x_173);
x_174 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_152);
x_175 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_175, 0, x_173);
x_176 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_176, 0, x_175);
lean_ctor_set(x_176, 1, x_155);
x_177 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_177, 0, x_174);
lean_ctor_set(x_177, 1, x_176);
lean_inc(x_116);
x_178 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_178, 0, x_116);
lean_ctor_set(x_178, 1, x_169);
lean_ctor_set(x_178, 2, x_172);
lean_ctor_set(x_178, 3, x_177);
lean_inc(x_105);
x_179 = l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(x_152, x_105);
if (lean_obj_tag(x_179) == 0)
{
lean_object* x_180; 
lean_dec(x_101);
x_180 = l_Lean_quoteNameMk(x_105);
x_29 = x_99;
x_30 = x_100;
x_31 = x_102;
x_32 = x_140;
x_33 = x_103;
x_34 = x_104;
x_35 = x_178;
x_36 = x_165;
x_37 = x_107;
x_38 = x_137;
x_39 = x_161;
x_40 = x_132;
x_41 = x_111;
x_42 = x_112;
x_43 = x_167;
x_44 = x_135;
x_45 = x_116;
x_46 = x_163;
x_47 = x_133;
x_48 = x_180;
goto block_60;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
lean_dec(x_105);
x_181 = lean_ctor_get(x_179, 0);
lean_inc(x_181);
lean_dec(x_179);
x_182 = lean_mk_string_unchecked("quotedName", 10, 10);
lean_inc(x_28);
lean_inc(x_27);
x_183 = l_Lean_Name_mkStr4(x_27, x_28, x_101, x_182);
x_184 = lean_mk_string_unchecked("`", 1, 1);
x_185 = lean_mk_string_unchecked(".", 1, 1);
x_186 = l_String_intercalate(x_185, x_181);
lean_dec(x_185);
x_187 = lean_string_append(x_184, x_186);
lean_dec(x_186);
lean_inc(x_107);
x_188 = l_Lean_Syntax_mkNameLit(x_187, x_107);
x_189 = lean_mk_empty_array_with_capacity(x_97);
x_190 = lean_array_push(x_189, x_188);
lean_inc(x_107);
x_191 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_191, 0, x_107);
lean_ctor_set(x_191, 1, x_183);
lean_ctor_set(x_191, 2, x_190);
x_29 = x_99;
x_30 = x_100;
x_31 = x_102;
x_32 = x_140;
x_33 = x_103;
x_34 = x_104;
x_35 = x_178;
x_36 = x_165;
x_37 = x_107;
x_38 = x_137;
x_39 = x_161;
x_40 = x_132;
x_41 = x_111;
x_42 = x_112;
x_43 = x_167;
x_44 = x_135;
x_45 = x_116;
x_46 = x_163;
x_47 = x_133;
x_48 = x_191;
goto block_60;
}
}
block_288:
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; 
lean_inc(x_206);
x_216 = l_Array_append(lean_box(0), x_206, x_215);
lean_dec(x_215);
lean_inc(x_199);
lean_inc(x_212);
x_217 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_217, 0, x_212);
lean_ctor_set(x_217, 1, x_199);
lean_ctor_set(x_217, 2, x_216);
x_218 = lean_mk_string_unchecked("attributes", 10, 10);
lean_inc(x_195);
lean_inc(x_28);
lean_inc(x_27);
x_219 = l_Lean_Name_mkStr4(x_27, x_28, x_195, x_218);
x_220 = lean_mk_string_unchecked("@[", 2, 2);
lean_inc(x_212);
x_221 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_221, 0, x_212);
lean_ctor_set(x_221, 1, x_220);
x_222 = l_Lean_Syntax_TSepArray_push(x_207, x_194, x_201, x_205);
lean_dec(x_207);
lean_inc(x_206);
x_223 = l_Array_append(lean_box(0), x_206, x_222);
lean_dec(x_222);
lean_inc(x_199);
lean_inc(x_212);
x_224 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_224, 0, x_212);
lean_ctor_set(x_224, 1, x_199);
lean_ctor_set(x_224, 2, x_223);
x_225 = lean_mk_string_unchecked("]", 1, 1);
lean_inc(x_212);
x_226 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_226, 0, x_212);
lean_ctor_set(x_226, 1, x_225);
lean_inc(x_212);
x_227 = l_Lean_Syntax_node3(x_212, x_219, x_221, x_224, x_226);
lean_inc(x_199);
lean_inc(x_212);
x_228 = l_Lean_Syntax_node1(x_212, x_199, x_227);
lean_inc(x_199);
lean_inc(x_212);
x_229 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_229, 0, x_212);
lean_ctor_set(x_229, 1, x_199);
lean_ctor_set(x_229, 2, x_206);
lean_inc_n(x_229, 4);
lean_inc(x_212);
x_230 = l_Lean_Syntax_node6(x_212, x_203, x_217, x_228, x_229, x_229, x_229, x_229);
x_231 = lean_mk_string_unchecked("definition", 10, 10);
lean_inc(x_96);
lean_inc(x_28);
lean_inc(x_27);
x_232 = l_Lean_Name_mkStr4(x_27, x_28, x_96, x_231);
x_233 = lean_mk_string_unchecked("def", 3, 3);
lean_inc(x_212);
x_234 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_234, 0, x_212);
lean_ctor_set(x_234, 1, x_233);
x_235 = lean_mk_string_unchecked("declId", 6, 6);
lean_inc(x_96);
lean_inc(x_28);
lean_inc(x_27);
x_236 = l_Lean_Name_mkStr4(x_27, x_28, x_96, x_235);
lean_inc(x_229);
lean_inc(x_212);
x_237 = l_Lean_Syntax_node2(x_212, x_236, x_213, x_229);
x_238 = lean_mk_string_unchecked("optDeclSig", 10, 10);
lean_inc(x_96);
lean_inc(x_28);
lean_inc(x_27);
x_239 = l_Lean_Name_mkStr4(x_27, x_28, x_96, x_238);
x_240 = lean_mk_string_unchecked("typeSpec", 8, 8);
lean_inc(x_195);
lean_inc(x_28);
lean_inc(x_27);
x_241 = l_Lean_Name_mkStr4(x_27, x_28, x_195, x_240);
x_242 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_212);
x_243 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_243, 0, x_212);
lean_ctor_set(x_243, 1, x_242);
x_244 = lean_mk_string_unchecked("Lean.TrailingParserDescr", 24, 24);
x_245 = l_String_toSubstring_x27(x_244);
x_246 = lean_mk_string_unchecked("TrailingParserDescr", 19, 19);
lean_inc(x_27);
x_247 = l_Lean_Name_mkStr2(x_27, x_246);
lean_inc(x_198);
lean_inc(x_247);
lean_inc(x_204);
x_248 = l_Lean_addMacroScope(x_204, x_247, x_198);
x_249 = lean_box(0);
x_250 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_250, 0, x_247);
lean_ctor_set(x_250, 1, x_249);
x_251 = lean_box(0);
x_252 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_252, 0, x_250);
lean_ctor_set(x_252, 1, x_251);
lean_inc(x_212);
x_253 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_253, 0, x_212);
lean_ctor_set(x_253, 1, x_245);
lean_ctor_set(x_253, 2, x_248);
lean_ctor_set(x_253, 3, x_252);
lean_inc(x_212);
x_254 = l_Lean_Syntax_node2(x_212, x_241, x_243, x_253);
lean_inc(x_199);
lean_inc(x_212);
x_255 = l_Lean_Syntax_node1(x_212, x_199, x_254);
lean_inc(x_229);
lean_inc(x_212);
x_256 = l_Lean_Syntax_node2(x_212, x_239, x_229, x_255);
x_257 = lean_mk_string_unchecked("declValSimple", 13, 13);
lean_inc(x_28);
lean_inc(x_27);
x_258 = l_Lean_Name_mkStr4(x_27, x_28, x_96, x_257);
x_259 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_212);
x_260 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_260, 0, x_212);
lean_ctor_set(x_260, 1, x_259);
x_261 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_195);
lean_inc(x_28);
lean_inc(x_27);
x_262 = l_Lean_Name_mkStr4(x_27, x_28, x_195, x_261);
x_263 = lean_mk_string_unchecked("ParserDescr.trailingNode", 24, 24);
x_264 = l_String_toSubstring_x27(x_263);
x_265 = lean_mk_string_unchecked("ParserDescr", 11, 11);
x_266 = lean_mk_string_unchecked("trailingNode", 12, 12);
lean_inc(x_266);
lean_inc(x_265);
x_267 = l_Lean_Name_mkStr2(x_265, x_266);
x_268 = l_Lean_addMacroScope(x_204, x_267, x_198);
lean_inc(x_27);
x_269 = l_Lean_Name_mkStr3(x_27, x_265, x_266);
lean_inc(x_269);
x_270 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_270, 0, x_269);
lean_ctor_set(x_270, 1, x_249);
x_271 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_271, 0, x_269);
x_272 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_272, 0, x_271);
lean_ctor_set(x_272, 1, x_251);
x_273 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_273, 0, x_270);
lean_ctor_set(x_273, 1, x_272);
lean_inc(x_212);
x_274 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_274, 0, x_212);
lean_ctor_set(x_274, 1, x_264);
lean_ctor_set(x_274, 2, x_268);
lean_ctor_set(x_274, 3, x_273);
lean_inc(x_200);
x_275 = l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(x_249, x_200);
if (lean_obj_tag(x_275) == 0)
{
lean_object* x_276; 
lean_dec(x_195);
x_276 = l_Lean_quoteNameMk(x_200);
x_61 = x_196;
x_62 = x_229;
x_63 = x_197;
x_64 = x_199;
x_65 = x_234;
x_66 = x_202;
x_67 = x_262;
x_68 = x_230;
x_69 = x_256;
x_70 = x_260;
x_71 = x_208;
x_72 = x_209;
x_73 = x_232;
x_74 = x_210;
x_75 = x_237;
x_76 = x_211;
x_77 = x_212;
x_78 = x_274;
x_79 = x_214;
x_80 = x_258;
x_81 = x_276;
goto block_95;
}
else
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; 
lean_dec(x_200);
x_277 = lean_ctor_get(x_275, 0);
lean_inc(x_277);
lean_dec(x_275);
x_278 = lean_mk_string_unchecked("quotedName", 10, 10);
lean_inc(x_28);
lean_inc(x_27);
x_279 = l_Lean_Name_mkStr4(x_27, x_28, x_195, x_278);
x_280 = lean_mk_string_unchecked("`", 1, 1);
x_281 = lean_mk_string_unchecked(".", 1, 1);
x_282 = l_String_intercalate(x_281, x_277);
lean_dec(x_281);
x_283 = lean_string_append(x_280, x_282);
lean_dec(x_282);
lean_inc(x_202);
x_284 = l_Lean_Syntax_mkNameLit(x_283, x_202);
x_285 = lean_mk_empty_array_with_capacity(x_193);
x_286 = lean_array_push(x_285, x_284);
lean_inc(x_202);
x_287 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_287, 0, x_202);
lean_ctor_set(x_287, 1, x_279);
lean_ctor_set(x_287, 2, x_286);
x_61 = x_196;
x_62 = x_229;
x_63 = x_197;
x_64 = x_199;
x_65 = x_234;
x_66 = x_202;
x_67 = x_262;
x_68 = x_230;
x_69 = x_256;
x_70 = x_260;
x_71 = x_208;
x_72 = x_209;
x_73 = x_232;
x_74 = x_210;
x_75 = x_237;
x_76 = x_211;
x_77 = x_212;
x_78 = x_274;
x_79 = x_214;
x_80 = x_258;
x_81 = x_287;
goto block_95;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Command_elabSyntax_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_elabSyntax_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_addMacroScopeIfLocal___at___Lean_Elab_Command_elabSyntax_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Command_addMacroScopeIfLocal___at___Lean_Elab_Command_elabSyntax_spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSyntax___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_elabSyntax___lam__0(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSyntax___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Command_elabSyntax___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabSyntax__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Command", 7, 7);
x_6 = lean_mk_string_unchecked("syntax", 6, 6);
lean_inc(x_5);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("Elab", 4, 4);
x_9 = lean_mk_string_unchecked("elabSyntax", 10, 10);
x_10 = l_Lean_Name_mkStr4(x_3, x_8, x_5, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabSyntax), 4, 0);
x_12 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_10, x_11, x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabSyntax_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("Command", 7, 7);
x_5 = lean_mk_string_unchecked("elabSyntax", 10, 10);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(368u);
x_8 = lean_unsigned_to_nat(33u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(401u);
x_11 = lean_unsigned_to_nat(43u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_11);
x_14 = lean_unsigned_to_nat(37u);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_unsigned_to_nat(47u);
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
LEAN_EXPORT uint8_t l_Lean_Elab_Command_elabSyntaxAbbrev___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSyntaxAbbrev___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_mk_string_unchecked("null", 4, 4);
x_11 = l_Lean_Name_mkStr1(x_10);
x_12 = lean_box(2);
x_13 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
lean_ctor_set(x_13, 2, x_1);
x_14 = lean_box(0);
x_15 = l_Lean_Elab_Term_toParserDescr(x_13, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSyntaxAbbrev(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_180; lean_object* x_181; uint8_t x_182; 
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabSyntaxAbbrev___lam__0___boxed), 1, 0);
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("Parser", 6, 6);
x_39 = lean_mk_string_unchecked("Command", 7, 7);
x_180 = lean_mk_string_unchecked("syntaxAbbrev", 12, 12);
lean_inc(x_39);
lean_inc(x_7);
lean_inc(x_6);
x_181 = l_Lean_Name_mkStr4(x_6, x_7, x_39, x_180);
lean_inc(x_1);
x_182 = l_Lean_Syntax_isOfKind(x_1, x_181);
lean_dec(x_181);
if (x_182 == 0)
{
lean_object* x_183; 
lean_dec(x_39);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_183 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_183;
}
else
{
lean_object* x_184; lean_object* x_185; uint8_t x_186; 
x_184 = lean_unsigned_to_nat(0u);
x_185 = l_Lean_Syntax_getArg(x_1, x_184);
x_186 = l_Lean_Syntax_isNone(x_185);
if (x_186 == 0)
{
lean_object* x_187; uint8_t x_188; 
x_187 = lean_unsigned_to_nat(1u);
lean_inc(x_185);
x_188 = l_Lean_Syntax_matchesNull(x_185, x_187);
if (x_188 == 0)
{
lean_object* x_189; 
lean_dec(x_185);
lean_dec(x_39);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_189 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_189;
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; uint8_t x_193; 
x_190 = l_Lean_Syntax_getArg(x_185, x_184);
lean_dec(x_185);
x_191 = lean_mk_string_unchecked("docComment", 10, 10);
lean_inc(x_39);
lean_inc(x_7);
lean_inc(x_6);
x_192 = l_Lean_Name_mkStr4(x_6, x_7, x_39, x_191);
lean_inc(x_190);
x_193 = l_Lean_Syntax_isOfKind(x_190, x_192);
lean_dec(x_192);
if (x_193 == 0)
{
lean_object* x_194; 
lean_dec(x_190);
lean_dec(x_39);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_194 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_194;
}
else
{
lean_object* x_195; 
x_195 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_195, 0, x_190);
x_124 = x_195;
x_125 = x_2;
x_126 = x_3;
x_127 = x_4;
goto block_179;
}
}
}
else
{
lean_object* x_196; 
lean_dec(x_185);
x_196 = lean_box(0);
x_124 = x_196;
x_125 = x_2;
x_126 = x_3;
x_127 = x_4;
goto block_179;
}
}
block_38:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_inc(x_23);
x_27 = l_Lean_Syntax_node3(x_23, x_25, x_11, x_26, x_8);
lean_inc(x_23);
x_28 = l_Lean_Syntax_node2(x_23, x_24, x_22, x_27);
x_29 = lean_mk_string_unchecked("Termination", 11, 11);
x_30 = lean_mk_string_unchecked("suffix", 6, 6);
x_31 = l_Lean_Name_mkStr4(x_6, x_7, x_29, x_30);
lean_inc_n(x_14, 2);
lean_inc(x_23);
x_32 = l_Lean_Syntax_node2(x_23, x_31, x_14, x_14);
lean_inc(x_14);
lean_inc(x_23);
x_33 = l_Lean_Syntax_node4(x_23, x_9, x_12, x_28, x_32, x_14);
lean_inc(x_23);
x_34 = l_Lean_Syntax_node5(x_23, x_10, x_20, x_15, x_21, x_33, x_14);
x_35 = l_Lean_Syntax_node2(x_23, x_13, x_17, x_34);
lean_inc(x_35);
x_36 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand), 4, 1);
lean_closure_set(x_36, 0, x_35);
x_37 = l_Lean_Elab_Command_withMacroExpansion(lean_box(0), x_1, x_35, x_36, x_16, x_18, x_19);
return x_37;
}
block_123:
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_inc(x_41);
x_56 = l_Array_append(lean_box(0), x_41, x_55);
lean_dec(x_55);
lean_inc(x_54);
lean_inc(x_53);
x_57 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_57, 0, x_53);
lean_ctor_set(x_57, 1, x_54);
lean_ctor_set(x_57, 2, x_56);
lean_inc(x_54);
lean_inc(x_53);
x_58 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_58, 0, x_53);
lean_ctor_set(x_58, 1, x_54);
lean_ctor_set(x_58, 2, x_41);
lean_inc_n(x_58, 5);
lean_inc(x_53);
x_59 = l_Lean_Syntax_node6(x_53, x_40, x_57, x_58, x_58, x_58, x_58, x_58);
x_60 = lean_mk_string_unchecked("definition", 10, 10);
lean_inc(x_39);
lean_inc(x_7);
lean_inc(x_6);
x_61 = l_Lean_Name_mkStr4(x_6, x_7, x_39, x_60);
x_62 = lean_mk_string_unchecked("def", 3, 3);
lean_inc(x_53);
x_63 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_63, 0, x_53);
lean_ctor_set(x_63, 1, x_62);
x_64 = lean_mk_string_unchecked("declId", 6, 6);
lean_inc(x_39);
lean_inc(x_7);
lean_inc(x_6);
x_65 = l_Lean_Name_mkStr4(x_6, x_7, x_39, x_64);
lean_inc(x_58);
lean_inc(x_53);
x_66 = l_Lean_Syntax_node2(x_53, x_65, x_52, x_58);
x_67 = lean_mk_string_unchecked("optDeclSig", 10, 10);
lean_inc(x_39);
lean_inc(x_7);
lean_inc(x_6);
x_68 = l_Lean_Name_mkStr4(x_6, x_7, x_39, x_67);
x_69 = lean_mk_string_unchecked("Term", 4, 4);
x_70 = lean_mk_string_unchecked("typeSpec", 8, 8);
lean_inc(x_69);
lean_inc(x_7);
lean_inc(x_6);
x_71 = l_Lean_Name_mkStr4(x_6, x_7, x_69, x_70);
x_72 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_53);
x_73 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_73, 0, x_53);
lean_ctor_set(x_73, 1, x_72);
x_74 = lean_mk_string_unchecked("Lean.ParserDescr", 16, 16);
x_75 = l_String_toSubstring_x27(x_74);
x_76 = lean_mk_string_unchecked("ParserDescr", 11, 11);
lean_inc(x_76);
lean_inc(x_6);
x_77 = l_Lean_Name_mkStr2(x_6, x_76);
lean_inc(x_46);
lean_inc(x_77);
lean_inc(x_42);
x_78 = l_Lean_addMacroScope(x_42, x_77, x_46);
x_79 = lean_box(0);
lean_inc(x_77);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_79);
x_81 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_81, 0, x_77);
x_82 = lean_box(0);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_80);
lean_ctor_set(x_84, 1, x_83);
lean_inc(x_53);
x_85 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_85, 0, x_53);
lean_ctor_set(x_85, 1, x_75);
lean_ctor_set(x_85, 2, x_78);
lean_ctor_set(x_85, 3, x_84);
lean_inc(x_53);
x_86 = l_Lean_Syntax_node2(x_53, x_71, x_73, x_85);
lean_inc(x_54);
lean_inc(x_53);
x_87 = l_Lean_Syntax_node1(x_53, x_54, x_86);
lean_inc(x_58);
lean_inc(x_53);
x_88 = l_Lean_Syntax_node2(x_53, x_68, x_58, x_87);
x_89 = lean_mk_string_unchecked("declValSimple", 13, 13);
lean_inc(x_7);
lean_inc(x_6);
x_90 = l_Lean_Name_mkStr4(x_6, x_7, x_39, x_89);
x_91 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_53);
x_92 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_92, 0, x_53);
lean_ctor_set(x_92, 1, x_91);
x_93 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_69);
lean_inc(x_7);
lean_inc(x_6);
x_94 = l_Lean_Name_mkStr4(x_6, x_7, x_69, x_93);
x_95 = lean_mk_string_unchecked("ParserDescr.nodeWithAntiquot", 28, 28);
x_96 = l_String_toSubstring_x27(x_95);
x_97 = lean_mk_string_unchecked("nodeWithAntiquot", 16, 16);
lean_inc(x_97);
lean_inc(x_76);
x_98 = l_Lean_Name_mkStr2(x_76, x_97);
x_99 = l_Lean_addMacroScope(x_42, x_98, x_46);
lean_inc(x_6);
x_100 = l_Lean_Name_mkStr3(x_6, x_76, x_97);
lean_inc(x_100);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_79);
x_102 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_102, 0, x_100);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_82);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_101);
lean_ctor_set(x_104, 1, x_103);
lean_inc(x_53);
x_105 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_105, 0, x_53);
lean_ctor_set(x_105, 1, x_96);
lean_ctor_set(x_105, 2, x_99);
lean_ctor_set(x_105, 3, x_104);
x_106 = l_Lean_Name_toString(x_50, x_47, x_5);
x_107 = lean_box(2);
x_108 = l_Lean_Syntax_mkStrLit(x_106, x_107);
lean_dec(x_106);
lean_inc(x_51);
x_109 = l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(x_79, x_51);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; 
lean_dec(x_69);
x_110 = l_Lean_quoteNameMk(x_51);
x_8 = x_43;
x_9 = x_90;
x_10 = x_61;
x_11 = x_108;
x_12 = x_92;
x_13 = x_44;
x_14 = x_58;
x_15 = x_66;
x_16 = x_45;
x_17 = x_59;
x_18 = x_48;
x_19 = x_49;
x_20 = x_63;
x_21 = x_88;
x_22 = x_105;
x_23 = x_53;
x_24 = x_94;
x_25 = x_54;
x_26 = x_110;
goto block_38;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_51);
x_111 = lean_ctor_get(x_109, 0);
lean_inc(x_111);
lean_dec(x_109);
x_112 = lean_mk_string_unchecked("quotedName", 10, 10);
lean_inc(x_7);
lean_inc(x_6);
x_113 = l_Lean_Name_mkStr4(x_6, x_7, x_69, x_112);
x_114 = lean_mk_string_unchecked("`", 1, 1);
x_115 = lean_mk_string_unchecked(".", 1, 1);
x_116 = l_String_intercalate(x_115, x_111);
lean_dec(x_115);
x_117 = lean_string_append(x_114, x_116);
lean_dec(x_116);
x_118 = l_Lean_Syntax_mkNameLit(x_117, x_107);
x_119 = lean_unsigned_to_nat(1u);
x_120 = lean_mk_empty_array_with_capacity(x_119);
x_121 = lean_array_push(x_120, x_118);
x_122 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_122, 0, x_107);
lean_ctor_set(x_122, 1, x_113);
lean_ctor_set(x_122, 2, x_121);
x_8 = x_43;
x_9 = x_90;
x_10 = x_61;
x_11 = x_108;
x_12 = x_92;
x_13 = x_44;
x_14 = x_58;
x_15 = x_66;
x_16 = x_45;
x_17 = x_59;
x_18 = x_48;
x_19 = x_49;
x_20 = x_63;
x_21 = x_88;
x_22 = x_105;
x_23 = x_53;
x_24 = x_94;
x_25 = x_54;
x_26 = x_122;
goto block_38;
}
}
block_179:
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; 
x_128 = lean_unsigned_to_nat(2u);
x_129 = l_Lean_Syntax_getArg(x_1, x_128);
x_130 = lean_mk_string_unchecked("ident", 5, 5);
x_131 = l_Lean_Name_mkStr1(x_130);
lean_inc(x_129);
x_132 = l_Lean_Syntax_isOfKind(x_129, x_131);
lean_dec(x_131);
if (x_132 == 0)
{
lean_object* x_133; 
lean_dec(x_129);
lean_dec(x_124);
lean_dec(x_39);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_133 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_125, x_126, x_127);
lean_dec(x_126);
lean_dec(x_125);
return x_133;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; size_t x_137; lean_object* x_138; size_t x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_134 = lean_unsigned_to_nat(4u);
x_135 = l_Lean_Syntax_getArg(x_1, x_134);
x_136 = l_Lean_Syntax_getArgs(x_135);
lean_dec(x_135);
x_137 = lean_array_size(x_136);
x_138 = lean_unsigned_to_nat(0u);
x_139 = lean_usize_of_nat(x_138);
x_140 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_elabSyntax_spec__0(x_137, x_139, x_136);
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
lean_dec(x_140);
x_142 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabSyntaxAbbrev___lam__1___boxed), 9, 1);
lean_closure_set(x_142, 0, x_141);
x_143 = l_Lean_Elab_Command_runTermElabM___redArg(x_142, x_125, x_126, x_127);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; uint8_t x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_143, 1);
lean_inc(x_145);
lean_dec(x_143);
x_146 = lean_ctor_get(x_144, 0);
lean_inc(x_146);
lean_dec(x_144);
x_147 = l_Lean_Elab_Command_getScope___redArg(x_126, x_145);
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_147, 1);
lean_inc(x_149);
lean_dec(x_147);
x_150 = l_Lean_Elab_Command_getRef(x_125, x_126, x_149);
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_150, 1);
lean_inc(x_152);
lean_dec(x_150);
x_153 = l_Lean_Elab_Command_getCurrMacroScope(x_125, x_126, x_152);
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
lean_dec(x_153);
x_156 = l_Lean_Elab_Command_getMainModule___redArg(x_126, x_155);
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
lean_dec(x_156);
x_159 = lean_ctor_get(x_148, 2);
lean_inc(x_159);
lean_dec(x_148);
x_160 = lean_box(0);
x_161 = l_Lean_Syntax_getId(x_129);
lean_inc(x_161);
x_162 = l_Lean_Name_append(x_159, x_161);
x_163 = lean_unbox(x_160);
x_164 = l_Lean_SourceInfo_fromRef(x_151, x_163);
lean_dec(x_151);
x_165 = lean_mk_string_unchecked("declaration", 11, 11);
lean_inc(x_39);
lean_inc(x_7);
lean_inc(x_6);
x_166 = l_Lean_Name_mkStr4(x_6, x_7, x_39, x_165);
x_167 = lean_mk_string_unchecked("declModifiers", 13, 13);
lean_inc(x_39);
lean_inc(x_7);
lean_inc(x_6);
x_168 = l_Lean_Name_mkStr4(x_6, x_7, x_39, x_167);
x_169 = lean_mk_string_unchecked("null", 4, 4);
x_170 = l_Lean_Name_mkStr1(x_169);
x_171 = l_Array_mkArray0(lean_box(0));
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_172; 
x_172 = l_Array_empty(lean_box(0));
x_40 = x_168;
x_41 = x_171;
x_42 = x_157;
x_43 = x_146;
x_44 = x_166;
x_45 = x_125;
x_46 = x_154;
x_47 = x_132;
x_48 = x_126;
x_49 = x_158;
x_50 = x_161;
x_51 = x_162;
x_52 = x_129;
x_53 = x_164;
x_54 = x_170;
x_55 = x_172;
goto block_123;
}
else
{
lean_object* x_173; lean_object* x_174; 
x_173 = lean_ctor_get(x_124, 0);
lean_inc(x_173);
lean_dec(x_124);
x_174 = l_Array_mkArray1___redArg(x_173);
x_40 = x_168;
x_41 = x_171;
x_42 = x_157;
x_43 = x_146;
x_44 = x_166;
x_45 = x_125;
x_46 = x_154;
x_47 = x_132;
x_48 = x_126;
x_49 = x_158;
x_50 = x_161;
x_51 = x_162;
x_52 = x_129;
x_53 = x_164;
x_54 = x_170;
x_55 = x_174;
goto block_123;
}
}
else
{
uint8_t x_175; 
lean_dec(x_129);
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_124);
lean_dec(x_39);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_175 = !lean_is_exclusive(x_143);
if (x_175 == 0)
{
return x_143;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_176 = lean_ctor_get(x_143, 0);
x_177 = lean_ctor_get(x_143, 1);
lean_inc(x_177);
lean_inc(x_176);
lean_dec(x_143);
x_178 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_178, 0, x_176);
lean_ctor_set(x_178, 1, x_177);
return x_178;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSyntaxAbbrev___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Command_elabSyntaxAbbrev___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSyntaxAbbrev___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Command_elabSyntaxAbbrev___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabSyntaxAbbrev__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Command", 7, 7);
x_6 = lean_mk_string_unchecked("syntaxAbbrev", 12, 12);
lean_inc(x_5);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("Elab", 4, 4);
x_9 = lean_mk_string_unchecked("elabSyntaxAbbrev", 16, 16);
x_10 = l_Lean_Name_mkStr4(x_3, x_8, x_5, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabSyntaxAbbrev), 4, 0);
x_12 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_10, x_11, x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabSyntaxAbbrev_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("Command", 7, 7);
x_5 = lean_mk_string_unchecked("elabSyntaxAbbrev", 16, 16);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(403u);
x_8 = lean_unsigned_to_nat(39u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(409u);
x_11 = lean_unsigned_to_nat(49u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_11);
x_14 = lean_unsigned_to_nat(43u);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_unsigned_to_nat(59u);
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
LEAN_EXPORT uint8_t l_Lean_Elab_Command_checkRuleKind(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_name_eq(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_mk_string_unchecked("antiquot", 8, 8);
x_5 = l_Lean_Name_mkStr1(x_4);
x_6 = l_Lean_Name_append(x_2, x_5);
x_7 = lean_name_eq(x_1, x_6);
lean_dec(x_6);
return x_7;
}
else
{
lean_dec(x_2);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_checkRuleKind___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Elab_Command_checkRuleKind(x_1, x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_inferMacroRulesAltKind(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_mk_string_unchecked("Lean", 4, 4);
x_6 = lean_mk_string_unchecked("Parser", 6, 6);
x_7 = lean_mk_string_unchecked("Term", 4, 4);
x_8 = lean_mk_string_unchecked("matchAlt", 8, 8);
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
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
lean_dec(x_1);
lean_inc(x_13);
x_14 = l_Lean_Syntax_matchesNull(x_13, x_12);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_13);
x_15 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_2, x_3, x_4);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Lean_Syntax_getArg(x_13, x_16);
lean_dec(x_13);
lean_inc(x_17);
x_18 = l_Lean_Syntax_matchesNull(x_17, x_12);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_17);
x_19 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_2, x_3, x_4);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_26; 
x_20 = l_Lean_Syntax_getArg(x_17, x_16);
lean_dec(x_17);
x_26 = l_Lean_Syntax_isQuot(x_20);
if (x_26 == 0)
{
if (x_18 == 0)
{
x_21 = x_4;
goto block_25;
}
else
{
lean_object* x_27; uint8_t x_28; 
lean_dec(x_20);
x_27 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_2, x_3, x_4);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
return x_27;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_27);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
x_21 = x_4;
goto block_25;
}
block_25:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = l_Lean_Syntax_getQuotContent(x_20);
x_23 = l_Lean_Syntax_getKind(x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_21);
return x_24;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_inferMacroRulesAltKind___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_inferMacroRulesAltKind(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Command_expandNoKindMacroRulesAux_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_eq(x_3, x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_array_uget(x_2, x_3);
lean_inc(x_10);
x_11 = l_Lean_Elab_Command_inferMacroRulesAltKind(x_10, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_20; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_1);
x_20 = l_Lean_Elab_Command_checkRuleKind(x_12, x_1);
lean_dec(x_12);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_array_push(x_5, x_10);
x_14 = x_21;
goto block_19;
}
else
{
lean_dec(x_10);
x_14 = x_5;
goto block_19;
}
block_19:
{
lean_object* x_15; size_t x_16; size_t x_17; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_usize_of_nat(x_15);
x_17 = lean_usize_add(x_3, x_16);
x_3 = x_17;
x_5 = x_14;
x_8 = x_13;
goto _start;
}
}
else
{
uint8_t x_22; 
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_11);
if (x_22 == 0)
{
return x_11;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_11, 0);
x_24 = lean_ctor_get(x_11, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_11);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
else
{
lean_object* x_26; 
lean_dec(x_1);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_5);
lean_ctor_set(x_26, 1, x_8);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Command_expandNoKindMacroRulesAux_spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_eq(x_3, x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_array_uget(x_2, x_3);
lean_inc(x_10);
x_11 = l_Lean_Elab_Command_inferMacroRulesAltKind(x_10, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_20; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_1);
x_20 = l_Lean_Elab_Command_checkRuleKind(x_12, x_1);
lean_dec(x_12);
if (x_20 == 0)
{
lean_dec(x_10);
x_14 = x_5;
goto block_19;
}
else
{
lean_object* x_21; 
x_21 = lean_array_push(x_5, x_10);
x_14 = x_21;
goto block_19;
}
block_19:
{
lean_object* x_15; size_t x_16; size_t x_17; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_usize_of_nat(x_15);
x_17 = lean_usize_add(x_3, x_16);
x_3 = x_17;
x_5 = x_14;
x_8 = x_13;
goto _start;
}
}
else
{
uint8_t x_22; 
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_11);
if (x_22 == 0)
{
return x_11;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_11, 0);
x_24 = lean_ctor_get(x_11, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_11);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
else
{
lean_object* x_26; 
lean_dec(x_1);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_5);
lean_ctor_set(x_26, 1, x_8);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandNoKindMacroRulesAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_71; lean_object* x_72; 
x_43 = lean_mk_string_unchecked("Lean", 4, 4);
x_44 = lean_mk_string_unchecked("Parser", 6, 6);
x_45 = lean_mk_string_unchecked("Term", 4, 4);
x_46 = lean_mk_string_unchecked("matchAlt", 8, 8);
x_47 = l_Lean_Name_mkStr4(x_43, x_44, x_45, x_46);
x_48 = lean_box(0);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = l_Lean_instInhabitedTSyntax(x_49);
lean_dec(x_49);
x_51 = lean_unsigned_to_nat(0u);
x_71 = lean_array_get(x_50, x_1, x_51);
lean_inc(x_71);
x_72 = l_Lean_Elab_Command_inferMacroRulesAltKind(x_71, x_4, x_5, x_6);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_107; uint8_t x_110; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_110 = l_Lean_Name_isStr(x_73);
if (x_110 == 0)
{
x_107 = x_110;
goto block_109;
}
else
{
lean_object* x_111; lean_object* x_112; uint8_t x_113; 
x_111 = l_Lean_Name_getString_x21(x_73);
x_112 = lean_mk_string_unchecked("antiquot", 8, 8);
x_113 = lean_string_dec_eq(x_111, x_112);
lean_dec(x_112);
lean_dec(x_111);
x_107 = x_113;
goto block_109;
}
block_106:
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_78 = lean_mk_string_unchecked("choice", 6, 6);
x_79 = l_Lean_Name_mkStr1(x_78);
x_80 = lean_name_eq(x_75, x_79);
lean_dec(x_79);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; uint8_t x_83; 
lean_dec(x_71);
x_81 = lean_array_get_size(x_1);
x_82 = lean_mk_empty_array_with_capacity(x_51);
x_83 = lean_nat_dec_lt(x_51, x_81);
if (x_83 == 0)
{
x_52 = x_77;
x_53 = x_76;
x_54 = x_81;
x_55 = x_75;
x_56 = x_82;
x_57 = x_74;
goto block_70;
}
else
{
uint8_t x_84; 
x_84 = lean_nat_dec_le(x_81, x_81);
if (x_84 == 0)
{
x_52 = x_77;
x_53 = x_76;
x_54 = x_81;
x_55 = x_75;
x_56 = x_82;
x_57 = x_74;
goto block_70;
}
else
{
size_t x_85; size_t x_86; lean_object* x_87; 
x_85 = lean_usize_of_nat(x_51);
x_86 = lean_usize_of_nat(x_81);
lean_inc(x_75);
x_87 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_Command_expandNoKindMacroRulesAux_spec__1(x_75, x_1, x_85, x_86, x_82, x_76, x_77, x_74);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
x_52 = x_77;
x_53 = x_76;
x_54 = x_81;
x_55 = x_75;
x_56 = x_88;
x_57 = x_89;
goto block_70;
}
else
{
uint8_t x_90; 
lean_dec(x_81);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_3);
x_90 = !lean_is_exclusive(x_87);
if (x_90 == 0)
{
return x_87;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_87, 0);
x_92 = lean_ctor_get(x_87, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_87);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_75);
lean_dec(x_3);
x_94 = lean_mk_string_unchecked("invalid ", 8, 8);
x_95 = l_Lean_stringToMessageData(x_94);
lean_dec(x_94);
x_96 = l_Lean_stringToMessageData(x_2);
lean_inc(x_96);
x_97 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
x_98 = lean_mk_string_unchecked(" alternative, multiple interpretations for pattern (solution: specify node kind using `", 87, 87);
x_99 = l_Lean_stringToMessageData(x_98);
lean_dec(x_98);
x_100 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_100, 0, x_97);
lean_ctor_set(x_100, 1, x_99);
x_101 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_96);
x_102 = lean_mk_string_unchecked(" (kind := ...) ...`)", 20, 20);
x_103 = l_Lean_stringToMessageData(x_102);
lean_dec(x_102);
x_104 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_104, 0, x_101);
lean_ctor_set(x_104, 1, x_103);
x_105 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__3___redArg(x_71, x_104, x_76, x_77, x_74);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_71);
return x_105;
}
}
block_109:
{
if (x_107 == 0)
{
x_75 = x_73;
x_76 = x_4;
x_77 = x_5;
goto block_106;
}
else
{
lean_object* x_108; 
x_108 = l_Lean_Name_getPrefix(x_73);
lean_dec(x_73);
x_75 = x_108;
x_76 = x_4;
x_77 = x_5;
goto block_106;
}
}
}
else
{
uint8_t x_114; 
lean_dec(x_71);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_114 = !lean_is_exclusive(x_72);
if (x_114 == 0)
{
return x_72;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_72, 0);
x_116 = lean_ctor_get(x_72, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_72);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
block_42:
{
uint8_t x_13; 
x_13 = l_Array_isEmpty___redArg(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_10);
lean_inc(x_3);
lean_inc(x_7);
lean_inc(x_8);
x_15 = lean_apply_5(x_3, x_14, x_9, x_8, x_7, x_12);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_box(0);
lean_inc(x_7);
lean_inc(x_8);
x_19 = lean_apply_5(x_3, x_18, x_11, x_8, x_7, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_Elab_Command_getRef(x_8, x_7, x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_Elab_Command_getCurrMacroScope(x_8, x_7, x_24);
lean_dec(x_8);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = l_Lean_Elab_Command_getMainModule___redArg(x_7, x_26);
lean_dec(x_7);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
x_30 = l_Lean_SourceInfo_fromRef(x_23, x_13);
lean_dec(x_23);
x_31 = lean_mk_string_unchecked("null", 4, 4);
x_32 = l_Lean_Name_mkStr1(x_31);
x_33 = l_Lean_Syntax_node2(x_30, x_32, x_16, x_20);
lean_ctor_set(x_27, 0, x_33);
return x_27;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_ctor_get(x_27, 1);
lean_inc(x_34);
lean_dec(x_27);
x_35 = l_Lean_SourceInfo_fromRef(x_23, x_13);
lean_dec(x_23);
x_36 = lean_mk_string_unchecked("null", 4, 4);
x_37 = l_Lean_Name_mkStr1(x_36);
x_38 = l_Lean_Syntax_node2(x_35, x_37, x_16, x_20);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_34);
return x_39;
}
}
else
{
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
return x_19;
}
}
else
{
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
return x_15;
}
}
else
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_11);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_10);
x_41 = lean_apply_5(x_3, x_40, x_9, x_8, x_7, x_12);
return x_41;
}
}
block_70:
{
lean_object* x_58; uint8_t x_59; 
x_58 = lean_mk_empty_array_with_capacity(x_51);
x_59 = lean_nat_dec_lt(x_51, x_54);
if (x_59 == 0)
{
lean_dec(x_54);
x_7 = x_52;
x_8 = x_53;
x_9 = x_56;
x_10 = x_55;
x_11 = x_58;
x_12 = x_57;
goto block_42;
}
else
{
uint8_t x_60; 
x_60 = lean_nat_dec_le(x_54, x_54);
if (x_60 == 0)
{
lean_dec(x_54);
x_7 = x_52;
x_8 = x_53;
x_9 = x_56;
x_10 = x_55;
x_11 = x_58;
x_12 = x_57;
goto block_42;
}
else
{
size_t x_61; size_t x_62; lean_object* x_63; 
x_61 = lean_usize_of_nat(x_51);
x_62 = lean_usize_of_nat(x_54);
lean_dec(x_54);
lean_inc(x_55);
x_63 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_Command_expandNoKindMacroRulesAux_spec__0(x_55, x_1, x_61, x_62, x_58, x_53, x_52, x_57);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_7 = x_52;
x_8 = x_53;
x_9 = x_56;
x_10 = x_55;
x_11 = x_64;
x_12 = x_65;
goto block_42;
}
else
{
uint8_t x_66; 
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_3);
x_66 = !lean_is_exclusive(x_63);
if (x_66 == 0)
{
return x_63;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_63, 0);
x_68 = lean_ctor_get(x_63, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_63);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Command_expandNoKindMacroRulesAux_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_Command_expandNoKindMacroRulesAux_spec__0(x_1, x_2, x_9, x_10, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Command_expandNoKindMacroRulesAux_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_Command_expandNoKindMacroRulesAux_spec__1(x_1, x_2, x_9, x_10, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandNoKindMacroRulesAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Command_expandNoKindMacroRulesAux(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_strLitToPattern(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Syntax_isStrLit_x3f(x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
x_5 = l_Lean_Macro_throwUnsupported(lean_box(0), x_2, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_box(0);
x_8 = lean_unbox(x_7);
x_9 = l_Lean_mkAtomFrom(x_1, x_6, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_3);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_strLitToPattern___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_strLitToPattern(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_initFn____x40_Lean_Elab_Syntax___hyg_11805_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_2 = lean_mk_string_unchecked("Elab", 4, 4);
x_3 = lean_mk_string_unchecked("defaultInstance", 15, 15);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(0);
x_6 = lean_box(0);
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
lean_inc(x_7);
x_8 = l_Lean_Name_str___override(x_6, x_7);
lean_inc(x_2);
x_9 = l_Lean_Name_str___override(x_8, x_2);
x_10 = lean_mk_string_unchecked("Command", 7, 7);
x_11 = l_Lean_Name_str___override(x_9, x_10);
x_12 = lean_mk_string_unchecked("initFn", 6, 6);
x_13 = l_Lean_Name_str___override(x_11, x_12);
x_14 = lean_mk_string_unchecked("_@", 2, 2);
x_15 = l_Lean_Name_str___override(x_13, x_14);
x_16 = l_Lean_Name_str___override(x_15, x_7);
x_17 = l_Lean_Name_str___override(x_16, x_2);
x_18 = lean_mk_string_unchecked("Syntax", 6, 6);
x_19 = l_Lean_Name_str___override(x_17, x_18);
x_20 = lean_mk_string_unchecked("_hyg", 4, 4);
x_21 = l_Lean_Name_str___override(x_19, x_20);
x_22 = lean_unsigned_to_nat(11805u);
x_23 = l_Lean_Name_num___override(x_21, x_22);
x_24 = lean_unbox(x_5);
x_25 = l_Lean_registerTraceClass(x_4, x_24, x_23, x_1);
return x_25;
}
}
lean_object* initialize_Lean_Elab_Command(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Parser_Syntax(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Util(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Syntax(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Command(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Syntax(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
if (builtin) {res = l___regBuiltin_Lean_Elab_Command_elabDeclareSyntaxCat__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Command_elabDeclareSyntaxCat_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Command_elabSyntax__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Command_elabSyntax_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Command_elabSyntaxAbbrev__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Command_elabSyntaxAbbrev_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l_Lean_Elab_Command_initFn____x40_Lean_Elab_Syntax___hyg_11805_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
