// Lean compiler output
// Module: Lean.Parser.Basic
// Imports: Lean.Parser.Types
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
LEAN_EXPORT lean_object* l_Lean_Parser_checkPrec(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Syntax_foldArgsM___at___Lean_Syntax_foldArgs_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Syntax_foldArgsM___at___Lean_Syntax_foldArgs_spec__0_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_binNumberFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Parser_isQuotableCharDefault(uint32_t);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1438_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepLatest(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_identFnAux_parse___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nodeWithAntiquot___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserCategory;
lean_object* lean_format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkColEq(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_mkAntiquot_docString__1(lean_object*);
lean_object* l_Lean_Parser_ParserState_mkNode(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkNameLit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_instAndThenParser___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_instOrElseParser___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___List_toString___at___Lean_Parser_dbgTraceStateFn_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_quotedCharFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_takeUntilFn___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepTop(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_octalNumberFn___lam__0___boxed(lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_identFnAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_formatStx(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Parser_pushNone;
LEAN_EXPORT lean_object* l_Lean_Parser_runLongestMatchParser(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_decQuotDepth(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_recover_x27___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_noConfusion(lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_mkResult(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nameLitNoAntiquot;
LEAN_EXPORT lean_object* l_Lean_Parser_checkLineEqFn(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_error(lean_object*);
lean_object* l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepNewError(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_instCoeStringParser;
LEAN_EXPORT lean_object* l_Lean_Parser_sepByElemParser(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_setLhsPrecFn___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchFnAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_orelseFn(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_toCtorIdx___boxed(lean_object*);
lean_object* l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_dbgTraceStateFn___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_instBEqRecoveryContext;
LEAN_EXPORT lean_object* l_Lean_Parser_leadingParserAux(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_checkColGe_docString__1(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Parser_Basic_0__Lean_Parser_isToken(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Parser_symbolFnAux___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchStep___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_symbolNoAntiquot___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_toCtorIdx(uint8_t);
LEAN_EXPORT uint8_t l_Lean_Parser_unicodeSymbolFnAux___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_decEqRecoveryContext____x40_Lean_Parser_Basic___hyg_1293____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_leadingParserAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkPrecFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_strAux_parse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_prattParser___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Parser_octalNumberFn___lam__0(uint32_t);
lean_object* l_Lean_RBNode_find___at___Lean_NameMap_contains_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_symbolInfo(lean_object*);
lean_object* l_Lean_Parser_Error_toString(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_rawFn(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Parser_adaptCacheableContextFn(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_andthenInfo(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_leadingNode(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_satisfyFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_noConfusion(lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepByFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParser(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_skip___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1Fn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_andthenInfo___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_identFnAux_parse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_quotedStringFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_recover(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_manyAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_noConfusion___redArg(uint8_t, uint8_t);
lean_object* l_Lean_Parser_SyntaxStack_size(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Parser_whitespace___lam__0(uint32_t);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkIdResult(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_hexDigitFn___boxed(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Parser_checkWsBeforeFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1NoAntiquot(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoImmediateColon___lam__0(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1NoAntiquot___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_fieldIdxFn(lean_object*, lean_object*);
lean_object* l_Lean_registerEnvExtension___redArg(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbol(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Parser_mkIdResult___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_leadingParser___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_instReprRecoveryContext;
LEAN_EXPORT lean_object* l_Lean_Parser_binNumberFn___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_recover_x27(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_forArgsM___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_isQuotableCharDefault___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1Fn(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_andthenFn(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_identFnAux_parse___lam__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkAtomicInfo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchStep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_mkUnexpectedError(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Parser_checkLinebreakBefore(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withForbidden___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM___at___Lean_Syntax_foldArgs_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_setLhsPrecFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instForInProdNameList(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_andthenInfo___lam__0(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at___Lean_SearchPath_findAllWithExt_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotSuffixSplice___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_orelse(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepByInfo(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquotSplice(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_indexed(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Parser_errorAtSavedPosFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_trailingNodeAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_mkResult___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Parser_isIdCont(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchStep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_instDecidableEqRecoveryContext___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_initFn___lam__0____x40_Lean_Parser_Basic___hyg_9337____boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withPosition___lam__0(lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_restore(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_withCacheFn(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Parser_identFnAux_parse___lam__0(uint32_t);
uint8_t l___private_Lean_Parser_Types_0__Lean_Parser_beqError____x40_Lean_Parser_Types___hyg_440_(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_setExpected(lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
extern uint32_t l_Lean_idBeginEscape;
LEAN_EXPORT lean_object* l_Lean_Parser_withoutInfo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_isIdCont___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbol___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_fieldIdx;
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchMkResult(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_noConfusion___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_many1Fn(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withoutPosition___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_whitespace___lam__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Parser_Basic_0__Lean_Parser_decEqRecoveryContext____x40_Lean_Parser_Basic___hyg_1293_(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Parser_chFn___lam__0(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Parser_mkTokenAndFixPos(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_suppressInsideQuot___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8874_(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_noFirstTokenInfo___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepByElemParser___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_stackSize(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM___at___Lean_Syntax_foldArgs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParserFnExtension;
LEAN_EXPORT lean_object* l_Lean_Parser_rawCh(uint32_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbol___boxed(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkPrecFn___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepByNoAntiquot(lean_object*, lean_object*, uint8_t);
lean_object* lean_string_push(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepLatest___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchFnAux_parse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getNumArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkLinebreakBeforeFn___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_symbol___boxed(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_decimalNumberFn_parseOptExp___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkEmptySubstringAt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_hexNumberFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_finishCommentBlock_eoi(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_findSomeRevM_x3f_find___at_____private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkWsBeforeFn___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_errorAtSavedPos(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_updateTokenCache(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_orelseInfo(lean_object*, lean_object*);
lean_object* l_Lean_Parser_SyntaxStack_extract(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_lookaheadFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolInfo___boxed(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkTailWs___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_forArgsM___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_flip(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_popSyntax(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_identEqFn___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_hygieneInfoFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_epsilonInfo;
LEAN_EXPORT lean_object* l_Lean_Parser_symbolNoAntiquot(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_eoi;
LEAN_EXPORT lean_object* l_Lean_Parser_withPosition(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Syntax_foldArgsM___at___Lean_Syntax_foldArgs_spec__0_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_hygieneInfoNoAntiquot;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_finishCommentBlock___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_optionalNoAntiquot(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_dbgTraceState(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_atomic_docString__1(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Parser_instInhabitedLeadingIdentBehavior;
LEAN_EXPORT lean_object* l_Lean_Parser_decimalNumberFn_parseOptDot(lean_object*, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_beqRecoveryContext____x40_Lean_Parser_Basic___hyg_1219____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_eoiFn___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_rawStrLitFnAux_normalState___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_charLitFnAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_next(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolNoAntiquot(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Parser_indexed___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolInfo(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1Info(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_charLitFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_trailingNodeFn(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_identFnAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_forArgsM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_charLitNoAntiquot;
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_decimalNumberFn_parseOptDot___boxed(lean_object*, lean_object*);
uint32_t lean_uint32_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_pushNone___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolNoAntiquot___boxed(lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
lean_object* l_Lean_Parser_adaptCacheableContext(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_replaceLongest___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_recover_docString__1(lean_object*);
lean_object* l_Lean_Name_quickCmp___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_numberFnAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mergeOrElseErrors(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchFnAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepTop___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_takeDigitsFn(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_mkErrorAt(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkStackTopFn___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_SyntaxStack_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_quotedCharCoreFn(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_rawStrLitFnAux_normalState(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotSuffixSplice(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_rawIdentNoAntiquot;
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_noConfusion___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkLhsPrecFn___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_symbolFnAux___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_instReprLeadingIdentBehavior;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_checkLineEq_docString__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_recover___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Parser_decimalNumberFn_parseOptExp___lam__0(uint32_t);
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotFn(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_indexed___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withPositionAfterLinebreak___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_9337_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_manyFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_trailingNode(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_epsilonInfo___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_tokenFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_epsilonInfo___lam__1(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_nameLitAux___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_stringGapFn___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_strLitFnAux(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Parser_hygieneInfoFn___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_notFollowedBy(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_takeWhileFn___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Syntax_foldArgsM___at___Lean_Syntax_foldArgs_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgs___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_symbol(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkLhsPrecFn___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_satisfyFn(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_optionaInfo(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Parser_checkTailWs(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_forArgsM(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mergeErrors___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_many1Unbox___lam__0(lean_object*);
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_lookahead_docString__1(lean_object*);
lean_object* l_Lean_Parser_ParserState_mkUnexpectedTokenErrors(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoImmediateColon;
lean_object* l_Lean_Parser_SyntaxStack_toSubarray(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_setLhsPrecFn___redArg(lean_object*, lean_object*);
lean_object* l_Subarray_get___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_setTailInfo(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkLhsPrecFn___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withPosition___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepPrevError(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoWsBefore(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParser___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParserFn___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_takeUntilFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withoutInfo___boxed(lean_object*);
lean_object* l_Lean_Syntax_mkLit(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_numLitFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquot(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_finishCommentBlock(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nodeInfo(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchFnAux_parse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_takeWhileFn___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withPositionAfterLinebreak(lean_object*);
lean_object* l_Lean_Data_Trie_matchPrefix(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_tokenFnAux(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Parser_isRawStrLitStart(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_rawFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_errorFn___redArg(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withResultOfFn(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_forArgsM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkStackTopFn(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBMap_instForInProd(lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkLhsPrecFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nodeWithAntiquot(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Parser_skip___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_epsilonInfo___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_withForbidden_docString__1(lean_object*);
lean_object* l_Lean_Syntax_getTailInfo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkWsBeforeFn___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_decimalNumberFn_parseScientific(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_many1Unbox___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_satisfySymbolFn(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_strLitFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_orelse_docString__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_initFn___lam__0____x40_Lean_Parser_Basic___hyg_9363____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_many1NoAntiquot(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_node(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withoutForbidden___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_chFn(uint32_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_orelseFnCore___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgs(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_noConfusion___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_isRawStrLitStart___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_numLitNoAntiquot;
LEAN_EXPORT lean_object* l_Lean_Parser_suppressInsideQuot___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParserFn___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_rawStrLitFnAux_closingState(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Parser_Basic_0__Lean_Parser_isIdFirstOrBeginEscape(uint32_t);
lean_object* l_Lean_Parser_ParserState_mkError(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkStackTopFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParser___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withForbidden(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Error_merge(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_andthen(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nodeInfo___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_checkWsBefore_docString__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepPrevError___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mergeOrElseErrors___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_instBEqLeadingIdentBehavior;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_isToken___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_takeWhile1Fn(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nodeFn(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_peekTokenAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkColGe(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_dbgTraceStateFn___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_rawStrLitFnAux_errorUnterminated___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_insert___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_forArgsM___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_atomic(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_antiquotNestedExpr;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_notFollowedBy_docString__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_errorFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_indexed___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Parser_initFn___lam__0____x40_Lean_Parser_Basic___hyg_9337_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Parser_instDecidableEqRecoveryContext(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchMkResult___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nameLitFn(lean_object*, lean_object*);
uint8_t l_Lean_isLetterLike(uint32_t);
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolFn(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Parser_hexNumberFn___lam__0(uint32_t);
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolNoAntiquot___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_anyAux___at___Lean_Parser_checkTailLinebreak_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Parser_binNumberFn___lam__0(uint32_t);
LEAN_EXPORT lean_object* l_Lean_Parser_withoutPosition___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_tokenAntiquotFn(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_anyAux___at___Lean_Parser_checkTailLinebreak_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_rawAux(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_recover___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolInfo___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instInhabited(lean_object*);
lean_object* l_Lean_Parser_ParserState_shrinkStack(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_chFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_scientificLitFn(lean_object*, lean_object*);
extern uint32_t l_Lean_idEndEscape;
LEAN_EXPORT lean_object* l_Lean_Parser_leadingParser(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_decimalNumberFn_parseOptExp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_errorAtSavedPos___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_symbolFnAux(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_FirstTokens_toOptional(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_noConfusion___redArg(uint8_t, uint8_t);
lean_object* l_Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_rawAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_tokenWithAntiquot___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_setPos(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepByFn(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Parser_SyntaxNodeKindSet_insert(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withoutForbidden___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_replaceLongest(lean_object*, lean_object*);
uint8_t l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at___Lean_Parser_ParserState_mkNode_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_tokenWithAntiquot(lean_object*);
uint8_t l_Lean_isSubScriptAlnum(uint32_t);
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoImmediateColon___lam__0___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_addParenHeuristic(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1438____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_symbolFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Parser_trailingLoopStep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_orelseFnCore(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_incQuotDepth(lean_object*);
uint32_t l_Lean_Parser_getNext(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotSpliceAndSuffix(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_skip;
lean_object* l_Lean_Parser_ParserState_mkEOIError(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_recoverFn(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_scientificLitNoAntiquot;
LEAN_EXPORT lean_object* l_Lean_Parser_withResultOfInfo___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_noFirstTokenInfo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbol(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_isIdFirstOrBeginEscape___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_strLitNoAntiquot;
LEAN_EXPORT lean_object* l_Lean_Parser_checkStackTop(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext___redArg____x40_Lean_Parser_Basic___hyg_1438_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_quotedCharCoreFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolInfo(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkLhsPrec(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM___at___Lean_Syntax_foldArgs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_withoutPosition_docString__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchStep___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_dbgTraceStateFn(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchFn(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append(lean_object*, lean_object*, lean_object*);
lean_object* l_Int_toNat(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_finishCommentBlock_eoi___boxed(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_withPosition_docString__1(lean_object*);
uint8_t l_Lean_Parser_SyntaxStack_isEmpty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoWsBeforeFn___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_decimalNumberFn_parseScientific___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_prattParser(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_next_x27(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withResultOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolFnAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoWsBeforeFn___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkLineEq(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_rawStrLitFnAux_errorUnterminated(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_expectTokenFn(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_antiquotExpr;
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedPrattParsingTables;
LEAN_EXPORT lean_object* l_Lean_Parser_atomicFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Parser_identFnAux_parse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_errorAtSavedPosFn(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_identFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_identNoAntiquot;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoWsBeforeFn(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_FirstTokens_seq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkWsBefore(lean_object*);
lean_object* l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instEmptyCollection(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkTokenAndFixPos___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Parser_identFnAux_parse___lam__1(uint32_t);
lean_object* l_Subarray_size___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_takeDigitsFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolFnAux___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_notFollowedByFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withForbidden___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_strAux_parse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withPositionAfterLinebreak___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_initFn___lam__0____x40_Lean_Parser_Basic___hyg_9363_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_hygieneInfoFn___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_identEqFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_rawStrLitFnAux_initState(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_lookahead(lean_object*);
LEAN_EXPORT lean_object* l_List_toString___at___Lean_Parser_dbgTraceStateFn_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_rawIdentFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_noConfusion___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolNoAntiquot(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM___at___Lean_Syntax_foldArgs_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_recover_x27_docString__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_trailingLoop(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_invalidLongestMatchParser(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Parser_identEqFn___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_hexNumberFn___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mergeErrors(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Parser_checkTailLinebreak(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_runLongestMatchParser___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot(lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSpliceFn(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_indexed___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8874____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withoutForbidden(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_notFollowedByFn(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkColEqFn(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_mkUnexpectedTokenError(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_strAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_SyntaxStack_shrink(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_checkColEq_docString__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_rawCh___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_epsilonInfo___lam__1___boxed(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_many1Unbox(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkColGeFn(lean_object*, lean_object*, lean_object*);
lean_object* l_List_appendTR(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_takeWhileFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkTailLinebreak___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withPositionAfterLinebreak___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkTailNoWs___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Subarray_findSomeRevM_x3f_find___at_____private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_setExpectedFn(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_rawStrLitFnAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withResultOfInfo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_errorFn___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_peekToken(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_expectTokenFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_withAntiquot_docString__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_rawStrLitFnAux_closingState___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_findSomeRevM_x3f_find___at_____private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Pi_instInhabited___redArg(lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_eoiFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_beqOrElseOnAntiquotBehavior____x40_Lean_Parser_Basic___hyg_639____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_symbolInfo___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_orelseFnCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_whitespace(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_setLhsPrec(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Parser_checkTailNoWs(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_identEq(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_nameLitAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkColGtFn(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_pushSyntax(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_manyNoAntiquot(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_strAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_pushNone___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_findSomeRevM_x3f_find___at_____private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_hexDigitFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_anyOfFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgs___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_noConfusion___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_indexed___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_instBEqOrElseOnAntiquotBehavior;
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_insert(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkLinebreakBeforeFn___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_mkTrailingNode(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_chFn___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_mkUnexpectedErrorAt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_stringGapFn(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Parser_takeWhileFn___lam__0(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_beqLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8856____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_instOrElseParser;
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParserFnRef;
uint8_t l_instDecidableEqPos(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkNodeToken(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withoutPosition(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_noConfusion___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Parser_Basic_0__Lean_Parser_beqLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8856_(uint8_t, uint8_t);
uint8_t l_instDecidableEqChar(uint32_t, uint32_t);
uint8_t l_Lean_Syntax_isAntiquots(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepByNoAntiquot___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_dbg_trace(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_instAndThenParser;
LEAN_EXPORT uint8_t l___private_Lean_Parser_Basic_0__Lean_Parser_beqOrElseOnAntiquotBehavior____x40_Lean_Parser_Basic___hyg_639_(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Parser_checkColGt(lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
lean_object* l_Lean_Parser_SyntaxStack_back(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_octalNumberFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParserFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withPosition___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Parser_Basic_0__Lean_Parser_beqRecoveryContext____x40_Lean_Parser_Basic___hyg_1219_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolFnAux(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_suppressInsideQuot(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_checkColGt_docString__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepNewError___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_withoutForbidden_docString__1(lean_object*);
uint32_t l_Char_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_optionalFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_decimalNumberFn_parseOptExp___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_decimalNumberFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_9363_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_termParser(lean_object*);
lean_object* l_Lean_Parser_FirstTokens_merge(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkLinebreakBeforeFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___List_toString___at___Lean_Parser_dbgTraceStateFn_spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_mk_string_unchecked(", ", 2, 2);
x_6 = lean_string_append(x_1, x_5);
lean_dec(x_5);
x_7 = lean_box(0);
x_8 = lean_box(0);
x_9 = lean_unbox(x_8);
x_10 = l_Lean_Syntax_formatStx(x_3, x_7, x_9);
x_11 = lean_unsigned_to_nat(120u);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_format_pretty(x_10, x_11, x_12, x_12);
x_14 = lean_string_append(x_6, x_13);
lean_dec(x_13);
x_1 = x_14;
x_2 = x_4;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___Lean_Parser_dbgTraceStateFn_spec__0(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_mk_string_unchecked("[]", 2, 2);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_mk_string_unchecked("[", 1, 1);
x_6 = lean_box(0);
x_7 = lean_box(0);
x_8 = lean_unbox(x_7);
x_9 = l_Lean_Syntax_formatStx(x_4, x_6, x_8);
x_10 = lean_unsigned_to_nat(120u);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_format_pretty(x_9, x_10, x_11, x_11);
x_13 = lean_string_append(x_5, x_12);
lean_dec(x_12);
x_14 = lean_mk_string_unchecked("]", 1, 1);
x_15 = lean_string_append(x_13, x_14);
lean_dec(x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint32_t x_28; lean_object* x_29; 
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
lean_dec(x_1);
x_17 = lean_mk_string_unchecked("[", 1, 1);
x_18 = lean_box(0);
x_19 = lean_box(0);
x_20 = lean_unbox(x_19);
x_21 = l_Lean_Syntax_formatStx(x_16, x_18, x_20);
x_22 = lean_unsigned_to_nat(120u);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_format_pretty(x_21, x_22, x_23, x_23);
x_25 = lean_string_append(x_17, x_24);
lean_dec(x_24);
x_26 = l_List_foldl___at___List_toString___at___Lean_Parser_dbgTraceStateFn_spec__0_spec__0(x_25, x_3);
x_27 = lean_unsigned_to_nat(93u);
x_28 = l_Char_ofNat(x_27);
x_29 = lean_string_push(x_26, x_28);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_dbgTraceStateFn___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_dbgTraceStateFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_30; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = l_Lean_Parser_SyntaxStack_size(x_5);
lean_dec(x_5);
x_7 = lean_apply_2(x_2, x_3, x_4);
lean_inc(x_7);
x_8 = lean_alloc_closure((void*)(l_Lean_Parser_dbgTraceStateFn___lam__0___boxed), 2, 1);
lean_closure_set(x_8, 0, x_7);
x_9 = lean_mk_string_unchecked("\n  pos: ", 8, 8);
x_10 = lean_string_append(x_1, x_9);
lean_dec(x_9);
x_11 = lean_ctor_get(x_7, 2);
lean_inc(x_11);
x_12 = l___private_Init_Data_Repr_0__Nat_reprFast(x_11);
x_13 = lean_string_append(x_10, x_12);
lean_dec(x_12);
x_14 = lean_mk_string_unchecked("\n  err: ", 8, 8);
x_15 = lean_string_append(x_13, x_14);
lean_dec(x_14);
x_30 = lean_ctor_get(x_7, 4);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; 
x_31 = lean_mk_string_unchecked("none", 4, 4);
x_16 = x_31;
goto block_29;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_mk_string_unchecked("(some ", 6, 6);
x_34 = l_Lean_Parser_Error_toString(x_32);
x_35 = l_addParenHeuristic(x_34);
lean_dec(x_34);
x_36 = lean_string_append(x_33, x_35);
lean_dec(x_35);
x_37 = lean_mk_string_unchecked(")", 1, 1);
x_38 = lean_string_append(x_36, x_37);
lean_dec(x_37);
x_16 = x_38;
goto block_29;
}
block_29:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_17 = lean_string_append(x_15, x_16);
lean_dec(x_16);
x_18 = lean_mk_string_unchecked("\n  out: ", 8, 8);
x_19 = lean_string_append(x_17, x_18);
lean_dec(x_18);
x_20 = lean_ctor_get(x_7, 0);
lean_inc(x_20);
lean_dec(x_7);
x_21 = l_Lean_Parser_SyntaxStack_size(x_20);
x_22 = l_Lean_Parser_SyntaxStack_extract(x_20, x_6, x_21);
lean_dec(x_21);
lean_dec(x_6);
lean_dec(x_20);
x_23 = lean_mk_string_unchecked("#", 1, 1);
x_24 = lean_array_to_list(x_22);
x_25 = l_List_toString___at___Lean_Parser_dbgTraceStateFn_spec__0(x_24);
x_26 = lean_string_append(x_23, x_25);
lean_dec(x_25);
x_27 = lean_string_append(x_19, x_26);
lean_dec(x_26);
x_28 = lean_dbg_trace(x_27, x_8);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_dbgTraceStateFn___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_dbgTraceStateFn___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_dbgTraceState(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_dbgTraceStateFn), 4, 2);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_epsilonInfo___lam__0(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_epsilonInfo___lam__1(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_epsilonInfo() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_epsilonInfo___lam__0___boxed), 1, 0);
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_epsilonInfo___lam__1___boxed), 1, 0);
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_epsilonInfo___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_epsilonInfo___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_epsilonInfo___lam__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_epsilonInfo___lam__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkStackTopFn___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = l_Lean_Parser_SyntaxStack_back(x_4);
lean_dec(x_4);
x_6 = lean_apply_1(x_1, x_5);
x_7 = lean_unbox(x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_8 = lean_box(1);
x_9 = lean_box(0);
x_10 = lean_unbox(x_8);
x_11 = l_Lean_Parser_ParserState_mkUnexpectedError(x_3, x_2, x_9, x_10);
return x_11;
}
else
{
lean_dec(x_2);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkStackTopFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_checkStackTopFn___redArg(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkStackTopFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_checkStackTopFn(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkStackTop(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_Parser_epsilonInfo;
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_checkStackTopFn___boxed), 4, 2);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_2);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_andthenFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
lean_inc(x_3);
x_5 = lean_apply_2(x_1, x_3, x_4);
x_6 = lean_ctor_get(x_5, 4);
lean_inc(x_6);
x_7 = lean_box(0);
x_8 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at___Lean_Parser_ParserState_mkNode_spec__0(x_6, x_7);
if (x_8 == 0)
{
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
else
{
lean_object* x_9; 
x_9 = lean_apply_2(x_2, x_3, x_5);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_andthenInfo___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_1(x_1, x_3);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_andthenInfo___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_1(x_1, x_3);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_andthenInfo(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_andthenInfo___lam__0), 3, 2);
lean_closure_set(x_5, 0, x_4);
lean_closure_set(x_5, 1, x_3);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
x_8 = lean_alloc_closure((void*)(l_Lean_Parser_andthenInfo___lam__1), 3, 2);
lean_closure_set(x_8, 0, x_7);
lean_closure_set(x_8, 1, x_6);
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_2, 2);
lean_inc(x_10);
lean_dec(x_2);
x_11 = l_Lean_Parser_FirstTokens_seq(x_9, x_10);
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_8);
lean_ctor_set(x_12, 2, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_andthen(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = l_Lean_Parser_andthenInfo(x_3, x_4);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_8, 0, x_6);
lean_closure_set(x_8, 1, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instAndThenParser___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_box(0);
x_4 = lean_apply_1(x_2, x_3);
x_5 = l_Lean_Parser_andthen(x_1, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_instAndThenParser() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_instAndThenParser___lam__0), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nodeFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Lean_Parser_ParserState_stackSize(x_4);
x_6 = lean_apply_2(x_2, x_3, x_4);
x_7 = l_Lean_Parser_ParserState_mkNode(x_6, x_1, x_5);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_trailingNodeFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Lean_Parser_ParserState_stackSize(x_4);
x_6 = lean_apply_2(x_2, x_3, x_4);
x_7 = l_Lean_Parser_ParserState_mkTrailingNode(x_6, x_1, x_5);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nodeInfo___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_4, x_3);
x_6 = l_Lean_Parser_SyntaxNodeKindSet_insert(x_5, x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nodeInfo(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_inc(x_2);
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_nodeInfo___lam__0), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_3);
lean_ctor_set(x_6, 2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_node(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_inc(x_1);
x_4 = l_Lean_Parser_nodeInfo(x_1, x_3);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_nodeFn), 4, 2);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_errorFn___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_box(0);
x_4 = lean_box(1);
x_5 = lean_unbox(x_4);
x_6 = l_Lean_Parser_ParserState_mkUnexpectedError(x_2, x_1, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_errorFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_errorFn___redArg(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_errorFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_errorFn(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_error(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Parser_epsilonInfo;
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_errorFn___boxed), 3, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_errorAtSavedPosFn(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
lean_dec(x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_dec(x_3);
lean_dec(x_1);
lean_inc(x_4);
return x_4;
}
else
{
if (x_2 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Lean_Parser_ParserState_mkUnexpectedErrorAt(x_4, x_1, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
lean_dec(x_3);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_string_utf8_next(x_11, x_9);
lean_dec(x_9);
lean_dec(x_11);
x_13 = l_Lean_Parser_ParserState_mkUnexpectedErrorAt(x_4, x_1, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_errorAtSavedPosFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_Parser_errorAtSavedPosFn(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("errorAtSavedPos", 15, 15);
x_5 = l_Lean_Name_mkStr3(x_2, x_3, x_4);
x_6 = lean_mk_string_unchecked("Generate an error at the position saved with the `withPosition` combinator.\nIf `delta == true`, then it reports at saved position+1.\nThis useful to make sure a parser consumed at least one character.  ", 201, 201);
x_7 = l_Lean_addBuiltinDocString(x_5, x_6, x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_errorAtSavedPos(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_epsilonInfo___lam__0___boxed), 1, 0);
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_epsilonInfo___lam__1___boxed), 1, 0);
x_5 = lean_box(1);
x_6 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_5);
x_7 = lean_box(x_2);
x_8 = lean_alloc_closure((void*)(l_Lean_Parser_errorAtSavedPosFn___boxed), 4, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_errorAtSavedPos___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l_Lean_Parser_errorAtSavedPos(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkPrecFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_nat_dec_le(x_5, x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_7 = lean_mk_string_unchecked("unexpected token at this precedence level; consider parenthesizing the term", 75, 75);
x_8 = lean_box(0);
x_9 = lean_box(1);
x_10 = lean_unbox(x_9);
x_11 = l_Lean_Parser_ParserState_mkUnexpectedError(x_3, x_7, x_8, x_10);
return x_11;
}
else
{
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkPrecFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_checkPrecFn(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkPrec(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Parser_epsilonInfo;
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_checkPrecFn___boxed), 3, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkLhsPrecFn___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_4 = lean_nat_dec_le(x_1, x_3);
lean_dec(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_5 = lean_mk_string_unchecked("unexpected token at this precedence level; consider parenthesizing the term", 75, 75);
x_6 = lean_box(0);
x_7 = lean_box(1);
x_8 = lean_unbox(x_7);
x_9 = l_Lean_Parser_ParserState_mkUnexpectedError(x_2, x_5, x_6, x_8);
return x_9;
}
else
{
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkLhsPrecFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_checkLhsPrecFn___redArg(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkLhsPrecFn___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_checkLhsPrecFn___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkLhsPrecFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_checkLhsPrecFn(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkLhsPrec(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Parser_epsilonInfo;
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_checkLhsPrecFn___boxed), 3, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_setLhsPrecFn___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_2, 4);
lean_inc(x_3);
x_4 = lean_box(0);
lean_inc(x_3);
x_5 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at___Lean_Parser_ParserState_mkNode_spec__0(x_3, x_4);
if (x_5 == 0)
{
lean_dec(x_3);
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 3);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 5);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_1);
lean_ctor_set(x_10, 2, x_7);
lean_ctor_set(x_10, 3, x_8);
lean_ctor_set(x_10, 4, x_3);
lean_ctor_set(x_10, 5, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_setLhsPrecFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_setLhsPrecFn___redArg(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_setLhsPrecFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_setLhsPrecFn(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_setLhsPrec(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Parser_epsilonInfo;
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_setLhsPrecFn___boxed), 3, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_nat_to_int(x_4);
x_6 = lean_int_add(x_5, x_1);
lean_dec(x_5);
x_7 = l_Int_toNat(x_6);
lean_dec(x_6);
x_8 = lean_ctor_get_uint8(x_2, sizeof(void*)*4);
x_9 = lean_ctor_get(x_2, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 3);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_7);
lean_ctor_set(x_11, 2, x_9);
lean_ctor_set(x_11, 3, x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*4, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth___lam__0___boxed), 2, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = l_Lean_Parser_adaptCacheableContext(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth___lam__0(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_incQuotDepth(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_to_int(x_2);
x_4 = l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth(x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_decQuotDepth(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_to_int(x_2);
x_4 = lean_int_neg(x_3);
lean_dec(x_3);
x_5 = l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth(x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_suppressInsideQuot___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_inc(x_1);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_2);
lean_inc(x_5);
x_8 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_2);
lean_ctor_set(x_8, 2, x_6);
lean_ctor_set(x_8, 3, x_7);
lean_ctor_set_uint8(x_8, sizeof(void*)*4, x_4);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_suppressInsideQuot(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_suppressInsideQuot___lam__0___boxed), 1, 0);
x_3 = l_Lean_Parser_adaptCacheableContext(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_suppressInsideQuot___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_suppressInsideQuot___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_leadingNode(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_inc(x_2);
x_4 = l_Lean_Parser_checkPrec(x_2);
x_5 = l_Lean_Parser_node(x_1, x_3);
x_6 = l_Lean_Parser_setLhsPrec(x_2);
x_7 = l_Lean_Parser_andthen(x_5, x_6);
x_8 = l_Lean_Parser_andthen(x_4, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_trailingNodeAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_inc(x_1);
x_4 = l_Lean_Parser_nodeInfo(x_1, x_3);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_trailingNodeFn), 4, 2);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_trailingNode(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_inc(x_2);
x_5 = l_Lean_Parser_checkPrec(x_2);
x_6 = l_Lean_Parser_checkLhsPrec(x_3);
x_7 = l_Lean_Parser_trailingNodeAux(x_1, x_4);
x_8 = l_Lean_Parser_setLhsPrec(x_2);
x_9 = l_Lean_Parser_andthen(x_7, x_8);
x_10 = l_Lean_Parser_andthen(x_6, x_9);
x_11 = l_Lean_Parser_andthen(x_5, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mergeOrElseErrors(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 3);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 4);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 5);
lean_inc(x_10);
if (lean_obj_tag(x_9) == 0)
{
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_9, 0);
lean_inc(x_15);
lean_dec(x_9);
x_16 = l_instDecidableEqPos(x_7, x_3);
if (x_16 == 0)
{
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
return x_1;
}
else
{
lean_dec(x_1);
if (x_4 == 0)
{
lean_dec(x_2);
x_11 = x_15;
goto block_14;
}
else
{
lean_object* x_17; 
x_17 = l_Lean_Parser_Error_merge(x_2, x_15);
x_11 = x_17;
goto block_14;
}
}
}
block_14:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_6);
lean_ctor_set(x_13, 2, x_7);
lean_ctor_set(x_13, 3, x_8);
lean_ctor_set(x_13, 4, x_12);
lean_ctor_set(x_13, 5, x_10);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mergeOrElseErrors___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_4);
lean_dec(x_4);
x_6 = l_Lean_Parser_mergeOrElseErrors(x_1, x_2, x_3, x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_toCtorIdx(uint8_t x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Parser_OrElseOnAntiquotBehavior_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_noConfusion___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_noConfusion___redArg(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_OrElseOnAntiquotBehavior_noConfusion___redArg___lam__0___boxed), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_noConfusion(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_OrElseOnAntiquotBehavior_noConfusion___redArg(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_noConfusion___redArg___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_OrElseOnAntiquotBehavior_noConfusion___redArg___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_noConfusion___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lean_Parser_OrElseOnAntiquotBehavior_noConfusion___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_noConfusion___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_Lean_Parser_OrElseOnAntiquotBehavior_noConfusion(x_1, x_5, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Parser_Basic_0__Lean_Parser_beqOrElseOnAntiquotBehavior____x40_Lean_Parser_Basic___hyg_639_(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_Parser_OrElseOnAntiquotBehavior_toCtorIdx(x_1);
x_4 = l_Lean_Parser_OrElseOnAntiquotBehavior_toCtorIdx(x_2);
x_5 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_beqOrElseOnAntiquotBehavior____x40_Lean_Parser_Basic___hyg_639____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l___private_Lean_Parser_Basic_0__Lean_Parser_beqOrElseOnAntiquotBehavior____x40_Lean_Parser_Basic___hyg_639_(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Parser_instBEqOrElseOnAntiquotBehavior() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Parser_Basic_0__Lean_Parser_beqOrElseOnAntiquotBehavior____x40_Lean_Parser_Basic___hyg_639____boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_orelseFnCore___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_mk_string_unchecked("choice", 6, 6);
x_4 = l_Lean_Name_mkStr1(x_3);
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = l_Lean_Parser_ParserState_pushSyntax(x_2, x_1);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = l_Lean_Syntax_getArgs(x_1);
lean_dec(x_1);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = l_Array_append(lean_box(0), x_9, x_8);
lean_dec(x_8);
x_11 = lean_ctor_get(x_7, 1);
lean_inc(x_11);
lean_dec(x_7);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_2, 2);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 3);
lean_inc(x_15);
x_16 = lean_ctor_get(x_2, 4);
lean_inc(x_16);
x_17 = lean_ctor_get(x_2, 5);
lean_inc(x_17);
lean_dec(x_2);
x_18 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_13);
lean_ctor_set(x_18, 2, x_14);
lean_ctor_set(x_18, 3, x_15);
lean_ctor_set(x_18, 4, x_16);
lean_ctor_set(x_18, 5, x_17);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_orelseFnCore(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = l_Lean_Parser_ParserState_stackSize(x_5);
x_7 = lean_ctor_get(x_5, 2);
lean_inc(x_7);
lean_inc(x_4);
x_8 = lean_apply_2(x_1, x_4, x_5);
x_9 = lean_ctor_get(x_8, 4);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_17; lean_object* x_18; lean_object* x_29; uint8_t x_30; lean_object* x_31; uint8_t x_32; uint8_t x_38; lean_object* x_54; uint8_t x_55; uint8_t x_56; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
x_11 = l_Lean_Parser_SyntaxStack_back(x_10);
lean_dec(x_10);
x_54 = lean_box(0);
x_55 = lean_unbox(x_54);
x_56 = l___private_Lean_Parser_Basic_0__Lean_Parser_beqOrElseOnAntiquotBehavior____x40_Lean_Parser_Basic___hyg_639_(x_3, x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_57 = l_Lean_Parser_ParserState_stackSize(x_8);
x_58 = lean_unsigned_to_nat(1u);
x_59 = lean_nat_add(x_6, x_58);
x_60 = lean_nat_dec_eq(x_57, x_59);
lean_dec(x_59);
lean_dec(x_57);
if (x_60 == 0)
{
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
return x_8;
}
else
{
x_38 = x_56;
goto block_53;
}
}
else
{
x_38 = x_56;
goto block_53;
}
block_16:
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Lean_Parser_ParserState_restore(x_13, x_6, x_12);
lean_dec(x_6);
x_15 = l_Lean_Parser_ParserState_pushSyntax(x_14, x_11);
return x_15;
}
block_28:
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = l_Lean_Parser_SyntaxStack_back(x_19);
lean_dec(x_19);
lean_inc(x_20);
x_21 = l_Lean_Syntax_isAntiquots(x_20);
if (x_21 == 0)
{
lean_dec(x_20);
x_12 = x_17;
x_13 = x_18;
goto block_16;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_17);
x_22 = l_Lean_Parser_ParserState_popSyntax(x_18);
x_23 = l_Lean_Parser_orelseFnCore___lam__0(x_11, x_22);
x_24 = l_Lean_Parser_orelseFnCore___lam__0(x_20, x_23);
x_25 = lean_mk_string_unchecked("choice", 6, 6);
x_26 = l_Lean_Name_mkStr1(x_25);
x_27 = l_Lean_Parser_ParserState_mkNode(x_24, x_26, x_6);
lean_dec(x_6);
return x_27;
}
}
block_37:
{
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_33 = l_Lean_Parser_ParserState_stackSize(x_31);
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_nat_add(x_6, x_34);
x_36 = lean_nat_dec_eq(x_33, x_35);
lean_dec(x_35);
lean_dec(x_33);
if (x_36 == 0)
{
if (x_30 == 0)
{
x_17 = x_29;
x_18 = x_31;
goto block_28;
}
else
{
x_12 = x_29;
x_13 = x_31;
goto block_16;
}
}
else
{
x_17 = x_29;
x_18 = x_31;
goto block_28;
}
}
else
{
x_12 = x_29;
x_13 = x_31;
goto block_16;
}
}
block_53:
{
if (x_38 == 0)
{
uint8_t x_39; 
lean_inc(x_11);
x_39 = l_Lean_Syntax_isAntiquots(x_11);
if (x_39 == 0)
{
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
return x_8;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_40 = lean_ctor_get(x_8, 2);
lean_inc(x_40);
x_41 = l_Lean_Parser_ParserState_restore(x_8, x_6, x_7);
x_42 = lean_apply_2(x_2, x_4, x_41);
x_43 = lean_ctor_get(x_42, 4);
lean_inc(x_43);
x_44 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at___Lean_Parser_ParserState_mkNode_spec__0(x_43, x_9);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = l_Lean_Parser_ParserState_restore(x_42, x_6, x_40);
lean_dec(x_6);
x_46 = l_Lean_Parser_ParserState_pushSyntax(x_45, x_11);
return x_46;
}
else
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_ctor_get(x_42, 2);
lean_inc(x_47);
x_48 = lean_nat_dec_lt(x_40, x_47);
if (x_48 == 0)
{
uint8_t x_49; 
x_49 = lean_nat_dec_lt(x_47, x_40);
lean_dec(x_47);
if (x_49 == 0)
{
lean_object* x_50; uint8_t x_51; uint8_t x_52; 
x_50 = lean_box(2);
x_51 = lean_unbox(x_50);
x_52 = l___private_Lean_Parser_Basic_0__Lean_Parser_beqOrElseOnAntiquotBehavior____x40_Lean_Parser_Basic___hyg_639_(x_3, x_51);
if (x_52 == 0)
{
x_29 = x_40;
x_30 = x_44;
x_31 = x_42;
x_32 = x_44;
goto block_37;
}
else
{
x_29 = x_40;
x_30 = x_44;
x_31 = x_42;
x_32 = x_49;
goto block_37;
}
}
else
{
x_29 = x_40;
x_30 = x_44;
x_31 = x_42;
x_32 = x_49;
goto block_37;
}
}
else
{
lean_dec(x_47);
lean_dec(x_40);
lean_dec(x_11);
lean_dec(x_6);
return x_42;
}
}
}
}
else
{
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
return x_8;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_61 = lean_ctor_get(x_9, 0);
lean_inc(x_61);
lean_dec(x_9);
x_62 = lean_ctor_get(x_8, 2);
lean_inc(x_62);
x_63 = l_instDecidableEqPos(x_62, x_7);
lean_dec(x_62);
if (x_63 == 0)
{
lean_dec(x_61);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
return x_8;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_inc(x_7);
x_64 = l_Lean_Parser_ParserState_restore(x_8, x_6, x_7);
lean_dec(x_6);
x_65 = lean_apply_2(x_2, x_4, x_64);
x_66 = l_Lean_Parser_mergeOrElseErrors(x_65, x_61, x_7, x_63);
lean_dec(x_7);
return x_66;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_orelseFnCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_Lean_Parser_orelseFnCore(x_1, x_2, x_6, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_orelseFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_box(2);
x_6 = lean_unbox(x_5);
x_7 = l_Lean_Parser_orelseFnCore(x_1, x_2, x_6, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_orelseInfo(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_andthenInfo___lam__0), 3, 2);
lean_closure_set(x_5, 0, x_4);
lean_closure_set(x_5, 1, x_3);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
x_8 = lean_alloc_closure((void*)(l_Lean_Parser_andthenInfo___lam__1), 3, 2);
lean_closure_set(x_8, 0, x_7);
lean_closure_set(x_8, 1, x_6);
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_2, 2);
lean_inc(x_10);
lean_dec(x_2);
x_11 = l_Lean_Parser_FirstTokens_merge(x_9, x_10);
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_8);
lean_ctor_set(x_12, 2, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_orelse_docString__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("orelse", 6, 6);
x_5 = l_Lean_Name_mkStr3(x_2, x_3, x_4);
x_6 = lean_mk_string_unchecked("Run `p`, falling back to `q` if `p` failed without consuming any input.\n\nNOTE: In order for the pretty printer to retrace an `orelse`, `p` must be a call to `node` or some other parser\nproducing a single node kind. Nested `orelse` calls are flattened for this, i.e. `(node k1 p1 <|> node k2 p2) <|> ...`\nis fine as well. ", 321, 321);
x_7 = l_Lean_addBuiltinDocString(x_5, x_6, x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_orelse(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = l_Lean_Parser_orelseInfo(x_3, x_4);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_alloc_closure((void*)(l_Lean_Parser_orelseFn), 4, 2);
lean_closure_set(x_8, 0, x_6);
lean_closure_set(x_8, 1, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instOrElseParser___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_box(0);
x_4 = lean_apply_1(x_2, x_3);
x_5 = l_Lean_Parser_orelse(x_1, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_instOrElseParser() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_instOrElseParser___lam__0), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_noFirstTokenInfo(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_box(1);
lean_inc(x_3);
lean_inc(x_2);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_noFirstTokenInfo___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_noFirstTokenInfo(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_atomicFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
lean_inc(x_3);
x_4 = lean_apply_2(x_1, x_2, x_3);
x_5 = lean_ctor_get(x_4, 4);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_dec(x_3);
return x_4;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_4, 4);
lean_dec(x_7);
x_8 = lean_ctor_get(x_4, 2);
lean_dec(x_8);
x_9 = lean_ctor_get(x_3, 2);
lean_inc(x_9);
lean_dec(x_3);
lean_ctor_set(x_4, 2, x_9);
return x_4;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_4, 1);
x_12 = lean_ctor_get(x_4, 3);
x_13 = lean_ctor_get(x_4, 5);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_4);
x_14 = lean_ctor_get(x_3, 2);
lean_inc(x_14);
lean_dec(x_3);
x_15 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set(x_15, 2, x_14);
lean_ctor_set(x_15, 3, x_12);
lean_ctor_set(x_15, 4, x_5);
lean_ctor_set(x_15, 5, x_13);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_atomic_docString__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("atomic", 6, 6);
x_5 = l_Lean_Name_mkStr3(x_2, x_3, x_4);
x_6 = lean_mk_string_unchecked("The `atomic(p)` parser parses `p`, returns the same result as `p` and fails iff `p` fails,\nbut if `p` fails after consuming some tokens `atomic(p)` will fail without consuming tokens.\nThis is important for the `p <|> q` combinator, because it is not backtracking, and will fail if\n`p` fails after consuming some tokens. To get backtracking behavior, use `atomic(p) <|> q` instead.\n\nThis parser has the same arity as `p` - it produces the same result as `p`. ", 458, 458);
x_7 = l_Lean_addBuiltinDocString(x_5, x_6, x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_atomic(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_atomicFn), 3, 1);
lean_closure_set(x_4, 0, x_3);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Parser_Basic_0__Lean_Parser_beqRecoveryContext____x40_Lean_Parser_Basic___hyg_1219_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = l_instDecidableEqPos(x_3, x_5);
if (x_7 == 0)
{
return x_7;
}
else
{
uint8_t x_8; 
x_8 = lean_nat_dec_eq(x_4, x_6);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_beqRecoveryContext____x40_Lean_Parser_Basic___hyg_1219____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Parser_Basic_0__Lean_Parser_beqRecoveryContext____x40_Lean_Parser_Basic___hyg_1219_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_instBEqRecoveryContext() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Parser_Basic_0__Lean_Parser_beqRecoveryContext____x40_Lean_Parser_Basic___hyg_1219____boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Parser_Basic_0__Lean_Parser_decEqRecoveryContext____x40_Lean_Parser_Basic___hyg_1293_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = l_instDecidableEqPos(x_3, x_5);
if (x_7 == 0)
{
return x_7;
}
else
{
uint8_t x_8; 
x_8 = lean_nat_dec_eq(x_4, x_6);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_decEqRecoveryContext____x40_Lean_Parser_Basic___hyg_1293____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Parser_Basic_0__Lean_Parser_decEqRecoveryContext____x40_Lean_Parser_Basic___hyg_1293_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_instDecidableEqRecoveryContext(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l___private_Lean_Parser_Basic_0__Lean_Parser_decEqRecoveryContext____x40_Lean_Parser_Basic___hyg_1293_(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instDecidableEqRecoveryContext___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Parser_instDecidableEqRecoveryContext(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext___redArg____x40_Lean_Parser_Basic___hyg_1438_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_2 = lean_mk_string_unchecked("{ ", 2, 2);
x_3 = lean_box(0);
x_4 = lean_mk_string_unchecked("initialPos", 10, 10);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_mk_string_unchecked(" := ", 4, 4);
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_7);
lean_inc(x_8);
x_9 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(14u);
x_11 = lean_nat_to_int(x_10);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_mk_string_unchecked("{ byteIdx := ", 13, 13);
x_14 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = l___private_Init_Data_Repr_0__Nat_reprFast(x_12);
x_16 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_mk_string_unchecked(" }", 2, 2);
x_19 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_19, 0, x_18);
lean_inc(x_19);
x_20 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_23, 0, x_21);
x_24 = lean_unbox(x_22);
lean_ctor_set_uint8(x_23, sizeof(void*)*1, x_24);
x_25 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_25, 0, x_9);
lean_ctor_set(x_25, 1, x_23);
x_26 = lean_mk_string_unchecked(",", 1, 1);
x_27 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_box(1);
x_30 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_mk_string_unchecked("initialSize", 11, 11);
x_32 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_8);
x_35 = lean_unsigned_to_nat(15u);
x_36 = lean_nat_to_int(x_35);
x_37 = lean_ctor_get(x_1, 1);
lean_inc(x_37);
lean_dec(x_1);
x_38 = l___private_Init_Data_Repr_0__Nat_reprFast(x_37);
x_39 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_40 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_40, 0, x_36);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_41, 0, x_40);
x_42 = lean_unbox(x_22);
lean_ctor_set_uint8(x_41, sizeof(void*)*1, x_42);
x_43 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_43, 0, x_34);
lean_ctor_set(x_43, 1, x_41);
x_44 = lean_unsigned_to_nat(2u);
x_45 = lean_nat_to_int(x_44);
x_46 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_46, 0, x_2);
x_47 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_43);
x_48 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_19);
x_49 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_49, 0, x_45);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_50, 0, x_49);
x_51 = lean_unbox(x_22);
lean_ctor_set_uint8(x_50, sizeof(void*)*1, x_51);
return x_50;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1438_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext___redArg____x40_Lean_Parser_Basic___hyg_1438_(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1438____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1438_(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_instReprRecoveryContext() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1438____boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_recoverFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
lean_inc(x_4);
lean_inc(x_3);
x_5 = lean_apply_2(x_1, x_3, x_4);
x_6 = lean_ctor_get(x_5, 4);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_4, 2);
lean_inc(x_9);
lean_dec(x_4);
x_10 = l_Lean_Parser_SyntaxStack_size(x_8);
lean_dec(x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_ctor_get(x_5, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_5, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_5, 2);
lean_inc(x_14);
x_15 = lean_ctor_get(x_5, 3);
lean_inc(x_15);
x_16 = lean_box(0);
x_17 = lean_ctor_get(x_5, 5);
lean_inc(x_17);
lean_dec(x_5);
x_18 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_13);
lean_ctor_set(x_18, 2, x_14);
lean_ctor_set(x_18, 3, x_15);
lean_ctor_set(x_18, 4, x_16);
lean_ctor_set(x_18, 5, x_17);
x_19 = lean_apply_3(x_2, x_11, x_3, x_18);
x_20 = lean_ctor_get(x_19, 4);
lean_inc(x_20);
x_21 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at___Lean_Parser_ParserState_mkNode_spec__0(x_20, x_16);
if (x_21 == 0)
{
lean_dec(x_7);
return x_19;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_19, 2);
lean_inc(x_24);
x_25 = lean_ctor_get(x_19, 3);
lean_inc(x_25);
x_26 = lean_ctor_get(x_19, 5);
lean_inc(x_26);
lean_dec(x_19);
lean_inc(x_22);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_22);
lean_ctor_set(x_27, 1, x_7);
lean_inc(x_24);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_24);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_array_push(x_26, x_28);
x_30 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_30, 0, x_22);
lean_ctor_set(x_30, 1, x_23);
lean_ctor_set(x_30, 2, x_24);
lean_ctor_set(x_30, 3, x_25);
lean_ctor_set(x_30, 4, x_16);
lean_ctor_set(x_30, 5, x_29);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_recover_x27_docString__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("recover'", 8, 8);
x_5 = l_Lean_Name_mkStr3(x_2, x_3, x_4);
x_6 = lean_mk_string_unchecked("Recover from errors in `parser` using `handler` to consume input until a known-good state has appeared.\nIf `handler` fails itself, then no recovery is performed.\n\n`handler` is provided with information about the failing parser's effects , and it is run in the\nstate immediately after the failure.\n\nThe interactions between <|> and `recover'` are subtle, especially for syntactic\ncategories that admit user extension. Consider avoiding it in these cases. ", 454, 454);
x_7 = l_Lean_addBuiltinDocString(x_5, x_6, x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_recover_x27___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_apply_1(x_1, x_2);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_apply_2(x_6, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_recover_x27(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_recover_x27___lam__0), 4, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_recoverFn), 4, 2);
lean_closure_set(x_6, 0, x_5);
lean_closure_set(x_6, 1, x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_recover_docString__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("recover", 7, 7);
x_5 = l_Lean_Name_mkStr3(x_2, x_3, x_4);
x_6 = lean_mk_string_unchecked("Recover from errors in `parser` using `handler` to consume input until a known-good state has appeared.\nIf `handler` fails itself, then no recovery is performed.\n\n`handler` is run in the state immediately after the failure.\n\nThe interactions between <|> and `recover` are subtle, especially for syntactic\ncategories that admit user extension. Consider avoiding it in these cases. ", 380, 380);
x_7 = l_Lean_addBuiltinDocString(x_5, x_6, x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_recover___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_recover(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_recover___lam__0___boxed), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = l_Lean_Parser_recover_x27(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_recover___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_recover___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_optionalFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_4 = l_Lean_Parser_ParserState_stackSize(x_3);
lean_inc(x_3);
x_10 = lean_apply_2(x_1, x_2, x_3);
x_11 = lean_ctor_get(x_10, 4);
lean_inc(x_11);
x_12 = lean_box(0);
x_13 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at___Lean_Parser_ParserState_mkNode_spec__0(x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_3, 2);
lean_inc(x_14);
lean_dec(x_3);
x_15 = lean_ctor_get(x_10, 2);
lean_inc(x_15);
x_16 = l_instDecidableEqPos(x_15, x_14);
lean_dec(x_15);
if (x_16 == 0)
{
lean_dec(x_14);
x_5 = x_10;
goto block_9;
}
else
{
lean_object* x_17; 
x_17 = l_Lean_Parser_ParserState_restore(x_10, x_4, x_14);
x_5 = x_17;
goto block_9;
}
}
else
{
lean_dec(x_3);
x_5 = x_10;
goto block_9;
}
block_9:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_mk_string_unchecked("null", 4, 4);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = l_Lean_Parser_ParserState_mkNode(x_5, x_7, x_4);
lean_dec(x_4);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_optionaInfo(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_Lean_Parser_FirstTokens_toOptional(x_4);
x_6 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_3);
lean_ctor_set(x_6, 2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_optionalNoAntiquot(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_optionaInfo(x_2);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_optionalFn), 3, 1);
lean_closure_set(x_5, 0, x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_lookaheadFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
lean_inc(x_3);
x_4 = lean_apply_2(x_1, x_2, x_3);
x_5 = lean_ctor_get(x_4, 4);
lean_inc(x_5);
x_6 = lean_box(0);
x_7 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at___Lean_Parser_ParserState_mkNode_spec__0(x_5, x_6);
if (x_7 == 0)
{
lean_dec(x_3);
return x_4;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Lean_Parser_ParserState_stackSize(x_3);
x_9 = lean_ctor_get(x_3, 2);
lean_inc(x_9);
lean_dec(x_3);
x_10 = l_Lean_Parser_ParserState_restore(x_4, x_8, x_9);
lean_dec(x_8);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_lookahead_docString__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("lookahead", 9, 9);
x_5 = l_Lean_Name_mkStr3(x_2, x_3, x_4);
x_6 = lean_mk_string_unchecked("`lookahead(p)` runs `p` and fails if `p` does, but it produces no parse nodes and rewinds the\nposition to the original state on success. So for example `lookahead(\"=>\")` will ensure that the\nnext token is `\"=>\"`, without actually consuming this token.\n\nThis parser has arity 0 - it does not capture anything. ", 309, 309);
x_7 = l_Lean_addBuiltinDocString(x_5, x_6, x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_lookahead(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_lookaheadFn), 3, 1);
lean_closure_set(x_4, 0, x_3);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_notFollowedByFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = l_Lean_Parser_ParserState_stackSize(x_4);
x_6 = lean_ctor_get(x_4, 2);
lean_inc(x_6);
x_7 = lean_apply_2(x_1, x_3, x_4);
x_8 = lean_ctor_get(x_7, 4);
lean_inc(x_8);
x_9 = lean_box(0);
x_10 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at___Lean_Parser_ParserState_mkNode_spec__0(x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = l_Lean_Parser_ParserState_restore(x_7, x_5, x_6);
lean_dec(x_5);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = l_Lean_Parser_ParserState_restore(x_7, x_5, x_6);
lean_dec(x_5);
x_13 = lean_mk_string_unchecked("unexpected ", 11, 11);
x_14 = lean_string_append(x_13, x_2);
x_15 = lean_box(0);
x_16 = l_Lean_Parser_ParserState_mkUnexpectedError(x_12, x_14, x_15, x_10);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_notFollowedByFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_notFollowedByFn(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_notFollowedBy_docString__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("notFollowedBy", 13, 13);
x_5 = l_Lean_Name_mkStr3(x_2, x_3, x_4);
x_6 = lean_mk_string_unchecked("`notFollowedBy(p, \"foo\")` succeeds iff `p` fails;\nif `p` succeeds then it fails with the message `\"unexpected foo\"`.\n\nThis parser has arity 0 - it does not capture anything. ", 174, 174);
x_7 = l_Lean_addBuiltinDocString(x_5, x_6, x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_notFollowedBy(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_epsilonInfo___lam__0___boxed), 1, 0);
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_epsilonInfo___lam__1___boxed), 1, 0);
x_5 = lean_box(1);
x_6 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_5);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_Parser_notFollowedByFn___boxed), 4, 2);
lean_closure_set(x_8, 0, x_7);
lean_closure_set(x_8, 1, x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_manyAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = l_Lean_Parser_ParserState_stackSize(x_3);
x_5 = lean_ctor_get(x_3, 2);
lean_inc(x_5);
lean_inc(x_1);
lean_inc(x_2);
x_6 = lean_apply_2(x_1, x_2, x_3);
x_7 = lean_ctor_get(x_6, 4);
lean_inc(x_7);
x_8 = lean_box(0);
x_9 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at___Lean_Parser_ParserState_mkNode_spec__0(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
lean_dec(x_2);
lean_dec(x_1);
x_10 = lean_ctor_get(x_6, 2);
lean_inc(x_10);
x_11 = l_instDecidableEqPos(x_5, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
else
{
lean_object* x_12; 
x_12 = l_Lean_Parser_ParserState_restore(x_6, x_4, x_5);
lean_dec(x_4);
return x_12;
}
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_6, 2);
lean_inc(x_13);
x_14 = l_instDecidableEqPos(x_5, x_13);
lean_dec(x_13);
lean_dec(x_5);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_4, x_15);
x_17 = l_Lean_Parser_ParserState_stackSize(x_6);
x_18 = lean_nat_dec_lt(x_16, x_17);
lean_dec(x_17);
lean_dec(x_16);
if (x_18 == 0)
{
lean_dec(x_4);
x_3 = x_6;
goto _start;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_mk_string_unchecked("null", 4, 4);
x_21 = l_Lean_Name_mkStr1(x_20);
x_22 = l_Lean_Parser_ParserState_mkNode(x_6, x_21, x_4);
lean_dec(x_4);
x_3 = x_22;
goto _start;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_24 = lean_mk_string_unchecked("invalid 'many' parser combinator application, parser did not consume anything", 77, 77);
x_25 = lean_box(0);
x_26 = l_Lean_Parser_ParserState_mkUnexpectedError(x_6, x_24, x_25, x_9);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_manyFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = l_Lean_Parser_ParserState_stackSize(x_3);
x_5 = l_Lean_Parser_manyAux(x_1, x_2, x_3);
x_6 = lean_mk_string_unchecked("null", 4, 4);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = l_Lean_Parser_ParserState_mkNode(x_5, x_7, x_4);
lean_dec(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_manyNoAntiquot(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_noFirstTokenInfo(x_2);
lean_dec(x_2);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_manyFn), 3, 1);
lean_closure_set(x_5, 0, x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_many1Fn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = l_Lean_Parser_ParserState_stackSize(x_3);
lean_inc(x_1);
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_manyAux), 3, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = l_Lean_Parser_andthenFn(x_1, x_5, x_2, x_3);
x_7 = lean_mk_string_unchecked("null", 4, 4);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = l_Lean_Parser_ParserState_mkNode(x_6, x_8, x_4);
lean_dec(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_many1NoAntiquot(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_many1Fn), 3, 1);
lean_closure_set(x_4, 0, x_3);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_29 = l_Lean_Parser_ParserState_stackSize(x_7);
lean_inc(x_1);
lean_inc(x_7);
lean_inc(x_6);
x_30 = lean_apply_2(x_1, x_6, x_7);
x_31 = lean_ctor_get(x_30, 4);
lean_inc(x_31);
x_32 = lean_box(0);
x_33 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at___Lean_Parser_ParserState_mkNode_spec__0(x_31, x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_34 = lean_ctor_get(x_7, 2);
lean_inc(x_34);
lean_dec(x_7);
x_35 = lean_ctor_get(x_30, 2);
lean_inc(x_35);
x_36 = lean_nat_dec_lt(x_34, x_35);
lean_dec(x_35);
if (x_36 == 0)
{
if (x_5 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_34);
lean_dec(x_29);
x_37 = lean_box(0);
x_38 = l_Lean_Parser_ParserState_pushSyntax(x_30, x_37);
x_39 = lean_mk_string_unchecked("null", 4, 4);
x_40 = l_Lean_Name_mkStr1(x_39);
x_41 = l_Lean_Parser_ParserState_mkNode(x_38, x_40, x_4);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = l_Lean_Parser_ParserState_restore(x_30, x_29, x_34);
lean_dec(x_29);
x_43 = lean_mk_string_unchecked("null", 4, 4);
x_44 = l_Lean_Name_mkStr1(x_43);
x_45 = l_Lean_Parser_ParserState_mkNode(x_42, x_44, x_4);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_34);
lean_dec(x_29);
x_46 = lean_mk_string_unchecked("null", 4, 4);
x_47 = l_Lean_Name_mkStr1(x_46);
x_48 = l_Lean_Parser_ParserState_mkNode(x_30, x_47, x_4);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
lean_dec(x_7);
x_49 = lean_unsigned_to_nat(1u);
x_50 = lean_nat_add(x_29, x_49);
x_51 = l_Lean_Parser_ParserState_stackSize(x_30);
x_52 = lean_nat_dec_lt(x_50, x_51);
lean_dec(x_51);
lean_dec(x_50);
if (x_52 == 0)
{
lean_dec(x_29);
x_8 = x_30;
goto block_28;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_mk_string_unchecked("null", 4, 4);
x_54 = l_Lean_Name_mkStr1(x_53);
x_55 = l_Lean_Parser_ParserState_mkNode(x_30, x_54, x_29);
lean_dec(x_29);
x_8 = x_55;
goto block_28;
}
}
block_28:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = l_Lean_Parser_ParserState_stackSize(x_8);
lean_inc(x_2);
lean_inc(x_8);
lean_inc(x_6);
x_10 = lean_apply_2(x_2, x_6, x_8);
x_11 = lean_ctor_get(x_10, 4);
lean_inc(x_11);
x_12 = lean_box(0);
x_13 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at___Lean_Parser_ParserState_mkNode_spec__0(x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_ctor_get(x_8, 2);
lean_inc(x_14);
lean_dec(x_8);
x_15 = l_Lean_Parser_ParserState_restore(x_10, x_9, x_14);
lean_dec(x_9);
x_16 = lean_mk_string_unchecked("null", 4, 4);
x_17 = l_Lean_Name_mkStr1(x_16);
x_18 = l_Lean_Parser_ParserState_mkNode(x_15, x_17, x_4);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
lean_dec(x_8);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_9, x_19);
x_21 = l_Lean_Parser_ParserState_stackSize(x_10);
x_22 = lean_nat_dec_lt(x_20, x_21);
lean_dec(x_21);
lean_dec(x_20);
if (x_22 == 0)
{
lean_dec(x_9);
{
uint8_t _tmp_4 = x_3;
lean_object* _tmp_6 = x_10;
x_5 = _tmp_4;
x_7 = _tmp_6;
}
goto _start;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_mk_string_unchecked("null", 4, 4);
x_25 = l_Lean_Name_mkStr1(x_24);
x_26 = l_Lean_Parser_ParserState_mkNode(x_10, x_25, x_9);
lean_dec(x_9);
{
uint8_t _tmp_4 = x_3;
lean_object* _tmp_6 = x_26;
x_5 = _tmp_4;
x_7 = _tmp_6;
}
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_unbox(x_3);
lean_dec(x_3);
x_9 = lean_unbox(x_5);
lean_dec(x_5);
x_10 = l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse(x_1, x_2, x_8, x_4, x_9, x_6, x_7);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_unbox(x_3);
lean_dec(x_3);
x_9 = lean_unbox(x_5);
lean_dec(x_5);
x_10 = l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux(x_1, x_2, x_8, x_4, x_9, x_6, x_7);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepByFn(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_6 = l_Lean_Parser_ParserState_stackSize(x_5);
x_7 = lean_box(1);
x_8 = lean_unbox(x_7);
x_9 = l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse(x_2, x_3, x_1, x_6, x_8, x_4, x_5);
lean_dec(x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepByFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l_Lean_Parser_sepByFn(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1Fn(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_6 = l_Lean_Parser_ParserState_stackSize(x_5);
x_7 = lean_box(0);
x_8 = lean_unbox(x_7);
x_9 = l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse(x_2, x_3, x_1, x_6, x_8, x_4, x_5);
lean_dec(x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1Fn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l_Lean_Parser_sepBy1Fn(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepByInfo(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_andthenInfo___lam__0), 3, 2);
lean_closure_set(x_5, 0, x_4);
lean_closure_set(x_5, 1, x_3);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_alloc_closure((void*)(l_Lean_Parser_andthenInfo___lam__1), 3, 2);
lean_closure_set(x_8, 0, x_7);
lean_closure_set(x_8, 1, x_6);
x_9 = lean_box(1);
x_10 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_8);
lean_ctor_set(x_10, 2, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1Info(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_andthenInfo___lam__0), 3, 2);
lean_closure_set(x_5, 0, x_4);
lean_closure_set(x_5, 1, x_3);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_alloc_closure((void*)(l_Lean_Parser_andthenInfo___lam__1), 3, 2);
lean_closure_set(x_8, 0, x_7);
lean_closure_set(x_8, 1, x_6);
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_8);
lean_ctor_set(x_10, 2, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepByNoAntiquot(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = l_Lean_Parser_sepByInfo(x_4, x_5);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_box(x_3);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_sepByFn___boxed), 5, 3);
lean_closure_set(x_10, 0, x_9);
lean_closure_set(x_10, 1, x_7);
lean_closure_set(x_10, 2, x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepByNoAntiquot___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
lean_dec(x_3);
x_5 = l_Lean_Parser_sepByNoAntiquot(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1NoAntiquot(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = l_Lean_Parser_sepBy1Info(x_4, x_5);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_box(x_3);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_sepBy1Fn___boxed), 5, 3);
lean_closure_set(x_10, 0, x_9);
lean_closure_set(x_10, 1, x_7);
lean_closure_set(x_10, 2, x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1NoAntiquot___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
lean_dec(x_3);
x_5 = l_Lean_Parser_sepBy1NoAntiquot(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withResultOfFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_apply_2(x_1, x_3, x_4);
x_6 = lean_ctor_get(x_5, 4);
lean_inc(x_6);
x_7 = lean_box(0);
x_8 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at___Lean_Parser_ParserState_mkNode_spec__0(x_6, x_7);
if (x_8 == 0)
{
lean_dec(x_2);
return x_5;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
x_10 = l_Lean_Parser_SyntaxStack_back(x_9);
lean_dec(x_9);
x_11 = l_Lean_Parser_ParserState_popSyntax(x_5);
x_12 = lean_apply_1(x_2, x_10);
x_13 = l_Lean_Parser_ParserState_pushSyntax(x_11, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withResultOfInfo(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_box(1);
lean_inc(x_3);
lean_inc(x_2);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withResultOfInfo___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_withResultOfInfo(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withResultOf(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = l_Lean_Parser_withResultOfInfo(x_3);
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_withResultOfFn), 4, 2);
lean_closure_set(x_6, 0, x_5);
lean_closure_set(x_6, 1, x_2);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_many1Unbox___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l_Lean_Syntax_getNumArgs(x_1);
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_dec_eq(x_2, x_3);
lean_dec(x_2);
if (x_4 == 0)
{
lean_inc(x_1);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_many1Unbox(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_many1Unbox___lam__0___boxed), 1, 0);
x_3 = l_Lean_Parser_many1NoAntiquot(x_1);
x_4 = l_Lean_Parser_withResultOf(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_many1Unbox___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_many1Unbox___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_satisfyFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_4, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_6, 0);
x_8 = lean_string_utf8_at_end(x_7, x_5);
if (x_8 == 0)
{
uint32_t x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_string_utf8_get_fast(x_7, x_5);
x_10 = lean_box_uint32(x_9);
x_11 = lean_apply_1(x_1, x_10);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
lean_dec(x_5);
x_13 = lean_box(1);
x_14 = lean_box(0);
x_15 = lean_unbox(x_13);
x_16 = l_Lean_Parser_ParserState_mkUnexpectedError(x_4, x_2, x_14, x_15);
return x_16;
}
else
{
lean_object* x_17; 
lean_dec(x_2);
x_17 = l_Lean_Parser_ParserState_next_x27(x_4, x_7, x_5, lean_box(0));
lean_dec(x_5);
lean_dec(x_4);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_18 = lean_box(0);
x_19 = l_Lean_Parser_ParserState_mkEOIError(x_4, x_18);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_satisfyFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_satisfyFn(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_takeUntilFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_3, 2);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_5, 0);
x_7 = lean_string_utf8_at_end(x_6, x_4);
if (x_7 == 0)
{
uint32_t x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_string_utf8_get_fast(x_6, x_4);
x_9 = lean_box_uint32(x_8);
lean_inc(x_1);
x_10 = lean_apply_1(x_1, x_9);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = l_Lean_Parser_ParserState_next_x27(x_3, x_6, x_4, lean_box(0));
lean_dec(x_4);
lean_dec(x_3);
x_3 = x_12;
goto _start;
}
else
{
lean_dec(x_4);
lean_dec(x_1);
return x_3;
}
}
else
{
lean_dec(x_4);
lean_dec(x_1);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_takeUntilFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_takeUntilFn(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_takeWhileFn___lam__0(lean_object* x_1, uint32_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_box_uint32(x_2);
x_4 = lean_apply_1(x_1, x_3);
x_5 = lean_unbox(x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_box(1);
x_7 = lean_unbox(x_6);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_box(0);
x_9 = lean_unbox(x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_takeWhileFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_takeWhileFn___lam__0___boxed), 2, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = l_Lean_Parser_takeUntilFn(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_takeWhileFn___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_4 = l_Lean_Parser_takeWhileFn___lam__0(x_1, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_takeWhileFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_takeWhileFn(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_takeWhile1Fn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_inc(x_1);
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_satisfyFn___boxed), 4, 2);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_takeWhileFn___boxed), 3, 1);
lean_closure_set(x_6, 0, x_1);
x_7 = l_Lean_Parser_andthenFn(x_5, x_6, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_finishCommentBlock_eoi(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_mk_string_unchecked("unterminated comment", 20, 20);
x_4 = lean_box(0);
x_5 = l_Lean_Parser_ParserState_mkUnexpectedError(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_finishCommentBlock_eoi___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_Parser_finishCommentBlock_eoi(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_finishCommentBlock(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_5, 0);
x_7 = lean_ctor_get(x_4, 2);
lean_inc(x_7);
x_8 = lean_string_utf8_at_end(x_6, x_7);
if (x_8 == 0)
{
uint32_t x_9; lean_object* x_10; lean_object* x_11; uint32_t x_12; uint8_t x_13; 
x_9 = lean_string_utf8_get_fast(x_6, x_7);
x_10 = lean_string_utf8_next_fast(x_6, x_7);
lean_dec(x_7);
x_11 = lean_unsigned_to_nat(45u);
x_12 = l_Char_ofNat(x_11);
x_13 = l_instDecidableEqChar(x_9, x_12);
if (x_13 == 0)
{
lean_object* x_14; uint32_t x_15; uint8_t x_16; 
x_14 = lean_unsigned_to_nat(47u);
x_15 = l_Char_ofNat(x_14);
x_16 = l_instDecidableEqChar(x_9, x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = l_Lean_Parser_ParserState_setPos(x_4, x_10);
lean_dec(x_4);
x_4 = x_17;
goto _start;
}
else
{
uint8_t x_19; 
x_19 = lean_string_utf8_at_end(x_6, x_10);
if (x_19 == 0)
{
uint32_t x_20; uint8_t x_21; 
x_20 = lean_string_utf8_get_fast(x_6, x_10);
x_21 = l_instDecidableEqChar(x_20, x_12);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = l_Lean_Parser_ParserState_setPos(x_4, x_10);
lean_dec(x_4);
x_4 = x_22;
goto _start;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_2, x_24);
lean_dec(x_2);
x_26 = l_Lean_Parser_ParserState_next_x27(x_4, x_6, x_10, lean_box(0));
lean_dec(x_10);
lean_dec(x_4);
x_2 = x_25;
x_4 = x_26;
goto _start;
}
}
else
{
lean_object* x_28; 
lean_dec(x_10);
lean_dec(x_2);
x_28 = l_Lean_Parser_finishCommentBlock_eoi(x_1, x_4);
return x_28;
}
}
}
else
{
uint8_t x_29; 
x_29 = lean_string_utf8_at_end(x_6, x_10);
if (x_29 == 0)
{
uint32_t x_30; lean_object* x_31; uint32_t x_32; uint8_t x_33; 
x_30 = lean_string_utf8_get_fast(x_6, x_10);
x_31 = lean_unsigned_to_nat(47u);
x_32 = l_Char_ofNat(x_31);
x_33 = l_instDecidableEqChar(x_30, x_32);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = l_Lean_Parser_ParserState_setPos(x_4, x_10);
lean_dec(x_4);
x_4 = x_34;
goto _start;
}
else
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_nat_dec_eq(x_2, x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_nat_sub(x_2, x_36);
lean_dec(x_2);
x_39 = l_Lean_Parser_ParserState_next_x27(x_4, x_6, x_10, lean_box(0));
lean_dec(x_10);
lean_dec(x_4);
x_2 = x_38;
x_4 = x_39;
goto _start;
}
else
{
lean_object* x_41; 
lean_dec(x_2);
x_41 = l_Lean_Parser_ParserState_next_x27(x_4, x_6, x_10, lean_box(0));
lean_dec(x_10);
lean_dec(x_4);
return x_41;
}
}
}
else
{
lean_object* x_42; 
lean_dec(x_10);
lean_dec(x_2);
x_42 = l_Lean_Parser_finishCommentBlock_eoi(x_1, x_4);
return x_42;
}
}
}
else
{
lean_object* x_43; 
lean_dec(x_7);
lean_dec(x_2);
x_43 = l_Lean_Parser_finishCommentBlock_eoi(x_1, x_4);
return x_43;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_finishCommentBlock___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l_Lean_Parser_finishCommentBlock(x_5, x_2, x_3, x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_whitespace___lam__0(uint32_t x_1) {
_start:
{
lean_object* x_2; uint32_t x_3; uint8_t x_4; 
x_2 = lean_unsigned_to_nat(10u);
x_3 = l_Char_ofNat(x_2);
x_4 = l_instDecidableEqChar(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_whitespace(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_9; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
x_9 = lean_string_utf8_at_end(x_4, x_5);
if (x_9 == 0)
{
lean_object* x_10; uint32_t x_11; uint8_t x_12; uint8_t x_42; lean_object* x_50; uint32_t x_51; uint8_t x_52; 
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_whitespace___lam__0___boxed), 1, 0);
x_11 = lean_string_utf8_get_fast(x_4, x_5);
x_50 = lean_unsigned_to_nat(9u);
x_51 = l_Char_ofNat(x_50);
x_52 = l_instDecidableEqChar(x_11, x_51);
if (x_52 == 0)
{
lean_object* x_53; uint32_t x_54; uint8_t x_55; 
x_53 = lean_unsigned_to_nat(13u);
x_54 = l_Char_ofNat(x_53);
x_55 = l_instDecidableEqChar(x_11, x_54);
if (x_55 == 0)
{
lean_object* x_56; uint32_t x_57; uint8_t x_58; 
x_56 = lean_unsigned_to_nat(32u);
x_57 = l_Char_ofNat(x_56);
x_58 = l_instDecidableEqChar(x_11, x_57);
if (x_58 == 0)
{
x_42 = x_52;
goto block_49;
}
else
{
x_42 = x_58;
goto block_49;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_59 = lean_mk_string_unchecked("isolated carriage returns are not allowed", 41, 41);
x_60 = lean_box(0);
x_61 = l_Lean_Parser_ParserState_mkUnexpectedError(x_2, x_59, x_60, x_52);
return x_61;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_62 = lean_mk_string_unchecked("tabs are not allowed; please configure your editor to expand them", 65, 65);
x_63 = lean_box(0);
x_64 = l_Lean_Parser_ParserState_mkUnexpectedError(x_2, x_62, x_63, x_9);
return x_64;
}
block_41:
{
if (x_12 == 0)
{
lean_object* x_13; uint32_t x_14; uint8_t x_15; 
x_13 = lean_unsigned_to_nat(45u);
x_14 = l_Char_ofNat(x_13);
x_15 = l_instDecidableEqChar(x_11, x_14);
if (x_15 == 0)
{
lean_object* x_16; uint32_t x_17; uint8_t x_18; 
lean_dec(x_10);
x_16 = lean_unsigned_to_nat(47u);
x_17 = l_Char_ofNat(x_16);
x_18 = l_instDecidableEqChar(x_11, x_17);
if (x_18 == 0)
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_19; uint32_t x_20; uint8_t x_21; 
x_19 = lean_string_utf8_next_fast(x_4, x_5);
lean_dec(x_5);
x_20 = lean_string_utf8_get(x_4, x_19);
x_21 = l_instDecidableEqChar(x_20, x_14);
if (x_21 == 0)
{
lean_dec(x_19);
lean_dec(x_4);
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_22; uint32_t x_23; uint8_t x_24; 
x_22 = lean_string_utf8_next(x_4, x_19);
lean_dec(x_19);
x_23 = lean_string_utf8_get(x_4, x_22);
x_24 = l_instDecidableEqChar(x_23, x_14);
if (x_24 == 0)
{
lean_object* x_25; uint32_t x_26; uint8_t x_27; 
x_25 = lean_unsigned_to_nat(33u);
x_26 = l_Char_ofNat(x_25);
x_27 = l_instDecidableEqChar(x_23, x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_box(x_27);
x_30 = lean_alloc_closure((void*)(l_Lean_Parser_finishCommentBlock___boxed), 4, 2);
lean_closure_set(x_30, 0, x_29);
lean_closure_set(x_30, 1, x_28);
x_31 = lean_alloc_closure((void*)(l_Lean_Parser_whitespace), 2, 0);
x_32 = l_Lean_Parser_ParserState_next(x_2, x_4, x_22);
lean_dec(x_22);
lean_dec(x_4);
lean_dec(x_2);
x_33 = l_Lean_Parser_andthenFn(x_30, x_31, x_1, x_32);
return x_33;
}
else
{
lean_dec(x_22);
lean_dec(x_4);
lean_dec(x_1);
return x_2;
}
}
else
{
lean_dec(x_22);
lean_dec(x_4);
lean_dec(x_1);
return x_2;
}
}
}
}
else
{
lean_object* x_34; uint32_t x_35; uint8_t x_36; 
x_34 = lean_string_utf8_next_fast(x_4, x_5);
lean_dec(x_5);
x_35 = lean_string_utf8_get(x_4, x_34);
x_36 = l_instDecidableEqChar(x_35, x_14);
if (x_36 == 0)
{
lean_dec(x_34);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_alloc_closure((void*)(l_Lean_Parser_takeUntilFn___boxed), 3, 1);
lean_closure_set(x_37, 0, x_10);
x_38 = lean_alloc_closure((void*)(l_Lean_Parser_whitespace), 2, 0);
x_39 = l_Lean_Parser_ParserState_next(x_2, x_4, x_34);
lean_dec(x_34);
lean_dec(x_4);
lean_dec(x_2);
x_40 = l_Lean_Parser_andthenFn(x_37, x_38, x_1, x_39);
return x_40;
}
}
}
else
{
lean_dec(x_10);
goto block_8;
}
}
block_49:
{
if (x_42 == 0)
{
lean_object* x_43; uint32_t x_44; uint8_t x_45; 
x_43 = lean_unsigned_to_nat(13u);
x_44 = l_Char_ofNat(x_43);
x_45 = l_instDecidableEqChar(x_11, x_44);
if (x_45 == 0)
{
lean_object* x_46; uint32_t x_47; uint8_t x_48; 
x_46 = lean_unsigned_to_nat(10u);
x_47 = l_Char_ofNat(x_46);
x_48 = l_instDecidableEqChar(x_11, x_47);
x_12 = x_48;
goto block_41;
}
else
{
x_12 = x_45;
goto block_41;
}
}
else
{
lean_dec(x_10);
goto block_8;
}
}
}
else
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_2;
}
block_8:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_ParserState_next_x27(x_2, x_4, x_5, lean_box(0));
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_2 = x_6;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_whitespace___lam__0___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Lean_Parser_whitespace___lam__0(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkEmptySubstringAt(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc(x_2);
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_rawAux(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_4, 2);
lean_inc(x_7);
lean_inc_n(x_1, 2);
lean_inc(x_6);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_1);
lean_ctor_set(x_8, 2, x_1);
x_9 = lean_string_utf8_extract(x_6, x_1, x_7);
if (x_2 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_3);
lean_inc(x_7);
x_10 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_7);
lean_ctor_set(x_10, 2, x_7);
x_11 = lean_string_utf8_byte_size(x_9);
x_12 = lean_nat_add(x_1, x_11);
lean_dec(x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_1);
lean_ctor_set(x_13, 2, x_10);
lean_ctor_set(x_13, 3, x_12);
x_14 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_9);
x_15 = l_Lean_Parser_ParserState_pushSyntax(x_4, x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_16 = l_Lean_Parser_whitespace(x_3, x_4);
x_17 = lean_ctor_get(x_16, 2);
lean_inc(x_17);
x_18 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_18, 0, x_6);
lean_ctor_set(x_18, 1, x_7);
lean_ctor_set(x_18, 2, x_17);
x_19 = lean_string_utf8_byte_size(x_9);
x_20 = lean_nat_add(x_1, x_19);
lean_dec(x_19);
x_21 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_21, 0, x_8);
lean_ctor_set(x_21, 1, x_1);
lean_ctor_set(x_21, 2, x_18);
lean_ctor_set(x_21, 3, x_20);
x_22 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_9);
x_23 = l_Lean_Parser_ParserState_pushSyntax(x_16, x_22);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_rawAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l___private_Lean_Parser_Basic_0__Lean_Parser_rawAux(x_1, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_rawFn(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
lean_inc(x_4);
lean_inc(x_3);
x_5 = lean_apply_2(x_1, x_3, x_4);
x_6 = lean_ctor_get(x_5, 4);
lean_inc(x_6);
x_7 = lean_box(0);
x_8 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at___Lean_Parser_ParserState_mkNode_spec__0(x_6, x_7);
if (x_8 == 0)
{
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_4, 2);
lean_inc(x_9);
lean_dec(x_4);
x_10 = l___private_Lean_Parser_Basic_0__Lean_Parser_rawAux(x_9, x_2, x_3, x_5);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_rawFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_Parser_rawFn(x_1, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_chFn___lam__0(uint32_t x_1, uint32_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_instDecidableEqChar(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_chFn(uint32_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_5 = lean_box_uint32(x_1);
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_chFn___lam__0___boxed), 2, 1);
lean_closure_set(x_6, 0, x_5);
x_7 = lean_mk_string_unchecked("'", 1, 1);
x_8 = lean_mk_string_unchecked("", 0, 0);
x_9 = lean_string_push(x_8, x_1);
lean_inc(x_7);
x_10 = lean_string_append(x_7, x_9);
lean_dec(x_9);
x_11 = lean_string_append(x_10, x_7);
lean_dec(x_7);
x_12 = lean_alloc_closure((void*)(l_Lean_Parser_satisfyFn___boxed), 4, 2);
lean_closure_set(x_12, 0, x_6);
lean_closure_set(x_12, 1, x_11);
x_13 = l_Lean_Parser_rawFn(x_12, x_2, x_3, x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_chFn___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint32_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = l_Lean_Parser_chFn___lam__0(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_chFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint32_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_Lean_Parser_chFn(x_5, x_6, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_rawCh(uint32_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_epsilonInfo___lam__0___boxed), 1, 0);
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_epsilonInfo___lam__1___boxed), 1, 0);
x_5 = lean_box(1);
x_6 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_5);
x_7 = lean_box_uint32(x_1);
x_8 = lean_box(x_2);
x_9 = lean_alloc_closure((void*)(l_Lean_Parser_chFn___boxed), 4, 2);
lean_closure_set(x_9, 0, x_7);
lean_closure_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_rawCh___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lean_Parser_rawCh(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_hexDigitFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
x_6 = lean_string_utf8_at_end(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; uint32_t x_8; lean_object* x_9; uint8_t x_10; uint8_t x_17; uint8_t x_26; lean_object* x_35; uint32_t x_36; uint8_t x_37; 
x_7 = lean_box(1);
x_8 = lean_string_utf8_get_fast(x_4, x_5);
x_9 = lean_string_utf8_next_fast(x_4, x_5);
lean_dec(x_5);
x_35 = lean_unsigned_to_nat(48u);
x_36 = lean_uint32_of_nat(x_35);
x_37 = lean_uint32_dec_le(x_36, x_8);
if (x_37 == 0)
{
x_26 = x_37;
goto block_34;
}
else
{
lean_object* x_38; uint32_t x_39; uint8_t x_40; 
x_38 = lean_unsigned_to_nat(57u);
x_39 = lean_uint32_of_nat(x_38);
x_40 = lean_uint32_dec_le(x_8, x_39);
x_26 = x_40;
goto block_34;
}
block_16:
{
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
lean_dec(x_9);
x_11 = lean_mk_string_unchecked("invalid hexadecimal numeral", 27, 27);
x_12 = lean_box(0);
x_13 = lean_unbox(x_7);
x_14 = l_Lean_Parser_ParserState_mkUnexpectedError(x_2, x_11, x_12, x_13);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = l_Lean_Parser_ParserState_setPos(x_2, x_9);
lean_dec(x_2);
return x_15;
}
}
block_25:
{
if (x_17 == 0)
{
lean_object* x_18; uint32_t x_19; uint8_t x_20; 
x_18 = lean_unsigned_to_nat(65u);
x_19 = l_Char_ofNat(x_18);
x_20 = lean_uint32_dec_le(x_19, x_8);
if (x_20 == 0)
{
x_10 = x_20;
goto block_16;
}
else
{
lean_object* x_21; uint32_t x_22; uint8_t x_23; 
x_21 = lean_unsigned_to_nat(70u);
x_22 = l_Char_ofNat(x_21);
x_23 = lean_uint32_dec_le(x_8, x_22);
x_10 = x_23;
goto block_16;
}
}
else
{
lean_object* x_24; 
x_24 = l_Lean_Parser_ParserState_setPos(x_2, x_9);
lean_dec(x_2);
return x_24;
}
}
block_34:
{
if (x_26 == 0)
{
lean_object* x_27; uint32_t x_28; uint8_t x_29; 
x_27 = lean_unsigned_to_nat(97u);
x_28 = l_Char_ofNat(x_27);
x_29 = lean_uint32_dec_le(x_28, x_8);
if (x_29 == 0)
{
x_17 = x_29;
goto block_25;
}
else
{
lean_object* x_30; uint32_t x_31; uint8_t x_32; 
x_30 = lean_unsigned_to_nat(102u);
x_31 = l_Char_ofNat(x_30);
x_32 = lean_uint32_dec_le(x_8, x_31);
x_17 = x_32;
goto block_25;
}
}
else
{
lean_object* x_33; 
x_33 = l_Lean_Parser_ParserState_setPos(x_2, x_9);
lean_dec(x_2);
return x_33;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_5);
x_41 = lean_box(0);
x_42 = l_Lean_Parser_ParserState_mkEOIError(x_2, x_41);
return x_42;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_hexDigitFn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_hexDigitFn(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_stringGapFn(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_10; 
x_4 = lean_ctor_get(x_3, 2);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_5, 0);
x_10 = lean_string_utf8_at_end(x_6, x_4);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; uint32_t x_18; uint8_t x_19; lean_object* x_27; uint32_t x_28; uint8_t x_29; 
x_11 = lean_box(1);
x_18 = lean_string_utf8_get_fast(x_6, x_4);
x_27 = lean_unsigned_to_nat(10u);
x_28 = l_Char_ofNat(x_27);
x_29 = l_instDecidableEqChar(x_18, x_28);
if (x_29 == 0)
{
lean_object* x_30; uint32_t x_31; uint8_t x_32; 
x_30 = lean_unsigned_to_nat(32u);
x_31 = l_Char_ofNat(x_30);
x_32 = l_instDecidableEqChar(x_18, x_31);
if (x_32 == 0)
{
lean_object* x_33; uint32_t x_34; uint8_t x_35; 
x_33 = lean_unsigned_to_nat(9u);
x_34 = l_Char_ofNat(x_33);
x_35 = l_instDecidableEqChar(x_18, x_34);
x_19 = x_35;
goto block_26;
}
else
{
x_19 = x_32;
goto block_26;
}
}
else
{
if (x_1 == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = l_Lean_Parser_ParserState_next_x27(x_3, x_6, x_4, lean_box(0));
lean_dec(x_4);
lean_dec(x_3);
x_37 = lean_unbox(x_11);
x_1 = x_37;
x_3 = x_36;
goto _start;
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; 
lean_dec(x_4);
x_39 = lean_mk_string_unchecked("unexpected additional newline in string gap", 43, 43);
x_40 = lean_box(0);
x_41 = lean_unbox(x_11);
x_42 = l_Lean_Parser_ParserState_mkUnexpectedError(x_3, x_39, x_40, x_41);
return x_42;
}
}
block_17:
{
if (x_12 == 0)
{
lean_dec(x_4);
if (x_1 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_13 = lean_mk_string_unchecked("expecting newline in string gap", 31, 31);
x_14 = lean_box(0);
x_15 = lean_unbox(x_11);
x_16 = l_Lean_Parser_ParserState_mkUnexpectedError(x_3, x_13, x_14, x_15);
return x_16;
}
else
{
return x_3;
}
}
else
{
goto block_9;
}
}
block_26:
{
if (x_19 == 0)
{
lean_object* x_20; uint32_t x_21; uint8_t x_22; 
x_20 = lean_unsigned_to_nat(13u);
x_21 = l_Char_ofNat(x_20);
x_22 = l_instDecidableEqChar(x_18, x_21);
if (x_22 == 0)
{
lean_object* x_23; uint32_t x_24; uint8_t x_25; 
x_23 = lean_unsigned_to_nat(10u);
x_24 = l_Char_ofNat(x_23);
x_25 = l_instDecidableEqChar(x_18, x_24);
x_12 = x_25;
goto block_17;
}
else
{
x_12 = x_22;
goto block_17;
}
}
else
{
goto block_9;
}
}
}
else
{
lean_dec(x_4);
return x_3;
}
block_9:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_ParserState_next_x27(x_3, x_6, x_4, lean_box(0));
lean_dec(x_4);
lean_dec(x_3);
x_3 = x_7;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_stringGapFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_Parser_stringGapFn(x_4, x_2, x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_quotedCharCoreFn(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_4, 2);
lean_inc(x_7);
x_8 = lean_string_utf8_at_end(x_6, x_7);
if (x_8 == 0)
{
uint32_t x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_string_utf8_get_fast(x_6, x_7);
x_10 = lean_box_uint32(x_9);
x_11 = lean_apply_1(x_1, x_10);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; uint32_t x_14; uint8_t x_15; 
x_13 = lean_unsigned_to_nat(120u);
x_14 = l_Char_ofNat(x_13);
x_15 = l_instDecidableEqChar(x_9, x_14);
if (x_15 == 0)
{
lean_object* x_16; uint32_t x_17; uint8_t x_18; 
x_16 = lean_unsigned_to_nat(117u);
x_17 = l_Char_ofNat(x_16);
x_18 = l_instDecidableEqChar(x_9, x_17);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_7);
lean_dec(x_6);
x_19 = lean_box(1);
if (x_2 == 0)
{
lean_dec(x_3);
goto block_24;
}
else
{
lean_object* x_25; uint32_t x_26; uint8_t x_27; 
x_25 = lean_unsigned_to_nat(10u);
x_26 = l_Char_ofNat(x_25);
x_27 = l_instDecidableEqChar(x_9, x_26);
if (x_27 == 0)
{
lean_dec(x_3);
goto block_24;
}
else
{
lean_object* x_28; 
x_28 = l_Lean_Parser_stringGapFn(x_18, x_3, x_4);
lean_dec(x_3);
return x_28;
}
}
block_24:
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_20 = lean_mk_string_unchecked("invalid escape sequence", 23, 23);
x_21 = lean_box(0);
x_22 = lean_unbox(x_19);
x_23 = l_Lean_Parser_ParserState_mkUnexpectedError(x_4, x_20, x_21, x_22);
return x_23;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_alloc_closure((void*)(l_Lean_Parser_hexDigitFn___boxed), 2, 0);
lean_inc_n(x_29, 2);
x_30 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_30, 0, x_29);
lean_closure_set(x_30, 1, x_29);
lean_inc(x_29);
x_31 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_31, 0, x_29);
lean_closure_set(x_31, 1, x_30);
x_32 = l_Lean_Parser_ParserState_next_x27(x_4, x_6, x_7, lean_box(0));
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_33 = l_Lean_Parser_andthenFn(x_29, x_31, x_3, x_32);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_alloc_closure((void*)(l_Lean_Parser_hexDigitFn___boxed), 2, 0);
x_35 = l_Lean_Parser_ParserState_next_x27(x_4, x_6, x_7, lean_box(0));
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_inc(x_34);
x_36 = l_Lean_Parser_andthenFn(x_34, x_34, x_3, x_35);
return x_36;
}
}
else
{
lean_object* x_37; 
lean_dec(x_3);
x_37 = l_Lean_Parser_ParserState_next_x27(x_4, x_6, x_7, lean_box(0));
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_38 = lean_box(0);
x_39 = l_Lean_Parser_ParserState_mkEOIError(x_4, x_38);
return x_39;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_quotedCharCoreFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_Parser_quotedCharCoreFn(x_1, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_isQuotableCharDefault(uint32_t x_1) {
_start:
{
uint8_t x_2; lean_object* x_16; uint32_t x_17; uint8_t x_18; 
x_16 = lean_unsigned_to_nat(92u);
x_17 = l_Char_ofNat(x_16);
x_18 = l_instDecidableEqChar(x_1, x_17);
if (x_18 == 0)
{
lean_object* x_19; uint32_t x_20; uint8_t x_21; 
x_19 = lean_unsigned_to_nat(34u);
x_20 = l_Char_ofNat(x_19);
x_21 = l_instDecidableEqChar(x_1, x_20);
x_2 = x_21;
goto block_15;
}
else
{
x_2 = x_18;
goto block_15;
}
block_15:
{
if (x_2 == 0)
{
lean_object* x_3; uint32_t x_4; uint8_t x_5; 
x_3 = lean_unsigned_to_nat(39u);
x_4 = l_Char_ofNat(x_3);
x_5 = l_instDecidableEqChar(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint32_t x_7; uint8_t x_8; 
x_6 = lean_unsigned_to_nat(114u);
x_7 = l_Char_ofNat(x_6);
x_8 = l_instDecidableEqChar(x_1, x_7);
if (x_8 == 0)
{
lean_object* x_9; uint32_t x_10; uint8_t x_11; 
x_9 = lean_unsigned_to_nat(110u);
x_10 = l_Char_ofNat(x_9);
x_11 = l_instDecidableEqChar(x_1, x_10);
if (x_11 == 0)
{
lean_object* x_12; uint32_t x_13; uint8_t x_14; 
x_12 = lean_unsigned_to_nat(116u);
x_13 = l_Char_ofNat(x_12);
x_14 = l_instDecidableEqChar(x_1, x_13);
return x_14;
}
else
{
return x_11;
}
}
else
{
return x_8;
}
}
else
{
return x_5;
}
}
else
{
return x_2;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_isQuotableCharDefault___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Lean_Parser_isQuotableCharDefault(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_quotedCharFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_isQuotableCharDefault___boxed), 1, 0);
x_4 = lean_box(0);
x_5 = lean_unbox(x_4);
x_6 = l_Lean_Parser_quotedCharCoreFn(x_3, x_5, x_1, x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_quotedStringFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_isQuotableCharDefault___boxed), 1, 0);
x_4 = lean_box(1);
x_5 = lean_unbox(x_4);
x_6 = l_Lean_Parser_quotedCharCoreFn(x_3, x_5, x_1, x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkNodeToken(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_4, 4);
lean_inc(x_5);
x_6 = lean_box(0);
x_7 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at___Lean_Parser_ParserState_mkNode_spec__0(x_5, x_6);
if (x_7 == 0)
{
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_ctor_get(x_4, 2);
lean_inc(x_10);
lean_inc_n(x_2, 2);
lean_inc(x_9);
x_11 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_2);
lean_ctor_set(x_11, 2, x_2);
x_12 = lean_string_utf8_extract(x_9, x_2, x_10);
x_13 = l_Lean_Parser_whitespace(x_3, x_4);
x_14 = lean_ctor_get(x_13, 2);
lean_inc(x_14);
lean_inc(x_10);
x_15 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_15, 0, x_9);
lean_ctor_set(x_15, 1, x_10);
lean_ctor_set(x_15, 2, x_14);
x_16 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_2);
lean_ctor_set(x_16, 2, x_15);
lean_ctor_set(x_16, 3, x_10);
x_17 = l_Lean_Syntax_mkLit(x_1, x_12, x_16);
x_18 = l_Lean_Parser_ParserState_pushSyntax(x_13, x_17);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_charLitFnAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_3, 2);
lean_inc(x_6);
x_7 = lean_string_utf8_at_end(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint32_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint32_t x_32; uint8_t x_33; 
x_8 = lean_box(1);
x_28 = lean_string_utf8_get_fast(x_5, x_6);
x_29 = lean_string_utf8_next_fast(x_5, x_6);
lean_dec(x_6);
x_30 = l_Lean_Parser_ParserState_setPos(x_3, x_29);
lean_dec(x_3);
x_31 = lean_unsigned_to_nat(92u);
x_32 = l_Char_ofNat(x_31);
x_33 = l_instDecidableEqChar(x_28, x_32);
if (x_33 == 0)
{
x_9 = x_30;
goto block_27;
}
else
{
lean_object* x_34; 
lean_inc(x_2);
x_34 = l_Lean_Parser_quotedCharFn(x_2, x_30);
x_9 = x_34;
goto block_27;
}
block_27:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_9, 4);
lean_inc(x_10);
x_11 = lean_box(0);
x_12 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at___Lean_Parser_ParserState_mkNode_spec__0(x_10, x_11);
if (x_12 == 0)
{
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
else
{
if (x_7 == 0)
{
lean_object* x_13; uint32_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint32_t x_18; uint8_t x_19; 
x_13 = lean_ctor_get(x_9, 2);
lean_inc(x_13);
x_14 = lean_string_utf8_get(x_5, x_13);
x_15 = lean_string_utf8_next(x_5, x_13);
lean_dec(x_13);
lean_dec(x_5);
x_16 = l_Lean_Parser_ParserState_setPos(x_9, x_15);
lean_dec(x_9);
x_17 = lean_unsigned_to_nat(39u);
x_18 = l_Char_ofNat(x_17);
x_19 = l_instDecidableEqChar(x_14, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
lean_dec(x_2);
lean_dec(x_1);
x_20 = lean_mk_string_unchecked("missing end of character literal", 32, 32);
x_21 = lean_box(0);
x_22 = lean_unbox(x_8);
x_23 = l_Lean_Parser_ParserState_mkUnexpectedError(x_16, x_20, x_21, x_22);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_mk_string_unchecked("char", 4, 4);
x_25 = l_Lean_Name_mkStr1(x_24);
x_26 = l_Lean_Parser_mkNodeToken(x_25, x_1, x_2, x_16);
return x_26;
}
}
else
{
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
}
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_35 = lean_box(0);
x_36 = l_Lean_Parser_ParserState_mkEOIError(x_3, x_35);
return x_36;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_strLitFnAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_3, 2);
lean_inc(x_6);
x_7 = lean_string_utf8_at_end(x_5, x_6);
if (x_7 == 0)
{
uint32_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint32_t x_12; uint8_t x_13; 
x_8 = lean_string_utf8_get_fast(x_5, x_6);
x_9 = lean_string_utf8_next_fast(x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
x_10 = l_Lean_Parser_ParserState_setPos(x_3, x_9);
lean_dec(x_3);
x_11 = lean_unsigned_to_nat(34u);
x_12 = l_Char_ofNat(x_11);
x_13 = l_instDecidableEqChar(x_8, x_12);
if (x_13 == 0)
{
lean_object* x_14; uint32_t x_15; uint8_t x_16; 
x_14 = lean_unsigned_to_nat(92u);
x_15 = l_Char_ofNat(x_14);
x_16 = l_instDecidableEqChar(x_8, x_15);
if (x_16 == 0)
{
x_3 = x_10;
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_alloc_closure((void*)(l_Lean_Parser_quotedStringFn), 2, 0);
x_19 = lean_alloc_closure((void*)(l_Lean_Parser_strLitFnAux), 3, 1);
lean_closure_set(x_19, 0, x_1);
x_20 = l_Lean_Parser_andthenFn(x_18, x_19, x_2, x_10);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_mk_string_unchecked("str", 3, 3);
x_22 = l_Lean_Name_mkStr1(x_21);
x_23 = l_Lean_Parser_mkNodeToken(x_22, x_1, x_2, x_10);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_24 = lean_mk_string_unchecked("unterminated string literal", 27, 27);
x_25 = l_Lean_Parser_ParserState_mkUnexpectedErrorAt(x_3, x_24, x_1);
lean_dec(x_3);
return x_25;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_isRawStrLitStart(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_string_utf8_at_end(x_1, x_2);
if (x_3 == 0)
{
uint32_t x_4; lean_object* x_5; uint32_t x_6; uint8_t x_7; 
x_4 = lean_string_utf8_get_fast(x_1, x_2);
x_5 = lean_unsigned_to_nat(35u);
x_6 = l_Char_ofNat(x_5);
x_7 = l_instDecidableEqChar(x_4, x_6);
if (x_7 == 0)
{
lean_object* x_8; uint32_t x_9; uint8_t x_10; 
lean_dec(x_2);
x_8 = lean_unsigned_to_nat(34u);
x_9 = l_Char_ofNat(x_8);
x_10 = l_instDecidableEqChar(x_4, x_9);
return x_10;
}
else
{
lean_object* x_11; 
x_11 = lean_string_utf8_next_fast(x_1, x_2);
lean_dec(x_2);
x_2 = x_11;
goto _start;
}
}
else
{
lean_object* x_13; uint8_t x_14; 
lean_dec(x_2);
x_13 = lean_box(0);
x_14 = lean_unbox(x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_isRawStrLitStart___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Parser_isRawStrLitStart(x_1, x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_rawStrLitFnAux_errorUnterminated(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_mk_string_unchecked("unterminated raw string literal", 31, 31);
x_4 = l_Lean_Parser_ParserState_mkUnexpectedErrorAt(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_rawStrLitFnAux_errorUnterminated___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_rawStrLitFnAux_errorUnterminated(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_rawStrLitFnAux_normalState(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_4, 2);
lean_inc(x_7);
x_8 = lean_string_utf8_at_end(x_6, x_7);
if (x_8 == 0)
{
uint32_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint32_t x_13; uint8_t x_14; 
x_9 = lean_string_utf8_get_fast(x_6, x_7);
x_10 = lean_string_utf8_next_fast(x_6, x_7);
lean_dec(x_7);
lean_dec(x_6);
x_11 = l_Lean_Parser_ParserState_setPos(x_4, x_10);
lean_dec(x_4);
x_12 = lean_unsigned_to_nat(34u);
x_13 = l_Char_ofNat(x_12);
x_14 = l_instDecidableEqChar(x_9, x_13);
if (x_14 == 0)
{
x_4 = x_11;
goto _start;
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_dec_eq(x_2, x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = l_Lean_Parser_rawStrLitFnAux_closingState(x_1, x_2, x_16, x_3, x_11);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_mk_string_unchecked("str", 3, 3);
x_20 = l_Lean_Name_mkStr1(x_19);
x_21 = l_Lean_Parser_mkNodeToken(x_20, x_1, x_3, x_11);
return x_21;
}
}
}
else
{
lean_object* x_22; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_22 = l_Lean_Parser_rawStrLitFnAux_errorUnterminated(x_1, x_4);
lean_dec(x_4);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_rawStrLitFnAux_closingState(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_ctor_get(x_5, 2);
lean_inc(x_8);
x_9 = lean_string_utf8_at_end(x_7, x_8);
if (x_9 == 0)
{
uint32_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint32_t x_14; uint8_t x_15; 
x_10 = lean_string_utf8_get_fast(x_7, x_8);
x_11 = lean_string_utf8_next_fast(x_7, x_8);
lean_dec(x_8);
lean_dec(x_7);
x_12 = l_Lean_Parser_ParserState_setPos(x_5, x_11);
lean_dec(x_5);
x_13 = lean_unsigned_to_nat(35u);
x_14 = l_Char_ofNat(x_13);
x_15 = l_instDecidableEqChar(x_10, x_14);
if (x_15 == 0)
{
lean_object* x_16; uint32_t x_17; uint8_t x_18; 
lean_dec(x_3);
x_16 = lean_unsigned_to_nat(34u);
x_17 = l_Char_ofNat(x_16);
x_18 = l_instDecidableEqChar(x_10, x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = l_Lean_Parser_rawStrLitFnAux_normalState(x_1, x_2, x_4, x_12);
return x_19;
}
else
{
lean_object* x_20; 
x_20 = lean_unsigned_to_nat(0u);
x_3 = x_20;
x_5 = x_12;
goto _start;
}
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_3, x_22);
lean_dec(x_3);
x_24 = lean_nat_dec_eq(x_23, x_2);
if (x_24 == 0)
{
x_3 = x_23;
x_5 = x_12;
goto _start;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_23);
x_26 = lean_mk_string_unchecked("str", 3, 3);
x_27 = l_Lean_Name_mkStr1(x_26);
x_28 = l_Lean_Parser_mkNodeToken(x_27, x_1, x_4, x_12);
return x_28;
}
}
}
else
{
lean_object* x_29; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_29 = l_Lean_Parser_rawStrLitFnAux_errorUnterminated(x_1, x_5);
lean_dec(x_5);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_rawStrLitFnAux_normalState___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_rawStrLitFnAux_normalState(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_rawStrLitFnAux_closingState___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_rawStrLitFnAux_closingState(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_rawStrLitFnAux_initState(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_4, 2);
lean_inc(x_7);
x_8 = lean_string_utf8_at_end(x_6, x_7);
if (x_8 == 0)
{
uint32_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint32_t x_13; uint8_t x_14; 
x_9 = lean_string_utf8_get_fast(x_6, x_7);
x_10 = lean_string_utf8_next_fast(x_6, x_7);
lean_dec(x_7);
lean_dec(x_6);
x_11 = l_Lean_Parser_ParserState_setPos(x_4, x_10);
lean_dec(x_4);
x_12 = lean_unsigned_to_nat(35u);
x_13 = l_Char_ofNat(x_12);
x_14 = l_instDecidableEqChar(x_9, x_13);
if (x_14 == 0)
{
lean_object* x_15; uint32_t x_16; uint8_t x_17; 
x_15 = lean_unsigned_to_nat(34u);
x_16 = l_Char_ofNat(x_15);
x_17 = l_instDecidableEqChar(x_9, x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_3);
lean_dec(x_2);
x_18 = l_Lean_Parser_rawStrLitFnAux_errorUnterminated(x_1, x_11);
lean_dec(x_11);
return x_18;
}
else
{
lean_object* x_19; 
x_19 = l_Lean_Parser_rawStrLitFnAux_normalState(x_1, x_2, x_3, x_11);
lean_dec(x_2);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_2, x_20);
lean_dec(x_2);
x_2 = x_21;
x_4 = x_11;
goto _start;
}
}
else
{
lean_object* x_23; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_23 = l_Lean_Parser_rawStrLitFnAux_errorUnterminated(x_1, x_4);
lean_dec(x_4);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_rawStrLitFnAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_Parser_rawStrLitFnAux_initState(x_1, x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_takeDigitsFn(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_6, 0);
x_8 = lean_ctor_get(x_5, 2);
lean_inc(x_8);
x_9 = lean_string_utf8_at_end(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint32_t x_11; lean_object* x_12; uint32_t x_13; uint8_t x_14; 
x_10 = lean_box(1);
x_11 = lean_string_utf8_get_fast(x_7, x_8);
x_12 = lean_unsigned_to_nat(95u);
x_13 = l_Char_ofNat(x_12);
x_14 = l_instDecidableEqChar(x_11, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_box_uint32(x_11);
lean_inc(x_1);
x_16 = lean_apply_1(x_1, x_15);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_dec(x_8);
lean_dec(x_1);
if (x_3 == 0)
{
lean_dec(x_2);
return x_5;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_18 = lean_mk_string_unchecked("unexpected character", 20, 20);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_2);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_unbox(x_10);
x_22 = l_Lean_Parser_ParserState_mkUnexpectedError(x_5, x_18, x_20, x_21);
return x_22;
}
}
else
{
lean_object* x_23; 
x_23 = l_Lean_Parser_ParserState_next_x27(x_5, x_7, x_8, lean_box(0));
lean_dec(x_8);
lean_dec(x_5);
x_3 = x_14;
x_5 = x_23;
goto _start;
}
}
else
{
lean_object* x_25; uint8_t x_26; 
x_25 = l_Lean_Parser_ParserState_next_x27(x_5, x_7, x_8, lean_box(0));
lean_dec(x_8);
lean_dec(x_5);
x_26 = lean_unbox(x_10);
x_3 = x_26;
x_5 = x_25;
goto _start;
}
}
else
{
lean_dec(x_8);
lean_dec(x_1);
if (x_3 == 0)
{
lean_dec(x_2);
return x_5;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_2);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_Parser_ParserState_mkEOIError(x_5, x_29);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_takeDigitsFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_Lean_Parser_takeDigitsFn(x_1, x_2, x_6, x_4, x_5);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_decimalNumberFn_parseOptExp___lam__0(uint32_t x_1) {
_start:
{
lean_object* x_2; uint32_t x_3; uint8_t x_4; 
x_2 = lean_unsigned_to_nat(48u);
x_3 = lean_uint32_of_nat(x_2);
x_4 = lean_uint32_dec_le(x_3, x_1);
if (x_4 == 0)
{
return x_4;
}
else
{
lean_object* x_5; uint32_t x_6; uint8_t x_7; 
x_5 = lean_unsigned_to_nat(57u);
x_6 = lean_uint32_of_nat(x_5);
x_7 = lean_uint32_dec_le(x_1, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_decimalNumberFn_parseOptExp(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_6; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_28; uint8_t x_29; uint8_t x_30; lean_object* x_33; uint8_t x_34; uint32_t x_44; lean_object* x_45; uint32_t x_46; uint8_t x_47; 
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_decimalNumberFn_parseOptExp___lam__0___boxed), 1, 0);
x_16 = lean_ctor_get(x_1, 0);
x_17 = lean_ctor_get(x_16, 0);
x_33 = lean_ctor_get(x_2, 2);
lean_inc(x_33);
x_44 = lean_string_utf8_get(x_17, x_33);
x_45 = lean_unsigned_to_nat(101u);
x_46 = l_Char_ofNat(x_45);
x_47 = l_instDecidableEqChar(x_44, x_46);
if (x_47 == 0)
{
lean_object* x_48; uint32_t x_49; uint8_t x_50; 
x_48 = lean_unsigned_to_nat(69u);
x_49 = l_Char_ofNat(x_48);
x_50 = l_instDecidableEqChar(x_44, x_49);
x_34 = x_50;
goto block_43;
}
else
{
x_34 = x_47;
goto block_43;
}
block_15:
{
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_3);
x_7 = lean_mk_string_unchecked("missing exponent digits in scientific literal", 45, 45);
x_8 = lean_box(0);
x_9 = l_Lean_Parser_ParserState_mkUnexpectedError(x_2, x_7, x_8, x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_10 = lean_mk_string_unchecked("decimal number", 14, 14);
x_11 = lean_box(0);
x_12 = l_Lean_Parser_ParserState_setPos(x_2, x_4);
lean_dec(x_2);
x_13 = lean_unbox(x_11);
x_14 = l_Lean_Parser_takeDigitsFn(x_3, x_10, x_13, x_1, x_12);
return x_14;
}
}
block_27:
{
lean_object* x_20; uint32_t x_21; uint32_t x_22; uint8_t x_23; 
x_20 = lean_unsigned_to_nat(48u);
x_21 = lean_uint32_of_nat(x_20);
x_22 = lean_string_utf8_get(x_17, x_19);
x_23 = lean_uint32_dec_le(x_21, x_22);
if (x_23 == 0)
{
x_4 = x_19;
x_5 = x_18;
x_6 = x_23;
goto block_15;
}
else
{
lean_object* x_24; uint32_t x_25; uint8_t x_26; 
x_24 = lean_unsigned_to_nat(57u);
x_25 = lean_uint32_of_nat(x_24);
x_26 = lean_uint32_dec_le(x_22, x_25);
x_4 = x_19;
x_5 = x_18;
x_6 = x_26;
goto block_15;
}
}
block_32:
{
if (x_30 == 0)
{
x_18 = x_29;
x_19 = x_28;
goto block_27;
}
else
{
lean_object* x_31; 
x_31 = lean_string_utf8_next(x_17, x_28);
lean_dec(x_28);
x_18 = x_29;
x_19 = x_31;
goto block_27;
}
}
block_43:
{
if (x_34 == 0)
{
lean_dec(x_33);
lean_dec(x_3);
return x_2;
}
else
{
lean_object* x_35; uint32_t x_36; lean_object* x_37; uint32_t x_38; uint8_t x_39; 
x_35 = lean_string_utf8_next(x_17, x_33);
lean_dec(x_33);
x_36 = lean_string_utf8_get(x_17, x_35);
x_37 = lean_unsigned_to_nat(45u);
x_38 = l_Char_ofNat(x_37);
x_39 = l_instDecidableEqChar(x_36, x_38);
if (x_39 == 0)
{
lean_object* x_40; uint32_t x_41; uint8_t x_42; 
x_40 = lean_unsigned_to_nat(43u);
x_41 = l_Char_ofNat(x_40);
x_42 = l_instDecidableEqChar(x_36, x_41);
x_28 = x_35;
x_29 = x_34;
x_30 = x_42;
goto block_32;
}
else
{
x_28 = x_35;
x_29 = x_34;
x_30 = x_39;
goto block_32;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_decimalNumberFn_parseOptExp___lam__0___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Lean_Parser_decimalNumberFn_parseOptExp___lam__0(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_decimalNumberFn_parseOptExp___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_decimalNumberFn_parseOptExp(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_decimalNumberFn_parseOptDot(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint32_t x_6; lean_object* x_7; uint32_t x_8; uint8_t x_9; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_string_utf8_get(x_4, x_5);
x_7 = lean_unsigned_to_nat(46u);
x_8 = l_Char_ofNat(x_7);
x_9 = l_instDecidableEqChar(x_6, x_8);
if (x_9 == 0)
{
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_20; uint32_t x_21; uint32_t x_22; uint8_t x_23; 
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_decimalNumberFn_parseOptExp___lam__0___boxed), 1, 0);
x_11 = lean_string_utf8_next(x_4, x_5);
x_20 = lean_unsigned_to_nat(48u);
x_21 = lean_uint32_of_nat(x_20);
x_22 = lean_string_utf8_get(x_4, x_11);
x_23 = lean_uint32_dec_le(x_21, x_22);
if (x_23 == 0)
{
x_12 = x_23;
goto block_19;
}
else
{
lean_object* x_24; uint32_t x_25; uint8_t x_26; 
x_24 = lean_unsigned_to_nat(57u);
x_25 = lean_uint32_of_nat(x_24);
x_26 = lean_uint32_dec_le(x_22, x_25);
x_12 = x_26;
goto block_19;
}
block_19:
{
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
x_13 = l_Lean_Parser_ParserState_setPos(x_2, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_14 = lean_mk_string_unchecked("decimal number", 14, 14);
x_15 = lean_box(0);
x_16 = l_Lean_Parser_ParserState_setPos(x_2, x_11);
x_17 = lean_unbox(x_15);
x_18 = l_Lean_Parser_takeDigitsFn(x_10, x_14, x_17, x_1, x_16);
return x_18;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_decimalNumberFn_parseOptDot___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_decimalNumberFn_parseOptDot(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_decimalNumberFn_parseScientific(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = l_Lean_Parser_decimalNumberFn_parseOptDot(x_2, x_3);
x_5 = l_Lean_Parser_decimalNumberFn_parseOptExp(x_2, x_4);
x_6 = lean_mk_string_unchecked("scientific", 10, 10);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = l_Lean_Parser_mkNodeToken(x_7, x_1, x_2, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_decimalNumberFn_parseScientific___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_decimalNumberFn_parseScientific(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_decimalNumberFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_decimalNumberFn_parseOptExp___lam__0___boxed), 1, 0);
x_5 = lean_mk_string_unchecked("decimal number", 14, 14);
x_6 = lean_box(0);
x_7 = lean_unbox(x_6);
x_8 = l_Lean_Parser_takeDigitsFn(x_4, x_5, x_7, x_2, x_3);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_8, 2);
lean_inc(x_11);
x_12 = lean_string_utf8_at_end(x_10, x_11);
if (x_12 == 0)
{
uint32_t x_13; lean_object* x_14; uint32_t x_15; uint8_t x_16; 
x_13 = lean_string_utf8_get_fast(x_10, x_11);
lean_dec(x_11);
lean_dec(x_10);
x_14 = lean_unsigned_to_nat(46u);
x_15 = l_Char_ofNat(x_14);
x_16 = l_instDecidableEqChar(x_13, x_15);
if (x_16 == 0)
{
lean_object* x_17; uint32_t x_18; uint8_t x_19; 
x_17 = lean_unsigned_to_nat(101u);
x_18 = l_Char_ofNat(x_17);
x_19 = l_instDecidableEqChar(x_13, x_18);
if (x_19 == 0)
{
lean_object* x_20; uint32_t x_21; uint8_t x_22; 
x_20 = lean_unsigned_to_nat(69u);
x_21 = l_Char_ofNat(x_20);
x_22 = l_instDecidableEqChar(x_13, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_mk_string_unchecked("num", 3, 3);
x_24 = l_Lean_Name_mkStr1(x_23);
x_25 = l_Lean_Parser_mkNodeToken(x_24, x_1, x_2, x_8);
return x_25;
}
else
{
lean_object* x_26; 
x_26 = l_Lean_Parser_decimalNumberFn_parseScientific(x_1, x_2, x_8);
lean_dec(x_8);
return x_26;
}
}
else
{
lean_object* x_27; 
x_27 = l_Lean_Parser_decimalNumberFn_parseScientific(x_1, x_2, x_8);
lean_dec(x_8);
return x_27;
}
}
else
{
lean_object* x_28; 
x_28 = l_Lean_Parser_decimalNumberFn_parseScientific(x_1, x_2, x_8);
lean_dec(x_8);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_11);
lean_dec(x_10);
x_29 = lean_mk_string_unchecked("num", 3, 3);
x_30 = l_Lean_Name_mkStr1(x_29);
x_31 = l_Lean_Parser_mkNodeToken(x_30, x_1, x_2, x_8);
return x_31;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_binNumberFn___lam__0(uint32_t x_1) {
_start:
{
lean_object* x_2; uint32_t x_3; uint8_t x_4; 
x_2 = lean_unsigned_to_nat(48u);
x_3 = l_Char_ofNat(x_2);
x_4 = l_instDecidableEqChar(x_1, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint32_t x_6; uint8_t x_7; 
x_5 = lean_unsigned_to_nat(49u);
x_6 = l_Char_ofNat(x_5);
x_7 = l_instDecidableEqChar(x_1, x_6);
return x_7;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_binNumberFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_binNumberFn___lam__0___boxed), 1, 0);
x_5 = lean_mk_string_unchecked("binary number", 13, 13);
x_6 = lean_box(1);
x_7 = lean_unbox(x_6);
x_8 = l_Lean_Parser_takeDigitsFn(x_4, x_5, x_7, x_2, x_3);
x_9 = lean_mk_string_unchecked("num", 3, 3);
x_10 = l_Lean_Name_mkStr1(x_9);
x_11 = l_Lean_Parser_mkNodeToken(x_10, x_1, x_2, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_binNumberFn___lam__0___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Lean_Parser_binNumberFn___lam__0(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_octalNumberFn___lam__0(uint32_t x_1) {
_start:
{
lean_object* x_2; uint32_t x_3; uint8_t x_4; 
x_2 = lean_unsigned_to_nat(48u);
x_3 = l_Char_ofNat(x_2);
x_4 = lean_uint32_dec_le(x_3, x_1);
if (x_4 == 0)
{
return x_4;
}
else
{
lean_object* x_5; uint32_t x_6; uint8_t x_7; 
x_5 = lean_unsigned_to_nat(55u);
x_6 = l_Char_ofNat(x_5);
x_7 = lean_uint32_dec_le(x_1, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_octalNumberFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_octalNumberFn___lam__0___boxed), 1, 0);
x_5 = lean_mk_string_unchecked("octal number", 12, 12);
x_6 = lean_box(1);
x_7 = lean_unbox(x_6);
x_8 = l_Lean_Parser_takeDigitsFn(x_4, x_5, x_7, x_2, x_3);
x_9 = lean_mk_string_unchecked("num", 3, 3);
x_10 = l_Lean_Name_mkStr1(x_9);
x_11 = l_Lean_Parser_mkNodeToken(x_10, x_1, x_2, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_octalNumberFn___lam__0___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Lean_Parser_octalNumberFn___lam__0(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_hexNumberFn___lam__0(uint32_t x_1) {
_start:
{
uint8_t x_2; uint8_t x_10; lean_object* x_18; uint32_t x_19; uint8_t x_20; 
x_18 = lean_unsigned_to_nat(48u);
x_19 = l_Char_ofNat(x_18);
x_20 = lean_uint32_dec_le(x_19, x_1);
if (x_20 == 0)
{
x_10 = x_20;
goto block_17;
}
else
{
lean_object* x_21; uint32_t x_22; uint8_t x_23; 
x_21 = lean_unsigned_to_nat(57u);
x_22 = l_Char_ofNat(x_21);
x_23 = lean_uint32_dec_le(x_1, x_22);
x_10 = x_23;
goto block_17;
}
block_9:
{
if (x_2 == 0)
{
lean_object* x_3; uint32_t x_4; uint8_t x_5; 
x_3 = lean_unsigned_to_nat(65u);
x_4 = l_Char_ofNat(x_3);
x_5 = lean_uint32_dec_le(x_4, x_1);
if (x_5 == 0)
{
return x_5;
}
else
{
lean_object* x_6; uint32_t x_7; uint8_t x_8; 
x_6 = lean_unsigned_to_nat(70u);
x_7 = l_Char_ofNat(x_6);
x_8 = lean_uint32_dec_le(x_1, x_7);
return x_8;
}
}
else
{
return x_2;
}
}
block_17:
{
if (x_10 == 0)
{
lean_object* x_11; uint32_t x_12; uint8_t x_13; 
x_11 = lean_unsigned_to_nat(97u);
x_12 = l_Char_ofNat(x_11);
x_13 = lean_uint32_dec_le(x_12, x_1);
if (x_13 == 0)
{
x_2 = x_13;
goto block_9;
}
else
{
lean_object* x_14; uint32_t x_15; uint8_t x_16; 
x_14 = lean_unsigned_to_nat(102u);
x_15 = l_Char_ofNat(x_14);
x_16 = lean_uint32_dec_le(x_1, x_15);
x_2 = x_16;
goto block_9;
}
}
else
{
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_hexNumberFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_hexNumberFn___lam__0___boxed), 1, 0);
x_5 = lean_mk_string_unchecked("hexadecimal number", 18, 18);
x_6 = lean_box(1);
x_7 = lean_unbox(x_6);
x_8 = l_Lean_Parser_takeDigitsFn(x_4, x_5, x_7, x_2, x_3);
x_9 = lean_mk_string_unchecked("num", 3, 3);
x_10 = l_Lean_Name_mkStr1(x_9);
x_11 = l_Lean_Parser_mkNodeToken(x_10, x_1, x_2, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_hexNumberFn___lam__0___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Lean_Parser_hexNumberFn___lam__0(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_numberFnAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_12; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
x_12 = lean_string_utf8_at_end(x_4, x_5);
if (x_12 == 0)
{
uint32_t x_13; lean_object* x_14; uint32_t x_15; uint8_t x_16; 
x_13 = lean_string_utf8_get_fast(x_4, x_5);
x_14 = lean_unsigned_to_nat(48u);
x_15 = l_Char_ofNat(x_14);
x_16 = l_instDecidableEqChar(x_13, x_15);
if (x_16 == 0)
{
uint32_t x_17; uint8_t x_18; 
x_17 = lean_uint32_of_nat(x_14);
x_18 = lean_uint32_dec_le(x_17, x_13);
if (x_18 == 0)
{
x_6 = x_18;
goto block_11;
}
else
{
lean_object* x_19; uint32_t x_20; uint8_t x_21; 
x_19 = lean_unsigned_to_nat(57u);
x_20 = lean_uint32_of_nat(x_19);
x_21 = lean_uint32_dec_le(x_13, x_20);
x_6 = x_21;
goto block_11;
}
}
else
{
lean_object* x_22; uint32_t x_32; lean_object* x_33; uint32_t x_34; uint8_t x_35; 
x_22 = lean_string_utf8_next_fast(x_4, x_5);
x_32 = lean_string_utf8_get(x_4, x_22);
x_33 = lean_unsigned_to_nat(98u);
x_34 = l_Char_ofNat(x_33);
x_35 = l_instDecidableEqChar(x_32, x_34);
if (x_35 == 0)
{
lean_object* x_36; uint32_t x_37; uint8_t x_38; 
x_36 = lean_unsigned_to_nat(66u);
x_37 = l_Char_ofNat(x_36);
x_38 = l_instDecidableEqChar(x_32, x_37);
if (x_38 == 0)
{
lean_object* x_39; uint32_t x_40; uint8_t x_41; 
x_39 = lean_unsigned_to_nat(111u);
x_40 = l_Char_ofNat(x_39);
x_41 = l_instDecidableEqChar(x_32, x_40);
if (x_41 == 0)
{
lean_object* x_42; uint32_t x_43; uint8_t x_44; 
x_42 = lean_unsigned_to_nat(79u);
x_43 = l_Char_ofNat(x_42);
x_44 = l_instDecidableEqChar(x_32, x_43);
if (x_44 == 0)
{
lean_object* x_45; uint32_t x_46; uint8_t x_47; 
x_45 = lean_unsigned_to_nat(120u);
x_46 = l_Char_ofNat(x_45);
x_47 = l_instDecidableEqChar(x_32, x_46);
if (x_47 == 0)
{
lean_object* x_48; uint32_t x_49; uint8_t x_50; 
x_48 = lean_unsigned_to_nat(88u);
x_49 = l_Char_ofNat(x_48);
x_50 = l_instDecidableEqChar(x_32, x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_4);
x_51 = l_Lean_Parser_ParserState_setPos(x_2, x_22);
lean_dec(x_2);
x_52 = l_Lean_Parser_decimalNumberFn(x_5, x_1, x_51);
return x_52;
}
else
{
goto block_25;
}
}
else
{
goto block_25;
}
}
else
{
goto block_28;
}
}
else
{
goto block_28;
}
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
block_25:
{
lean_object* x_23; lean_object* x_24; 
x_23 = l_Lean_Parser_ParserState_next(x_2, x_4, x_22);
lean_dec(x_22);
lean_dec(x_4);
lean_dec(x_2);
x_24 = l_Lean_Parser_hexNumberFn(x_5, x_1, x_23);
return x_24;
}
block_28:
{
lean_object* x_26; lean_object* x_27; 
x_26 = l_Lean_Parser_ParserState_next(x_2, x_4, x_22);
lean_dec(x_22);
lean_dec(x_4);
lean_dec(x_2);
x_27 = l_Lean_Parser_octalNumberFn(x_5, x_1, x_26);
return x_27;
}
block_31:
{
lean_object* x_29; lean_object* x_30; 
x_29 = l_Lean_Parser_ParserState_next(x_2, x_4, x_22);
lean_dec(x_22);
lean_dec(x_4);
lean_dec(x_2);
x_30 = l_Lean_Parser_binNumberFn(x_5, x_1, x_29);
return x_30;
}
}
}
else
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_53 = lean_box(0);
x_54 = l_Lean_Parser_ParserState_mkEOIError(x_2, x_53);
return x_54;
}
block_11:
{
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_7 = lean_mk_string_unchecked("numeral", 7, 7);
x_8 = l_Lean_Parser_ParserState_mkError(x_2, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Lean_Parser_ParserState_next(x_2, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
x_10 = l_Lean_Parser_decimalNumberFn(x_5, x_1, x_9);
return x_10;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_isIdCont(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint32_t x_4; lean_object* x_5; uint32_t x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_2, 2);
x_4 = lean_string_utf8_get(x_1, x_3);
x_5 = lean_unsigned_to_nat(46u);
x_6 = l_Char_ofNat(x_5);
x_7 = l_instDecidableEqChar(x_4, x_6);
if (x_7 == 0)
{
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_string_utf8_next(x_1, x_3);
x_9 = lean_string_utf8_at_end(x_1, x_8);
if (x_9 == 0)
{
uint32_t x_10; uint8_t x_11; uint8_t x_19; lean_object* x_27; uint32_t x_28; uint8_t x_29; 
x_10 = lean_string_utf8_get(x_1, x_8);
lean_dec(x_8);
x_27 = lean_unsigned_to_nat(65u);
x_28 = lean_uint32_of_nat(x_27);
x_29 = lean_uint32_dec_le(x_28, x_10);
if (x_29 == 0)
{
x_19 = x_29;
goto block_26;
}
else
{
lean_object* x_30; uint32_t x_31; uint8_t x_32; 
x_30 = lean_unsigned_to_nat(90u);
x_31 = lean_uint32_of_nat(x_30);
x_32 = lean_uint32_dec_le(x_10, x_31);
x_19 = x_32;
goto block_26;
}
block_18:
{
if (x_11 == 0)
{
lean_object* x_12; uint32_t x_13; uint8_t x_14; 
x_12 = lean_unsigned_to_nat(95u);
x_13 = l_Char_ofNat(x_12);
x_14 = l_instDecidableEqChar(x_10, x_13);
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = l_Lean_isLetterLike(x_10);
if (x_15 == 0)
{
uint32_t x_16; uint8_t x_17; 
x_16 = l_Lean_idBeginEscape;
x_17 = l_instDecidableEqChar(x_10, x_16);
return x_17;
}
else
{
return x_7;
}
}
else
{
return x_7;
}
}
else
{
return x_7;
}
}
block_26:
{
if (x_19 == 0)
{
lean_object* x_20; uint32_t x_21; uint8_t x_22; 
x_20 = lean_unsigned_to_nat(97u);
x_21 = lean_uint32_of_nat(x_20);
x_22 = lean_uint32_dec_le(x_21, x_10);
if (x_22 == 0)
{
x_11 = x_22;
goto block_18;
}
else
{
lean_object* x_23; uint32_t x_24; uint8_t x_25; 
x_23 = lean_unsigned_to_nat(122u);
x_24 = lean_uint32_of_nat(x_23);
x_25 = lean_uint32_dec_le(x_10, x_24);
x_11 = x_25;
goto block_18;
}
}
else
{
return x_7;
}
}
}
else
{
lean_object* x_33; uint8_t x_34; 
lean_dec(x_8);
x_33 = lean_box(0);
x_34 = lean_unbox(x_33);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_isIdCont___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Parser_isIdCont(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Parser_Basic_0__Lean_Parser_isToken(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_box(0);
x_5 = lean_unbox(x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_nat_sub(x_2, x_1);
x_8 = lean_string_utf8_byte_size(x_6);
x_9 = lean_nat_dec_le(x_7, x_8);
lean_dec(x_8);
lean_dec(x_7);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_isToken___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l___private_Lean_Parser_Basic_0__Lean_Parser_isToken(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkTokenAndFixPos(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_5 = lean_mk_string_unchecked("token", 5, 5);
x_6 = lean_box(0);
x_7 = l_Lean_Parser_ParserState_mkErrorAt(x_4, x_5, x_1, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_3, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 3);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at___Lean_SearchPath_findAllWithExt_spec__0(x_10, x_2);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
lean_inc_n(x_1, 2);
lean_inc(x_13);
x_14 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_1);
lean_ctor_set(x_14, 2, x_1);
x_15 = lean_string_utf8_byte_size(x_8);
x_16 = lean_nat_add(x_1, x_15);
lean_dec(x_15);
lean_inc(x_16);
x_17 = l_Lean_Parser_ParserState_setPos(x_4, x_16);
x_18 = l_Lean_Parser_whitespace(x_3, x_17);
x_19 = lean_ctor_get(x_18, 2);
lean_inc(x_19);
lean_inc(x_16);
x_20 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_20, 0, x_13);
lean_ctor_set(x_20, 1, x_16);
lean_ctor_set(x_20, 2, x_19);
x_21 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_21, 0, x_14);
lean_ctor_set(x_21, 1, x_1);
lean_ctor_set(x_21, 2, x_20);
lean_ctor_set(x_21, 3, x_16);
lean_inc(x_8);
x_22 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_8);
x_23 = l_Lean_Parser_ParserState_pushSyntax(x_18, x_22);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_3);
x_24 = lean_mk_string_unchecked("forbidden token", 15, 15);
x_25 = lean_box(0);
x_26 = l_Lean_Parser_ParserState_mkErrorAt(x_4, x_24, x_1, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkTokenAndFixPos___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_mkTokenAndFixPos(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkIdResult(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
x_7 = l___private_Lean_Parser_Basic_0__Lean_Parser_isToken(x_1, x_6, x_2);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
lean_inc(x_6);
lean_inc(x_1);
lean_inc(x_9);
x_10 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_1);
lean_ctor_set(x_10, 2, x_6);
x_11 = l_Lean_Parser_whitespace(x_4, x_5);
x_12 = lean_ctor_get(x_11, 2);
lean_inc(x_12);
lean_inc_n(x_1, 2);
lean_inc(x_9);
x_13 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_1);
lean_ctor_set(x_13, 2, x_1);
lean_inc(x_6);
x_14 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_14, 0, x_9);
lean_ctor_set(x_14, 1, x_6);
lean_ctor_set(x_14, 2, x_12);
x_15 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_1);
lean_ctor_set(x_15, 2, x_14);
lean_ctor_set(x_15, 3, x_6);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_10);
lean_ctor_set(x_17, 2, x_3);
lean_ctor_set(x_17, 3, x_16);
x_18 = l_Lean_Parser_ParserState_pushSyntax(x_11, x_17);
return x_18;
}
else
{
lean_object* x_19; 
lean_dec(x_6);
lean_dec(x_3);
x_19 = l_Lean_Parser_mkTokenAndFixPos(x_1, x_2, x_4, x_5);
lean_dec(x_5);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkIdResult___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_mkIdResult(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_identFnAux_parse___lam__0(uint32_t x_1) {
_start:
{
uint8_t x_2; uint8_t x_18; uint8_t x_26; lean_object* x_34; uint32_t x_35; uint8_t x_36; 
x_34 = lean_unsigned_to_nat(65u);
x_35 = lean_uint32_of_nat(x_34);
x_36 = lean_uint32_dec_le(x_35, x_1);
if (x_36 == 0)
{
x_26 = x_36;
goto block_33;
}
else
{
lean_object* x_37; uint32_t x_38; uint8_t x_39; 
x_37 = lean_unsigned_to_nat(90u);
x_38 = lean_uint32_of_nat(x_37);
x_39 = lean_uint32_dec_le(x_1, x_38);
x_26 = x_39;
goto block_33;
}
block_17:
{
if (x_2 == 0)
{
lean_object* x_3; uint32_t x_4; uint8_t x_5; 
x_3 = lean_unsigned_to_nat(95u);
x_4 = l_Char_ofNat(x_3);
x_5 = l_instDecidableEqChar(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint32_t x_7; uint8_t x_8; 
x_6 = lean_unsigned_to_nat(39u);
x_7 = l_Char_ofNat(x_6);
x_8 = l_instDecidableEqChar(x_1, x_7);
if (x_8 == 0)
{
lean_object* x_9; uint32_t x_10; uint8_t x_11; 
x_9 = lean_unsigned_to_nat(33u);
x_10 = l_Char_ofNat(x_9);
x_11 = l_instDecidableEqChar(x_1, x_10);
if (x_11 == 0)
{
lean_object* x_12; uint32_t x_13; uint8_t x_14; 
x_12 = lean_unsigned_to_nat(63u);
x_13 = l_Char_ofNat(x_12);
x_14 = l_instDecidableEqChar(x_1, x_13);
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = l_Lean_isLetterLike(x_1);
if (x_15 == 0)
{
uint8_t x_16; 
x_16 = l_Lean_isSubScriptAlnum(x_1);
return x_16;
}
else
{
return x_15;
}
}
else
{
return x_14;
}
}
else
{
return x_11;
}
}
else
{
return x_8;
}
}
else
{
return x_5;
}
}
else
{
return x_2;
}
}
block_25:
{
if (x_18 == 0)
{
lean_object* x_19; uint32_t x_20; uint8_t x_21; 
x_19 = lean_unsigned_to_nat(48u);
x_20 = lean_uint32_of_nat(x_19);
x_21 = lean_uint32_dec_le(x_20, x_1);
if (x_21 == 0)
{
x_2 = x_21;
goto block_17;
}
else
{
lean_object* x_22; uint32_t x_23; uint8_t x_24; 
x_22 = lean_unsigned_to_nat(57u);
x_23 = lean_uint32_of_nat(x_22);
x_24 = lean_uint32_dec_le(x_1, x_23);
x_2 = x_24;
goto block_17;
}
}
else
{
return x_18;
}
}
block_33:
{
if (x_26 == 0)
{
lean_object* x_27; uint32_t x_28; uint8_t x_29; 
x_27 = lean_unsigned_to_nat(97u);
x_28 = lean_uint32_of_nat(x_27);
x_29 = lean_uint32_dec_le(x_28, x_1);
if (x_29 == 0)
{
x_18 = x_29;
goto block_25;
}
else
{
lean_object* x_30; uint32_t x_31; uint8_t x_32; 
x_30 = lean_unsigned_to_nat(122u);
x_31 = lean_uint32_of_nat(x_30);
x_32 = lean_uint32_dec_le(x_1, x_31);
x_18 = x_32;
goto block_25;
}
}
else
{
return x_26;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_identFnAux_parse___lam__1(uint32_t x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; 
x_2 = l_Lean_idEndEscape;
x_3 = l_instDecidableEqChar(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_identFnAux_parse(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_ctor_get(x_5, 2);
lean_inc(x_8);
x_9 = lean_string_utf8_at_end(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_21; uint32_t x_24; uint8_t x_25; uint8_t x_31; uint32_t x_39; uint8_t x_40; 
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_identFnAux_parse___lam__0___boxed), 1, 0);
x_24 = lean_string_utf8_get_fast(x_7, x_8);
x_39 = l_Lean_idBeginEscape;
x_40 = l_instDecidableEqChar(x_24, x_39);
if (x_40 == 0)
{
lean_object* x_41; uint32_t x_42; uint8_t x_43; 
x_41 = lean_unsigned_to_nat(65u);
x_42 = lean_uint32_of_nat(x_41);
x_43 = lean_uint32_dec_le(x_42, x_24);
if (x_43 == 0)
{
x_31 = x_43;
goto block_38;
}
else
{
lean_object* x_44; uint32_t x_45; uint8_t x_46; 
x_44 = lean_unsigned_to_nat(90u);
x_45 = lean_uint32_of_nat(x_44);
x_46 = lean_uint32_dec_le(x_24, x_45);
x_31 = x_46;
goto block_38;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
lean_dec(x_10);
x_47 = lean_alloc_closure((void*)(l_Lean_Parser_identFnAux_parse___lam__1___boxed), 1, 0);
x_48 = lean_string_utf8_next_fast(x_7, x_8);
lean_dec(x_8);
lean_inc(x_48);
x_49 = l_Lean_Parser_ParserState_setPos(x_5, x_48);
lean_dec(x_5);
x_50 = l_Lean_Parser_takeUntilFn(x_47, x_4, x_49);
x_51 = lean_ctor_get(x_50, 2);
lean_inc(x_51);
x_52 = lean_string_utf8_at_end(x_7, x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_53 = l_Lean_Parser_ParserState_next_x27(x_50, x_7, x_51, lean_box(0));
lean_dec(x_50);
x_54 = lean_string_utf8_extract(x_7, x_48, x_51);
lean_dec(x_51);
lean_dec(x_48);
x_55 = l_Lean_Name_str___override(x_3, x_54);
x_56 = l_Lean_Parser_isIdCont(x_7, x_53);
if (x_56 == 0)
{
lean_object* x_57; 
lean_dec(x_7);
x_57 = l_Lean_Parser_mkIdResult(x_1, x_2, x_55, x_4, x_53);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_53, 2);
lean_inc(x_58);
x_59 = l_Lean_Parser_ParserState_next(x_53, x_7, x_58);
lean_dec(x_58);
lean_dec(x_7);
lean_dec(x_53);
x_3 = x_55;
x_5 = x_59;
goto _start;
}
}
else
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_51);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_61 = lean_mk_string_unchecked("unterminated identifier escape", 30, 30);
x_62 = l_Lean_Parser_ParserState_mkUnexpectedErrorAt(x_50, x_61, x_48);
lean_dec(x_50);
return x_62;
}
}
block_20:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = l_Lean_Parser_ParserState_next(x_5, x_7, x_8);
lean_dec(x_5);
x_12 = l_Lean_Parser_takeWhileFn(x_10, x_4, x_11);
x_13 = lean_ctor_get(x_12, 2);
lean_inc(x_13);
x_14 = lean_string_utf8_extract(x_7, x_8, x_13);
lean_dec(x_8);
x_15 = l_Lean_Name_str___override(x_3, x_14);
x_16 = l_Lean_Parser_isIdCont(x_7, x_12);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_13);
lean_dec(x_7);
x_17 = l_Lean_Parser_mkIdResult(x_1, x_2, x_15, x_4, x_12);
return x_17;
}
else
{
lean_object* x_18; 
x_18 = l_Lean_Parser_ParserState_next(x_12, x_7, x_13);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_12);
x_3 = x_15;
x_5 = x_18;
goto _start;
}
}
block_23:
{
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
x_22 = l_Lean_Parser_mkTokenAndFixPos(x_1, x_2, x_4, x_5);
lean_dec(x_5);
return x_22;
}
else
{
goto block_20;
}
}
block_30:
{
if (x_25 == 0)
{
lean_object* x_26; uint32_t x_27; uint8_t x_28; 
x_26 = lean_unsigned_to_nat(95u);
x_27 = l_Char_ofNat(x_26);
x_28 = l_instDecidableEqChar(x_24, x_27);
if (x_28 == 0)
{
uint8_t x_29; 
x_29 = l_Lean_isLetterLike(x_24);
x_21 = x_29;
goto block_23;
}
else
{
x_21 = x_28;
goto block_23;
}
}
else
{
goto block_20;
}
}
block_38:
{
if (x_31 == 0)
{
lean_object* x_32; uint32_t x_33; uint8_t x_34; 
x_32 = lean_unsigned_to_nat(97u);
x_33 = lean_uint32_of_nat(x_32);
x_34 = lean_uint32_dec_le(x_33, x_24);
if (x_34 == 0)
{
x_25 = x_34;
goto block_30;
}
else
{
lean_object* x_35; uint32_t x_36; uint8_t x_37; 
x_35 = lean_unsigned_to_nat(122u);
x_36 = lean_uint32_of_nat(x_35);
x_37 = lean_uint32_dec_le(x_24, x_36);
x_25 = x_37;
goto block_30;
}
}
else
{
goto block_20;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_63 = lean_box(0);
x_64 = l_Lean_Parser_ParserState_mkEOIError(x_5, x_63);
return x_64;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_identFnAux_parse___lam__0___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Lean_Parser_identFnAux_parse___lam__0(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_identFnAux_parse___lam__1___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Lean_Parser_identFnAux_parse___lam__1(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_identFnAux_parse___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_identFnAux_parse(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_identFnAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_identFnAux_parse(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_identFnAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_identFnAux(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Parser_Basic_0__Lean_Parser_isIdFirstOrBeginEscape(uint32_t x_1) {
_start:
{
uint8_t x_2; uint8_t x_10; lean_object* x_18; uint32_t x_19; uint8_t x_20; 
x_18 = lean_unsigned_to_nat(65u);
x_19 = lean_uint32_of_nat(x_18);
x_20 = lean_uint32_dec_le(x_19, x_1);
if (x_20 == 0)
{
x_10 = x_20;
goto block_17;
}
else
{
lean_object* x_21; uint32_t x_22; uint8_t x_23; 
x_21 = lean_unsigned_to_nat(90u);
x_22 = lean_uint32_of_nat(x_21);
x_23 = lean_uint32_dec_le(x_1, x_22);
x_10 = x_23;
goto block_17;
}
block_9:
{
if (x_2 == 0)
{
lean_object* x_3; uint32_t x_4; uint8_t x_5; 
x_3 = lean_unsigned_to_nat(95u);
x_4 = l_Char_ofNat(x_3);
x_5 = l_instDecidableEqChar(x_1, x_4);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = l_Lean_isLetterLike(x_1);
if (x_6 == 0)
{
uint32_t x_7; uint8_t x_8; 
x_7 = l_Lean_idBeginEscape;
x_8 = l_instDecidableEqChar(x_1, x_7);
return x_8;
}
else
{
return x_6;
}
}
else
{
return x_5;
}
}
else
{
return x_2;
}
}
block_17:
{
if (x_10 == 0)
{
lean_object* x_11; uint32_t x_12; uint8_t x_13; 
x_11 = lean_unsigned_to_nat(97u);
x_12 = lean_uint32_of_nat(x_11);
x_13 = lean_uint32_dec_le(x_12, x_1);
if (x_13 == 0)
{
x_2 = x_13;
goto block_9;
}
else
{
lean_object* x_14; uint32_t x_15; uint8_t x_16; 
x_14 = lean_unsigned_to_nat(122u);
x_15 = lean_uint32_of_nat(x_14);
x_16 = lean_uint32_dec_le(x_1, x_15);
x_2 = x_16;
goto block_9;
}
}
else
{
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_isIdFirstOrBeginEscape___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l___private_Lean_Parser_Basic_0__Lean_Parser_isIdFirstOrBeginEscape(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_nameLitAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_box(0);
x_7 = lean_box(0);
x_8 = l_Lean_Parser_ParserState_next(x_3, x_5, x_1);
lean_dec(x_5);
x_9 = l_Lean_Parser_identFnAux_parse(x_1, x_6, x_7, x_2, x_8);
x_10 = lean_ctor_get(x_9, 4);
lean_inc(x_10);
x_11 = lean_box(0);
x_12 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at___Lean_Parser_ParserState_mkNode_spec__0(x_10, x_11);
if (x_12 == 0)
{
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_9, 0);
lean_inc(x_13);
x_14 = l_Lean_Parser_SyntaxStack_back(x_13);
lean_dec(x_13);
if (lean_obj_tag(x_14) == 3)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_15, 2);
lean_inc(x_19);
lean_dec(x_15);
x_20 = l_Lean_Parser_ParserState_popSyntax(x_9);
x_21 = lean_string_utf8_extract(x_17, x_18, x_19);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
x_22 = l_Lean_Syntax_mkNameLit(x_21, x_16);
x_23 = l_Lean_Parser_ParserState_pushSyntax(x_20, x_22);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_14);
x_24 = lean_mk_string_unchecked("invalid Name literal", 20, 20);
x_25 = l_Lean_Parser_ParserState_mkError(x_9, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_nameLitAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Parser_Basic_0__Lean_Parser_nameLitAux(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_tokenFnAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint32_t x_14; uint8_t x_15; uint8_t x_23; uint8_t x_31; lean_object* x_41; uint32_t x_42; uint8_t x_43; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
x_14 = lean_string_utf8_get(x_4, x_5);
x_41 = lean_unsigned_to_nat(34u);
x_42 = l_Char_ofNat(x_41);
x_43 = l_instDecidableEqChar(x_14, x_42);
if (x_43 == 0)
{
lean_object* x_44; uint32_t x_45; uint8_t x_46; 
x_44 = lean_unsigned_to_nat(39u);
x_45 = l_Char_ofNat(x_44);
x_46 = l_instDecidableEqChar(x_14, x_45);
if (x_46 == 0)
{
x_31 = x_46;
goto block_40;
}
else
{
uint32_t x_47; uint8_t x_48; 
x_47 = l_Lean_Parser_getNext(x_4, x_5);
x_48 = l_instDecidableEqChar(x_47, x_45);
if (x_48 == 0)
{
x_31 = x_46;
goto block_40;
}
else
{
x_31 = x_43;
goto block_40;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = l_Lean_Parser_ParserState_next(x_2, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
x_50 = l_Lean_Parser_strLitFnAux(x_5, x_1, x_49);
return x_50;
}
block_13:
{
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
lean_inc(x_5);
x_8 = l_Lean_Data_Trie_matchPrefix(lean_box(0), x_4, x_7, x_5);
lean_dec(x_4);
x_9 = lean_box(0);
x_10 = l_Lean_Parser_identFnAux_parse(x_5, x_8, x_9, x_1, x_2);
lean_dec(x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_Parser_ParserState_next(x_2, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
x_12 = l_Lean_Parser_rawStrLitFnAux(x_5, x_1, x_11);
return x_12;
}
}
block_22:
{
if (x_15 == 0)
{
lean_object* x_16; uint32_t x_17; uint8_t x_18; 
x_16 = lean_unsigned_to_nat(114u);
x_17 = l_Char_ofNat(x_16);
x_18 = l_instDecidableEqChar(x_14, x_17);
if (x_18 == 0)
{
x_6 = x_18;
goto block_13;
}
else
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_string_utf8_next(x_4, x_5);
x_20 = l_Lean_Parser_isRawStrLitStart(x_4, x_19);
x_6 = x_20;
goto block_13;
}
}
else
{
lean_object* x_21; 
lean_dec(x_4);
x_21 = l___private_Lean_Parser_Basic_0__Lean_Parser_nameLitAux(x_5, x_1, x_2);
lean_dec(x_2);
return x_21;
}
}
block_30:
{
if (x_23 == 0)
{
lean_object* x_24; uint32_t x_25; uint8_t x_26; 
x_24 = lean_unsigned_to_nat(96u);
x_25 = l_Char_ofNat(x_24);
x_26 = l_instDecidableEqChar(x_14, x_25);
if (x_26 == 0)
{
x_15 = x_26;
goto block_22;
}
else
{
uint32_t x_27; uint8_t x_28; 
x_27 = l_Lean_Parser_getNext(x_4, x_5);
x_28 = l___private_Lean_Parser_Basic_0__Lean_Parser_isIdFirstOrBeginEscape(x_27);
x_15 = x_28;
goto block_22;
}
}
else
{
lean_object* x_29; 
lean_dec(x_5);
lean_dec(x_4);
x_29 = l_Lean_Parser_numberFnAux(x_1, x_2);
return x_29;
}
}
block_40:
{
if (x_31 == 0)
{
lean_object* x_32; uint32_t x_33; uint8_t x_34; 
x_32 = lean_unsigned_to_nat(48u);
x_33 = lean_uint32_of_nat(x_32);
x_34 = lean_uint32_dec_le(x_33, x_14);
if (x_34 == 0)
{
x_23 = x_34;
goto block_30;
}
else
{
lean_object* x_35; uint32_t x_36; uint8_t x_37; 
x_35 = lean_unsigned_to_nat(57u);
x_36 = lean_uint32_of_nat(x_35);
x_37 = lean_uint32_dec_le(x_14, x_36);
x_23 = x_37;
goto block_30;
}
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = l_Lean_Parser_ParserState_next(x_2, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
x_39 = l_Lean_Parser_charLitFnAux(x_5, x_1, x_38);
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_updateTokenCache(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 3);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 4);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 5);
lean_inc(x_8);
x_9 = !lean_is_exclusive(x_3);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_3, 1);
x_11 = lean_ctor_get(x_3, 0);
lean_dec(x_11);
x_12 = l_Lean_Parser_SyntaxStack_size(x_5);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_eq(x_12, x_13);
lean_dec(x_12);
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_2);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_16 = lean_ctor_get(x_2, 5);
lean_dec(x_16);
x_17 = lean_ctor_get(x_2, 4);
lean_dec(x_17);
x_18 = lean_ctor_get(x_2, 3);
lean_dec(x_18);
x_19 = lean_ctor_get(x_2, 2);
lean_dec(x_19);
x_20 = lean_ctor_get(x_2, 1);
lean_dec(x_20);
x_21 = lean_ctor_get(x_2, 0);
lean_dec(x_21);
x_22 = l_Lean_Parser_SyntaxStack_back(x_5);
lean_inc(x_7);
x_23 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_7);
lean_ctor_set(x_23, 2, x_22);
lean_ctor_set(x_3, 0, x_23);
return x_2;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_2);
x_24 = l_Lean_Parser_SyntaxStack_back(x_5);
lean_inc(x_7);
x_25 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_7);
lean_ctor_set(x_25, 2, x_24);
lean_ctor_set(x_3, 0, x_25);
x_26 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_26, 0, x_5);
lean_ctor_set(x_26, 1, x_6);
lean_ctor_set(x_26, 2, x_7);
lean_ctor_set(x_26, 3, x_3);
lean_ctor_set(x_26, 4, x_4);
lean_ctor_set(x_26, 5, x_8);
return x_26;
}
}
else
{
lean_free_object(x_3);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_2;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_3, 1);
lean_inc(x_27);
lean_dec(x_3);
x_28 = l_Lean_Parser_SyntaxStack_size(x_5);
x_29 = lean_unsigned_to_nat(0u);
x_30 = lean_nat_dec_eq(x_28, x_29);
lean_dec(x_28);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 lean_ctor_release(x_2, 3);
 lean_ctor_release(x_2, 4);
 lean_ctor_release(x_2, 5);
 x_31 = x_2;
} else {
 lean_dec_ref(x_2);
 x_31 = lean_box(0);
}
x_32 = l_Lean_Parser_SyntaxStack_back(x_5);
lean_inc(x_7);
x_33 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_33, 0, x_1);
lean_ctor_set(x_33, 1, x_7);
lean_ctor_set(x_33, 2, x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_27);
if (lean_is_scalar(x_31)) {
 x_35 = lean_alloc_ctor(0, 6, 0);
} else {
 x_35 = x_31;
}
lean_ctor_set(x_35, 0, x_5);
lean_ctor_set(x_35, 1, x_6);
lean_ctor_set(x_35, 2, x_7);
lean_ctor_set(x_35, 3, x_34);
lean_ctor_set(x_35, 4, x_4);
lean_ctor_set(x_35, 5, x_8);
return x_35;
}
else
{
lean_dec(x_27);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_2;
}
}
}
else
{
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_tokenFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_3, 2);
lean_inc(x_6);
x_7 = lean_string_utf8_at_end(x_5, x_6);
lean_dec(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
lean_dec(x_1);
x_8 = lean_ctor_get(x_3, 3);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = l_instDecidableEqPos(x_10, x_6);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
x_12 = l___private_Lean_Parser_Basic_0__Lean_Parser_tokenFnAux(x_2, x_3);
x_13 = l___private_Lean_Parser_Basic_0__Lean_Parser_updateTokenCache(x_6, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_6);
lean_dec(x_2);
x_14 = lean_ctor_get(x_9, 2);
lean_inc(x_14);
x_15 = l_Lean_Parser_ParserState_pushSyntax(x_3, x_14);
x_16 = lean_ctor_get(x_9, 1);
lean_inc(x_16);
lean_dec(x_9);
x_17 = l_Lean_Parser_ParserState_setPos(x_15, x_16);
lean_dec(x_15);
return x_17;
}
}
else
{
lean_object* x_18; 
lean_dec(x_6);
lean_dec(x_2);
x_18 = l_Lean_Parser_ParserState_mkEOIError(x_3, x_1);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_peekTokenAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = l_Lean_Parser_ParserState_stackSize(x_2);
x_4 = lean_ctor_get(x_2, 2);
lean_inc(x_4);
x_5 = lean_box(0);
x_6 = l_Lean_Parser_tokenFn(x_5, x_1, x_2);
x_7 = lean_ctor_get(x_6, 4);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
x_9 = l_Lean_Parser_SyntaxStack_back(x_8);
lean_dec(x_8);
x_10 = l_Lean_Parser_ParserState_restore(x_6, x_3, x_4);
lean_dec(x_3);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_7);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_7, 0);
lean_dec(x_14);
lean_inc(x_6);
x_15 = l_Lean_Parser_ParserState_restore(x_6, x_3, x_4);
lean_dec(x_3);
lean_ctor_set_tag(x_7, 0);
lean_ctor_set(x_7, 0, x_6);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_7);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_7);
lean_inc(x_6);
x_17 = l_Lean_Parser_ParserState_restore(x_6, x_3, x_4);
lean_dec(x_3);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_6);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_peekToken(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_2, 3);
lean_inc(x_3);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
x_7 = l_instDecidableEqPos(x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_4);
x_8 = l_Lean_Parser_peekTokenAux(x_1, x_2);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_1);
x_9 = lean_ctor_get(x_4, 2);
lean_inc(x_9);
lean_dec(x_4);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_rawIdentFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
x_6 = lean_string_utf8_at_end(x_4, x_5);
lean_dec(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_box(0);
x_8 = lean_box(0);
x_9 = l_Lean_Parser_identFnAux_parse(x_5, x_7, x_8, x_1, x_2);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_1);
x_10 = lean_box(0);
x_11 = l_Lean_Parser_ParserState_mkEOIError(x_2, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_satisfySymbolFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
lean_inc(x_4);
lean_inc(x_2);
x_5 = l_Lean_Parser_tokenFn(x_2, x_3, x_4);
x_6 = lean_ctor_get(x_5, 4);
lean_inc(x_6);
x_7 = lean_box(0);
x_8 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at___Lean_Parser_ParserState_mkNode_spec__0(x_6, x_7);
if (x_8 == 0)
{
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_4, 2);
lean_inc(x_9);
lean_dec(x_4);
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
x_11 = l_Lean_Parser_SyntaxStack_back(x_10);
lean_dec(x_10);
if (lean_obj_tag(x_11) == 2)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_apply_1(x_1, x_12);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = l_Lean_Parser_ParserState_mkUnexpectedTokenErrors(x_5, x_2, x_9);
lean_dec(x_5);
return x_15;
}
else
{
lean_dec(x_9);
lean_dec(x_2);
return x_5;
}
}
else
{
lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_1);
x_16 = l_Lean_Parser_ParserState_mkUnexpectedTokenErrors(x_5, x_2, x_9);
lean_dec(x_5);
return x_16;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_symbolFnAux___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_string_dec_eq(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_symbolFnAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_symbolFnAux___lam__0___boxed), 2, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_6);
x_8 = l_Lean_Parser_satisfySymbolFn(x_5, x_7, x_3, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_symbolFnAux___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Parser_symbolFnAux___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_symbolInfo___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_symbolInfo(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_inc(x_1);
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_symbolInfo___lam__0), 2, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_epsilonInfo___lam__1___boxed), 1, 0);
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
x_6 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_3);
lean_ctor_set(x_7, 2, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_symbolFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_mk_string_unchecked("'", 1, 1);
lean_inc(x_4);
x_5 = lean_string_append(x_4, x_1);
x_6 = lean_string_append(x_5, x_4);
lean_dec(x_4);
x_7 = l_Lean_Parser_symbolFnAux(x_1, x_6, x_2, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_symbolNoAntiquot(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_string_utf8_byte_size(x_1);
x_4 = l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(x_1, x_3, x_2);
x_5 = l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(x_1, x_4, x_3);
x_6 = lean_string_utf8_extract(x_1, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_inc(x_6);
x_7 = l_Lean_Parser_symbolInfo(x_6);
x_8 = lean_alloc_closure((void*)(l_Lean_Parser_symbolFn), 3, 1);
lean_closure_set(x_8, 0, x_6);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_symbolNoAntiquot___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_symbolNoAntiquot(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_checkTailNoWs(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_getTailInfo(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 2);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_ctor_get(x_3, 2);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = l_instDecidableEqPos(x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
lean_dec(x_2);
x_7 = lean_box(0);
x_8 = lean_unbox(x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkTailNoWs___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Parser_checkTailNoWs(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolFnAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_5 = lean_box(0);
lean_inc(x_2);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
x_7 = l_Lean_Parser_tokenFn(x_6, x_3, x_4);
x_11 = lean_ctor_get(x_7, 4);
lean_inc(x_11);
x_12 = lean_box(0);
x_13 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at___Lean_Parser_ParserState_mkNode_spec__0(x_11, x_12);
if (x_13 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_7, 0);
lean_inc(x_14);
x_15 = l_Lean_Parser_SyntaxStack_back(x_14);
lean_dec(x_14);
switch (lean_obj_tag(x_15)) {
case 2:
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_string_dec_eq(x_1, x_16);
lean_dec(x_16);
lean_dec(x_1);
if (x_17 == 0)
{
goto block_10;
}
else
{
lean_dec(x_2);
return x_7;
}
}
case 3:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_15, 0);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_18, 2);
lean_inc(x_22);
lean_dec(x_18);
x_23 = lean_string_utf8_extract(x_20, x_21, x_22);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
x_24 = lean_string_dec_eq(x_1, x_23);
lean_dec(x_23);
if (x_24 == 0)
{
lean_dec(x_19);
lean_dec(x_1);
goto block_10;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_2);
x_25 = l_Lean_Parser_ParserState_popSyntax(x_7);
x_26 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_26, 0, x_19);
lean_ctor_set(x_26, 1, x_1);
x_27 = l_Lean_Parser_ParserState_pushSyntax(x_25, x_26);
return x_27;
}
}
default: 
{
lean_dec(x_15);
lean_dec(x_1);
goto block_10;
}
}
}
block_10:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_Parser_ParserState_mkUnexpectedTokenError(x_7, x_2, x_8);
lean_dec(x_7);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_mk_string_unchecked("'", 1, 1);
lean_inc(x_4);
x_5 = lean_string_append(x_4, x_1);
x_6 = lean_string_append(x_5, x_4);
lean_dec(x_4);
x_7 = l_Lean_Parser_nonReservedSymbolFnAux(x_1, x_6, x_2, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolInfo(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_epsilonInfo___lam__0___boxed), 1, 0);
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_epsilonInfo___lam__1___boxed), 1, 0);
if (x_2 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_4);
lean_ctor_set(x_8, 2, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_mk_string_unchecked("ident", 5, 5);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_14, 0, x_3);
lean_ctor_set(x_14, 1, x_4);
lean_ctor_set(x_14, 2, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolInfo___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l_Lean_Parser_nonReservedSymbolInfo(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolNoAntiquot(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_string_utf8_byte_size(x_1);
x_5 = l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(x_1, x_4, x_3);
x_6 = l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(x_1, x_5, x_4);
x_7 = lean_string_utf8_extract(x_1, x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
lean_inc(x_7);
x_8 = l_Lean_Parser_nonReservedSymbolInfo(x_7, x_2);
x_9 = lean_alloc_closure((void*)(l_Lean_Parser_nonReservedSymbolFn), 3, 1);
lean_closure_set(x_9, 0, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolNoAntiquot___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l_Lean_Parser_nonReservedSymbolNoAntiquot(x_1, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_strAux_parse(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_string_utf8_at_end(x_1, x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_5, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_ctor_get(x_8, 0);
x_10 = lean_string_utf8_at_end(x_9, x_7);
if (x_10 == 0)
{
uint32_t x_11; uint32_t x_12; uint8_t x_13; 
x_11 = lean_string_utf8_get_fast(x_1, x_3);
x_12 = lean_string_utf8_get_fast(x_9, x_7);
x_13 = l_instDecidableEqChar(x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_7);
lean_dec(x_3);
x_14 = l_Lean_Parser_ParserState_mkError(x_5, x_2);
return x_14;
}
else
{
if (x_10 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_string_utf8_next_fast(x_1, x_3);
lean_dec(x_3);
x_16 = l_Lean_Parser_ParserState_next_x27(x_5, x_9, x_7, lean_box(0));
lean_dec(x_7);
lean_dec(x_5);
x_3 = x_15;
x_5 = x_16;
goto _start;
}
else
{
lean_object* x_18; 
lean_dec(x_7);
lean_dec(x_3);
x_18 = l_Lean_Parser_ParserState_mkError(x_5, x_2);
return x_18;
}
}
}
else
{
lean_object* x_19; 
lean_dec(x_7);
lean_dec(x_3);
x_19 = l_Lean_Parser_ParserState_mkError(x_5, x_2);
return x_19;
}
}
else
{
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_strAux_parse___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_strAux_parse(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_strAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_strAux_parse(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_strAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_strAux(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_checkTailWs(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_getTailInfo(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 2);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 2);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_nat_dec_lt(x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
lean_dec(x_2);
x_7 = lean_box(0);
x_8 = lean_unbox(x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkTailWs___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Parser_checkTailWs(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkWsBeforeFn___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = l_Lean_Parser_SyntaxStack_back(x_3);
lean_dec(x_3);
x_5 = l_Lean_Parser_checkTailWs(x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = l_Lean_Parser_ParserState_mkError(x_2, x_1);
return x_6;
}
else
{
lean_dec(x_1);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkWsBeforeFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_checkWsBeforeFn___redArg(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkWsBeforeFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_checkWsBeforeFn(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_checkWsBefore_docString__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("checkWsBefore", 13, 13);
x_5 = l_Lean_Name_mkStr3(x_2, x_3, x_4);
x_6 = lean_mk_string_unchecked("The `ws` parser requires that there is some whitespace at this location.\nFor example, the parser `\"foo\" ws \"+\"` parses `foo +` or `foo/- -/+` but not `foo+`.\n\nThis parser has arity 0 - it does not capture anything. ", 215, 215);
x_7 = l_Lean_addBuiltinDocString(x_5, x_6, x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkWsBefore(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Parser_epsilonInfo;
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_checkWsBeforeFn___boxed), 3, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_String_anyAux___at___Lean_Parser_checkTailLinebreak_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_lt(x_3, x_2);
if (x_4 == 0)
{
lean_dec(x_3);
return x_4;
}
else
{
lean_object* x_5; uint32_t x_6; uint32_t x_7; uint8_t x_8; 
x_5 = lean_unsigned_to_nat(10u);
x_6 = l_Char_ofNat(x_5);
x_7 = lean_string_utf8_get(x_1, x_3);
x_8 = l_instDecidableEqChar(x_7, x_6);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_string_utf8_next(x_1, x_3);
lean_dec(x_3);
x_3 = x_9;
goto _start;
}
else
{
lean_dec(x_3);
return x_8;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_checkTailLinebreak(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_getTailInfo(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_2, 2);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 2);
lean_inc(x_6);
lean_dec(x_3);
x_7 = l_String_anyAux___at___Lean_Parser_checkTailLinebreak_spec__0(x_4, x_6, x_5);
lean_dec(x_6);
lean_dec(x_4);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
lean_dec(x_2);
x_8 = lean_box(0);
x_9 = lean_unbox(x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_String_anyAux___at___Lean_Parser_checkTailLinebreak_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_String_anyAux___at___Lean_Parser_checkTailLinebreak_spec__0(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkTailLinebreak___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Parser_checkTailLinebreak(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkLinebreakBeforeFn___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = l_Lean_Parser_SyntaxStack_back(x_3);
lean_dec(x_3);
x_5 = l_Lean_Parser_checkTailLinebreak(x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = l_Lean_Parser_ParserState_mkError(x_2, x_1);
return x_6;
}
else
{
lean_dec(x_1);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkLinebreakBeforeFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_checkLinebreakBeforeFn___redArg(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkLinebreakBeforeFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_checkLinebreakBeforeFn(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("checkLinebreakBefore", 20, 20);
x_5 = l_Lean_Name_mkStr3(x_2, x_3, x_4);
x_6 = lean_mk_string_unchecked("The `linebreak` parser requires that there is at least one line break at this location.\n(The line break may be inside a comment.)\n\nThis parser has arity 0 - it does not capture anything. ", 187, 187);
x_7 = l_Lean_addBuiltinDocString(x_5, x_6, x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkLinebreakBefore(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Parser_epsilonInfo;
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_checkLinebreakBeforeFn___boxed), 3, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Subarray_findSomeRevM_x3f_find___at_____private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 1)
{
lean_object* x_5; 
lean_dec(x_2);
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_2, x_6);
lean_dec(x_2);
x_8 = l_Subarray_get___redArg(x_1, x_7);
x_9 = l_Lean_Syntax_isNone(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_7);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_8);
return x_10;
}
else
{
lean_dec(x_8);
x_2 = x_7;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_findSomeRevM_x3f_find___at_____private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Subarray_findSomeRevM_x3f_find___at_____private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone_spec__0___redArg(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Parser_SyntaxStack_toSubarray(x_1);
x_3 = l_Subarray_size___redArg(x_2);
x_4 = l_Subarray_findSomeRevM_x3f_find___at_____private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone_spec__0___redArg(x_2, x_3);
lean_dec(x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Subarray_findSomeRevM_x3f_find___at_____private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Subarray_findSomeRevM_x3f_find___at_____private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone_spec__0___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Subarray_findSomeRevM_x3f_find___at_____private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Subarray_findSomeRevM_x3f_find___at_____private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone_spec__0(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoWsBeforeFn___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = l___private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone(x_3);
x_5 = l_Lean_Parser_checkTailNoWs(x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = l_Lean_Parser_ParserState_mkError(x_2, x_1);
return x_6;
}
else
{
lean_dec(x_1);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoWsBeforeFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_checkNoWsBeforeFn___redArg(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoWsBeforeFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_checkNoWsBeforeFn(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("checkNoWsBefore", 15, 15);
x_5 = l_Lean_Name_mkStr3(x_2, x_3, x_4);
x_6 = lean_mk_string_unchecked("The `noWs` parser requires that there is *no* whitespace between the preceding and following\nparsers. For example, the parser `\"foo\" noWs \"+\"` parses `foo+` but not `foo +`.\n\nThis is almost the same as `\"foo+\"`, but using this parser will make `foo+` a token, which may cause\nproblems for the use of `\"foo\"` and `\"+\"` as separate tokens in other parsers.\n\nThis parser has arity 0 - it does not capture anything. ", 412, 412);
x_7 = l_Lean_addBuiltinDocString(x_5, x_6, x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoWsBefore(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Parser_epsilonInfo;
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_checkNoWsBeforeFn___boxed), 3, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_unicodeSymbolFnAux___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_string_dec_eq(x_3, x_1);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = lean_string_dec_eq(x_3, x_2);
return x_5;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolFnAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_unicodeSymbolFnAux___lam__0___boxed), 3, 2);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_2);
x_7 = l_Lean_Parser_satisfySymbolFn(x_6, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolFnAux___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_Parser_unicodeSymbolFnAux___lam__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolInfo___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolInfo(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_inc(x_1);
lean_inc(x_2);
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_unicodeSymbolInfo___lam__0), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_epsilonInfo___lam__1___boxed), 1, 0);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_4);
lean_ctor_set(x_9, 2, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_5 = lean_mk_string_unchecked("'", 1, 1);
lean_inc(x_5);
x_6 = lean_string_append(x_5, x_1);
x_7 = lean_mk_string_unchecked("', '", 4, 4);
x_8 = lean_string_append(x_6, x_7);
lean_dec(x_7);
x_9 = lean_string_append(x_8, x_2);
x_10 = lean_string_append(x_9, x_5);
lean_dec(x_5);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Lean_Parser_unicodeSymbolFnAux(x_1, x_2, x_12, x_3, x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolNoAntiquot(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_string_utf8_byte_size(x_1);
x_5 = l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(x_1, x_4, x_3);
x_6 = l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(x_1, x_5, x_4);
x_7 = lean_string_utf8_extract(x_1, x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
x_8 = lean_string_utf8_byte_size(x_2);
x_9 = l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(x_2, x_8, x_3);
x_10 = l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(x_2, x_9, x_8);
x_11 = lean_string_utf8_extract(x_2, x_9, x_10);
lean_dec(x_10);
lean_dec(x_9);
lean_inc(x_11);
lean_inc(x_7);
x_12 = l_Lean_Parser_unicodeSymbolInfo(x_7, x_11);
x_13 = lean_alloc_closure((void*)(l_Lean_Parser_unicodeSymbolFn), 4, 2);
lean_closure_set(x_13, 0, x_7);
lean_closure_set(x_13, 1, x_11);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolNoAntiquot___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_unicodeSymbolNoAntiquot(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAtomicInfo(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_epsilonInfo___lam__0___boxed), 1, 0);
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_epsilonInfo___lam__1___boxed), 1, 0);
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
x_6 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_3);
lean_ctor_set(x_7, 2, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_expectTokenFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_box(0);
lean_inc(x_2);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
x_7 = l_Lean_Parser_tokenFn(x_6, x_3, x_4);
x_8 = lean_ctor_get(x_7, 4);
lean_inc(x_8);
x_9 = lean_box(0);
x_10 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at___Lean_Parser_ParserState_mkNode_spec__0(x_8, x_9);
if (x_10 == 0)
{
lean_dec(x_2);
return x_7;
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
x_12 = l_Lean_Parser_SyntaxStack_back(x_11);
lean_dec(x_11);
x_13 = l_Lean_Syntax_isOfKind(x_12, x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Lean_Parser_ParserState_mkUnexpectedTokenError(x_7, x_2, x_14);
lean_dec(x_7);
return x_15;
}
else
{
lean_dec(x_2);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_expectTokenFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_expectTokenFn(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_numLitFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_mk_string_unchecked("num", 3, 3);
x_4 = l_Lean_Name_mkStr1(x_3);
x_5 = lean_mk_string_unchecked("numeral", 7, 7);
x_6 = l_Lean_Parser_expectTokenFn(x_4, x_5, x_1, x_2);
lean_dec(x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_Parser_numLitNoAntiquot() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_mk_string_unchecked("num", 3, 3);
x_2 = l_Lean_Parser_mkAtomicInfo(x_1);
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_numLitFn), 2, 0);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_scientificLitFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_mk_string_unchecked("scientific", 10, 10);
x_4 = l_Lean_Name_mkStr1(x_3);
x_5 = lean_mk_string_unchecked("scientific number", 17, 17);
x_6 = l_Lean_Parser_expectTokenFn(x_4, x_5, x_1, x_2);
lean_dec(x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_Parser_scientificLitNoAntiquot() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_mk_string_unchecked("scientific", 10, 10);
x_2 = l_Lean_Parser_mkAtomicInfo(x_1);
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_scientificLitFn), 2, 0);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_strLitFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_mk_string_unchecked("str", 3, 3);
x_4 = l_Lean_Name_mkStr1(x_3);
x_5 = lean_mk_string_unchecked("string literal", 14, 14);
x_6 = l_Lean_Parser_expectTokenFn(x_4, x_5, x_1, x_2);
lean_dec(x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_Parser_strLitNoAntiquot() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_mk_string_unchecked("str", 3, 3);
x_2 = l_Lean_Parser_mkAtomicInfo(x_1);
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_strLitFn), 2, 0);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_charLitFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_mk_string_unchecked("char", 4, 4);
x_4 = l_Lean_Name_mkStr1(x_3);
x_5 = lean_mk_string_unchecked("character literal", 17, 17);
x_6 = l_Lean_Parser_expectTokenFn(x_4, x_5, x_1, x_2);
lean_dec(x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_Parser_charLitNoAntiquot() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_mk_string_unchecked("char", 4, 4);
x_2 = l_Lean_Parser_mkAtomicInfo(x_1);
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_charLitFn), 2, 0);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nameLitFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_mk_string_unchecked("name", 4, 4);
x_4 = l_Lean_Name_mkStr1(x_3);
x_5 = lean_mk_string_unchecked("Name literal", 12, 12);
x_6 = l_Lean_Parser_expectTokenFn(x_4, x_5, x_1, x_2);
lean_dec(x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_Parser_nameLitNoAntiquot() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_mk_string_unchecked("name", 4, 4);
x_2 = l_Lean_Parser_mkAtomicInfo(x_1);
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_nameLitFn), 2, 0);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_identFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_mk_string_unchecked("ident", 5, 5);
x_4 = l_Lean_Name_mkStr1(x_3);
x_5 = lean_mk_string_unchecked("identifier", 10, 10);
x_6 = l_Lean_Parser_expectTokenFn(x_4, x_5, x_1, x_2);
lean_dec(x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_Parser_identNoAntiquot() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_mk_string_unchecked("ident", 5, 5);
x_2 = l_Lean_Parser_mkAtomicInfo(x_1);
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_identFn), 2, 0);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_rawIdentNoAntiquot() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_epsilonInfo___lam__0___boxed), 1, 0);
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_epsilonInfo___lam__1___boxed), 1, 0);
x_3 = lean_box(1);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_rawIdentFn), 2, 0);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_identEqFn___lam__0(uint8_t x_1, lean_object* x_2) {
_start:
{
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_identEqFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_4 = lean_mk_string_unchecked("identifier", 10, 10);
x_5 = lean_box(0);
lean_inc(x_4);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
x_7 = l_Lean_Parser_tokenFn(x_6, x_2, x_3);
x_8 = lean_ctor_get(x_7, 4);
lean_inc(x_8);
x_9 = lean_box(0);
x_10 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at___Lean_Parser_ParserState_mkNode_spec__0(x_8, x_9);
if (x_10 == 0)
{
lean_dec(x_4);
lean_dec(x_1);
return x_7;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
x_12 = l_Lean_Parser_SyntaxStack_back(x_11);
lean_dec(x_11);
if (lean_obj_tag(x_12) == 3)
{
lean_object* x_13; uint8_t x_14; 
lean_dec(x_4);
x_13 = lean_ctor_get(x_12, 2);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_name_eq(x_13, x_1);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_15 = lean_box(x_14);
x_16 = lean_alloc_closure((void*)(l_Lean_Parser_identEqFn___lam__0___boxed), 2, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = lean_mk_string_unchecked("identifier '", 12, 12);
x_18 = l_Lean_Name_toString(x_1, x_10, x_16);
x_19 = lean_string_append(x_17, x_18);
lean_dec(x_18);
x_20 = lean_mk_string_unchecked("'", 1, 1);
x_21 = lean_string_append(x_19, x_20);
lean_dec(x_20);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Lean_Parser_ParserState_mkUnexpectedTokenError(x_7, x_21, x_22);
lean_dec(x_7);
return x_23;
}
else
{
lean_dec(x_1);
return x_7;
}
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_12);
lean_dec(x_1);
x_24 = lean_unsigned_to_nat(0u);
x_25 = l_Lean_Parser_ParserState_mkUnexpectedTokenError(x_7, x_4, x_24);
lean_dec(x_7);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_identEqFn___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_Parser_identEqFn___lam__0(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_identEq(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_mk_string_unchecked("ident", 5, 5);
x_3 = l_Lean_Parser_mkAtomicInfo(x_2);
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_identEqFn), 3, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_hygieneInfoFn___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_inc(x_1);
lean_inc(x_2);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_1);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_1);
x_6 = lean_box(0);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_2);
lean_ctor_set(x_8, 2, x_6);
lean_ctor_set(x_8, 3, x_7);
x_9 = lean_mk_string_unchecked("hygieneInfo", 11, 11);
x_10 = l_Lean_Name_mkStr1(x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_mk_empty_array_with_capacity(x_11);
x_13 = lean_array_push(x_12, x_8);
x_14 = lean_box(2);
x_15 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_10);
lean_ctor_set(x_15, 2, x_13);
x_16 = l_Lean_Parser_ParserState_pushSyntax(x_4, x_15);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_hygieneInfoFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_9; uint8_t x_10; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_3, 0);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
x_10 = l_Lean_Parser_SyntaxStack_isEmpty(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_Parser_SyntaxStack_back(x_9);
lean_dec(x_9);
x_12 = l_Lean_Syntax_getTailInfo(x_11);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_12, 2);
x_15 = lean_ctor_get(x_12, 3);
lean_inc_n(x_15, 2);
lean_inc(x_4);
x_16 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_16, 0, x_4);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set(x_16, 2, x_15);
x_17 = l_Lean_Parser_ParserState_popSyntax(x_2);
lean_inc(x_15);
lean_inc(x_16);
lean_ctor_set(x_12, 2, x_16);
x_18 = l_Lean_Syntax_setTailInfo(x_11, x_12);
x_19 = l_Lean_Parser_ParserState_pushSyntax(x_17, x_18);
x_20 = l_Lean_Parser_hygieneInfoFn___lam__0(x_15, x_16, x_14, x_19);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_21 = lean_ctor_get(x_12, 0);
x_22 = lean_ctor_get(x_12, 1);
x_23 = lean_ctor_get(x_12, 2);
x_24 = lean_ctor_get(x_12, 3);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_12);
lean_inc_n(x_24, 2);
lean_inc(x_4);
x_25 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_25, 0, x_4);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_25, 2, x_24);
x_26 = l_Lean_Parser_ParserState_popSyntax(x_2);
lean_inc(x_24);
lean_inc(x_25);
x_27 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_27, 0, x_21);
lean_ctor_set(x_27, 1, x_22);
lean_ctor_set(x_27, 2, x_25);
lean_ctor_set(x_27, 3, x_24);
x_28 = l_Lean_Syntax_setTailInfo(x_11, x_27);
x_29 = l_Lean_Parser_ParserState_pushSyntax(x_26, x_28);
x_30 = l_Lean_Parser_hygieneInfoFn___lam__0(x_24, x_25, x_23, x_29);
return x_30;
}
}
else
{
lean_dec(x_12);
lean_dec(x_11);
goto block_8;
}
}
else
{
lean_dec(x_9);
goto block_8;
}
block_8:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
lean_inc_n(x_5, 2);
lean_inc(x_4);
x_6 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
lean_ctor_set(x_6, 2, x_5);
lean_inc(x_6);
x_7 = l_Lean_Parser_hygieneInfoFn___lam__0(x_5, x_6, x_6, x_2);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_hygieneInfoFn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_hygieneInfoFn(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_hygieneInfoNoAntiquot() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_mk_string_unchecked("hygieneInfo", 11, 11);
x_2 = l_Lean_Name_mkStr1(x_1);
x_3 = l_Lean_Parser_epsilonInfo;
x_4 = l_Lean_Parser_nodeInfo(x_2, x_3);
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_hygieneInfoFn___boxed), 2, 0);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepTop(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_Parser_SyntaxStack_back(x_1);
x_4 = l_Lean_Parser_SyntaxStack_shrink(x_1, x_2);
x_5 = l_Lean_Parser_SyntaxStack_push(x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepTop___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_ParserState_keepTop(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepNewError(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = l_Lean_Parser_ParserState_keepTop(x_4, x_2);
lean_ctor_set(x_1, 0, x_5);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_1, 2);
x_9 = lean_ctor_get(x_1, 3);
x_10 = lean_ctor_get(x_1, 4);
x_11 = lean_ctor_get(x_1, 5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_1);
x_12 = l_Lean_Parser_ParserState_keepTop(x_6, x_2);
x_13 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_7);
lean_ctor_set(x_13, 2, x_8);
lean_ctor_set(x_13, 3, x_9);
lean_ctor_set(x_13, 4, x_10);
lean_ctor_set(x_13, 5, x_11);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepNewError___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_ParserState_keepNewError(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepPrevError(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 4);
lean_dec(x_8);
x_9 = lean_ctor_get(x_1, 2);
lean_dec(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_dec(x_10);
x_11 = l_Lean_Parser_SyntaxStack_shrink(x_7, x_2);
lean_ctor_set(x_1, 4, x_4);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_5);
lean_ctor_set(x_1, 0, x_11);
return x_1;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 3);
x_14 = lean_ctor_get(x_1, 5);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_1);
x_15 = l_Lean_Parser_SyntaxStack_shrink(x_12, x_2);
x_16 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_5);
lean_ctor_set(x_16, 2, x_3);
lean_ctor_set(x_16, 3, x_13);
lean_ctor_set(x_16, 4, x_4);
lean_ctor_set(x_16, 5, x_14);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepPrevError___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_ParserState_keepPrevError(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mergeErrors(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 4);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 5);
lean_inc(x_9);
if (lean_obj_tag(x_8) == 0)
{
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_1;
}
else
{
lean_object* x_15; uint8_t x_16; 
lean_dec(x_1);
x_15 = lean_ctor_get(x_8, 0);
lean_inc(x_15);
lean_dec(x_8);
lean_inc(x_15);
lean_inc(x_3);
x_16 = l___private_Lean_Parser_Types_0__Lean_Parser_beqError____x40_Lean_Parser_Types___hyg_440_(x_3, x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = l_Lean_Parser_Error_merge(x_3, x_15);
x_10 = x_17;
goto block_14;
}
else
{
lean_dec(x_3);
x_10 = x_15;
goto block_14;
}
}
block_14:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l_Lean_Parser_SyntaxStack_shrink(x_4, x_2);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_10);
x_13 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_5);
lean_ctor_set(x_13, 2, x_6);
lean_ctor_set(x_13, 3, x_7);
lean_ctor_set(x_13, 4, x_12);
lean_ctor_set(x_13, 5, x_9);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mergeErrors___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_ParserState_mergeErrors(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepLatest(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 4);
lean_dec(x_5);
x_6 = l_Lean_Parser_ParserState_keepTop(x_4, x_2);
x_7 = lean_box(0);
lean_ctor_set(x_1, 4, x_7);
lean_ctor_set(x_1, 0, x_6);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ctor_get(x_1, 2);
x_11 = lean_ctor_get(x_1, 3);
x_12 = lean_ctor_get(x_1, 5);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
x_13 = l_Lean_Parser_ParserState_keepTop(x_8, x_2);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_9);
lean_ctor_set(x_15, 2, x_10);
lean_ctor_set(x_15, 3, x_11);
lean_ctor_set(x_15, 4, x_14);
lean_ctor_set(x_15, 5, x_12);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepLatest___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_ParserState_keepLatest(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_replaceLongest(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_ParserState_keepLatest(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_replaceLongest___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_ParserState_replaceLongest(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_invalidLongestMatchParser(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_mk_string_unchecked("longestMatch parsers must generate exactly one Syntax node", 58, 58);
x_3 = l_Lean_Parser_ParserState_mkError(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_runLongestMatchParser(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_12; lean_object* x_13; lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_5, 0);
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_35; 
lean_dec(x_2);
x_35 = lean_unsigned_to_nat(1024u);
x_25 = x_35;
goto block_34;
}
else
{
x_25 = x_2;
goto block_34;
}
block_11:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Lean_Parser_ParserState_shrinkStack(x_7, x_6);
lean_dec(x_6);
x_9 = lean_box(0);
x_10 = l_Lean_Parser_ParserState_pushSyntax(x_8, x_9);
return x_10;
}
block_23:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_apply_2(x_3, x_4, x_13);
x_15 = l_Lean_Parser_ParserState_stackSize(x_14);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_12, x_16);
x_18 = lean_nat_dec_eq(x_15, x_17);
lean_dec(x_17);
lean_dec(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_14, 4);
lean_inc(x_19);
x_20 = lean_box(0);
x_21 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at___Lean_Parser_ParserState_mkNode_spec__0(x_19, x_20);
if (x_21 == 0)
{
x_6 = x_12;
x_7 = x_14;
goto block_11;
}
else
{
if (x_18 == 0)
{
lean_object* x_22; 
lean_dec(x_12);
x_22 = l_Lean_Parser_invalidLongestMatchParser(x_14);
return x_22;
}
else
{
x_6 = x_12;
x_7 = x_14;
goto block_11;
}
}
}
else
{
lean_dec(x_12);
return x_14;
}
}
block_34:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_5, 2);
x_27 = lean_ctor_get(x_5, 3);
x_28 = lean_ctor_get(x_5, 4);
x_29 = lean_ctor_get(x_5, 5);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_24);
x_30 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_30, 0, x_24);
lean_ctor_set(x_30, 1, x_25);
lean_ctor_set(x_30, 2, x_26);
lean_ctor_set(x_30, 3, x_27);
lean_ctor_set(x_30, 4, x_28);
lean_ctor_set(x_30, 5, x_29);
x_31 = l_Lean_Parser_ParserState_stackSize(x_30);
if (lean_obj_tag(x_1) == 0)
{
x_12 = x_31;
x_13 = x_30;
goto block_23;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_1, 0);
lean_inc(x_32);
lean_dec(x_1);
x_33 = l_Lean_Parser_ParserState_pushSyntax(x_30, x_32);
x_12 = x_31;
x_13 = x_33;
goto block_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_runLongestMatchParser___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_runLongestMatchParser(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchStep___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 2);
x_8 = lean_ctor_get(x_1, 4);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = lean_unsigned_to_nat(1u);
x_4 = x_9;
goto block_7;
}
else
{
lean_object* x_10; 
x_10 = lean_unsigned_to_nat(0u);
x_4 = x_10;
goto block_7;
}
block_7:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_inc(x_3);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchStep(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
lean_inc(x_5);
x_10 = l_Lean_Parser_longestMatchStep___lam__0(x_9, x_5);
x_11 = l_Lean_Parser_ParserState_stackSize(x_9);
lean_inc(x_9);
x_12 = l_Lean_Parser_ParserState_restore(x_9, x_11, x_4);
x_13 = l_Lean_Parser_runLongestMatchParser(x_1, x_3, x_7, x_8, x_12);
lean_dec(x_12);
lean_inc(x_6);
x_17 = l_Lean_Parser_longestMatchStep___lam__0(x_13, x_6);
x_18 = lean_ctor_get(x_10, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
x_20 = lean_nat_dec_lt(x_18, x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_27; 
x_21 = lean_ctor_get(x_9, 2);
lean_inc(x_21);
x_22 = lean_ctor_get(x_9, 4);
lean_inc(x_22);
x_23 = lean_ctor_get(x_9, 1);
lean_inc(x_23);
lean_dec(x_9);
x_27 = lean_nat_dec_eq(x_18, x_19);
lean_dec(x_19);
lean_dec(x_18);
if (x_27 == 0)
{
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_6);
goto block_26;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_28 = lean_ctor_get(x_10, 1);
lean_inc(x_28);
lean_dec(x_10);
x_29 = lean_ctor_get(x_17, 1);
lean_inc(x_29);
lean_dec(x_17);
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
x_32 = lean_nat_dec_lt(x_30, x_31);
if (x_32 == 0)
{
uint8_t x_33; 
x_33 = lean_nat_dec_eq(x_30, x_31);
lean_dec(x_31);
lean_dec(x_30);
if (x_33 == 0)
{
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_6);
goto block_26;
}
else
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_34 = lean_ctor_get(x_28, 1);
lean_inc(x_34);
lean_dec(x_28);
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
lean_dec(x_29);
x_36 = lean_nat_dec_lt(x_34, x_35);
if (x_36 == 0)
{
uint8_t x_37; 
x_37 = lean_nat_dec_eq(x_34, x_35);
lean_dec(x_35);
lean_dec(x_34);
if (x_37 == 0)
{
lean_dec(x_6);
goto block_26;
}
else
{
lean_dec(x_21);
lean_dec(x_5);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_47; uint8_t x_48; 
lean_dec(x_11);
x_38 = lean_ctor_get(x_13, 0);
lean_inc(x_38);
x_47 = lean_ctor_get(x_13, 1);
lean_inc(x_47);
x_48 = lean_nat_dec_le(x_47, x_23);
if (x_48 == 0)
{
lean_dec(x_47);
x_39 = x_23;
goto block_46;
}
else
{
lean_dec(x_23);
x_39 = x_47;
goto block_46;
}
block_46:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_13, 2);
lean_inc(x_40);
x_41 = lean_ctor_get(x_13, 3);
lean_inc(x_41);
x_42 = lean_ctor_get(x_13, 4);
lean_inc(x_42);
x_43 = lean_ctor_get(x_13, 5);
lean_inc(x_43);
lean_dec(x_13);
x_44 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_44, 0, x_38);
lean_ctor_set(x_44, 1, x_39);
lean_ctor_set(x_44, 2, x_40);
lean_ctor_set(x_44, 3, x_41);
lean_ctor_set(x_44, 4, x_42);
lean_ctor_set(x_44, 5, x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_6);
return x_45;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_23);
x_49 = lean_ctor_get(x_22, 0);
lean_inc(x_49);
lean_dec(x_22);
x_50 = l_Lean_Parser_ParserState_mergeErrors(x_13, x_11, x_49);
lean_dec(x_11);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_6);
return x_51;
}
}
}
else
{
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_11);
lean_dec(x_5);
goto block_16;
}
}
}
else
{
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_11);
lean_dec(x_5);
goto block_16;
}
}
block_26:
{
lean_object* x_24; lean_object* x_25; 
x_24 = l_Lean_Parser_ParserState_keepPrevError(x_13, x_11, x_21, x_22, x_23);
lean_dec(x_11);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_5);
return x_25;
}
}
else
{
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
goto block_16;
}
block_16:
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Lean_Parser_ParserState_keepNewError(x_13, x_2);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_6);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchStep___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_longestMatchStep___lam__0(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchStep___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Parser_longestMatchStep(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchMkResult(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_add(x_1, x_3);
x_5 = l_Lean_Parser_ParserState_stackSize(x_2);
x_6 = lean_nat_dec_lt(x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
if (x_6 == 0)
{
return x_2;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_mk_string_unchecked("choice", 6, 6);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = l_Lean_Parser_ParserState_mkNode(x_2, x_8, x_1);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchMkResult___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_longestMatchMkResult(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchFnAux_parse(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_9; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_9 = l_Lean_Parser_longestMatchMkResult(x_2, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_dec(x_6);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
lean_inc(x_7);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_15 = l_Lean_Parser_longestMatchStep(x_1, x_2, x_3, x_4, x_5, x_12, x_14, x_7, x_8);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_5 = x_17;
x_6 = x_11;
x_8 = x_16;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchFnAux_parse___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Parser_longestMatchFnAux_parse(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchFnAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Parser_longestMatchFnAux_parse(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchFnAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Parser_longestMatchFnAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
lean_dec(x_1);
x_5 = lean_mk_string_unchecked("longestMatch: empty list", 24, 24);
x_6 = l_Lean_Parser_ParserState_mkError(x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l_Lean_Parser_runLongestMatchParser(x_1, x_9, x_11, x_3, x_4);
lean_dec(x_4);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
lean_dec(x_2);
x_14 = l_Lean_Parser_ParserState_stackSize(x_4);
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_4, 2);
lean_inc(x_16);
x_17 = lean_ctor_get(x_13, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
lean_inc(x_3);
lean_inc(x_15);
lean_inc(x_1);
x_19 = l_Lean_Parser_runLongestMatchParser(x_1, x_15, x_18, x_3, x_4);
lean_dec(x_4);
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
lean_dec(x_13);
x_21 = l_Lean_Parser_longestMatchFnAux_parse(x_1, x_14, x_15, x_16, x_20, x_7, x_3, x_19);
lean_dec(x_14);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_anyOfFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_mk_string_unchecked("anyOf: empty list", 17, 17);
x_5 = l_Lean_Parser_ParserState_mkError(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_apply_2(x_8, x_2, x_3);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_alloc_closure((void*)(l_Lean_Parser_anyOfFn), 3, 1);
lean_closure_set(x_12, 0, x_6);
x_13 = l_Lean_Parser_orelseFn(x_11, x_12, x_2, x_3);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkColEqFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 2);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 2);
lean_inc(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_ctor_get(x_7, 2);
lean_inc(x_8);
lean_dec(x_7);
lean_inc(x_8);
x_9 = l_Lean_FileMap_toPosition(x_8, x_6);
lean_dec(x_6);
x_10 = lean_ctor_get(x_3, 2);
lean_inc(x_10);
x_11 = l_Lean_FileMap_toPosition(x_8, x_10);
lean_dec(x_10);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
lean_dec(x_9);
x_14 = lean_nat_dec_eq(x_12, x_13);
lean_dec(x_13);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = l_Lean_Parser_ParserState_mkError(x_3, x_1);
return x_15;
}
else
{
lean_dec(x_1);
return x_3;
}
}
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_checkColEq_docString__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("checkColEq", 10, 10);
x_5 = l_Lean_Name_mkStr3(x_2, x_3, x_4);
x_6 = lean_mk_string_unchecked("The `colEq` parser ensures that the next token starts at exactly the column of the saved\nposition (see `withPosition`). This can be used to do whitespace sensitive syntax like\na `by` block or `do` block, where all the lines have to line up.\n\nThis parser has arity 0 - it does not capture anything. ", 298, 298);
x_7 = l_Lean_addBuiltinDocString(x_5, x_6, x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkColEq(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_epsilonInfo___lam__0___boxed), 1, 0);
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_epsilonInfo___lam__1___boxed), 1, 0);
x_4 = lean_box(1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_checkColEqFn), 3, 1);
lean_closure_set(x_6, 0, x_1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkColGeFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 2);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 2);
lean_inc(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_ctor_get(x_7, 2);
lean_inc(x_8);
lean_dec(x_7);
lean_inc(x_8);
x_9 = l_Lean_FileMap_toPosition(x_8, x_6);
lean_dec(x_6);
x_10 = lean_ctor_get(x_3, 2);
lean_inc(x_10);
x_11 = l_Lean_FileMap_toPosition(x_8, x_10);
lean_dec(x_10);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_nat_dec_le(x_12, x_13);
lean_dec(x_13);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = l_Lean_Parser_ParserState_mkError(x_3, x_1);
return x_15;
}
else
{
lean_dec(x_1);
return x_3;
}
}
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_checkColGe_docString__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("checkColGe", 10, 10);
x_5 = l_Lean_Name_mkStr3(x_2, x_3, x_4);
x_6 = lean_mk_string_unchecked("The `colGe` parser requires that the next token starts from at least the column of the saved\nposition (see `withPosition`), but allows it to be more indented.\nThis can be used for whitespace sensitive syntax to ensure that a block does not go outside a\ncertain indentation scope. For example it is used in the lean grammar for `else if`, to ensure\nthat the `else` is not less indented than the `if` it matches with.\n\nThis parser has arity 0 - it does not capture anything. ", 473, 473);
x_7 = l_Lean_addBuiltinDocString(x_5, x_6, x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkColGe(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_epsilonInfo___lam__0___boxed), 1, 0);
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_epsilonInfo___lam__1___boxed), 1, 0);
x_4 = lean_box(1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_checkColGeFn), 3, 1);
lean_closure_set(x_6, 0, x_1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkColGtFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 2);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 2);
lean_inc(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_ctor_get(x_7, 2);
lean_inc(x_8);
lean_dec(x_7);
lean_inc(x_8);
x_9 = l_Lean_FileMap_toPosition(x_8, x_6);
lean_dec(x_6);
x_10 = lean_ctor_get(x_3, 2);
lean_inc(x_10);
x_11 = l_Lean_FileMap_toPosition(x_8, x_10);
lean_dec(x_10);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_nat_dec_lt(x_12, x_13);
lean_dec(x_13);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = l_Lean_Parser_ParserState_mkError(x_3, x_1);
return x_15;
}
else
{
lean_dec(x_1);
return x_3;
}
}
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_checkColGt_docString__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("checkColGt", 10, 10);
x_5 = l_Lean_Name_mkStr3(x_2, x_3, x_4);
x_6 = lean_mk_string_unchecked("The `colGt` parser requires that the next token starts a strictly greater column than the saved\nposition (see `withPosition`). This can be used for whitespace sensitive syntax for the arguments\nto a tactic, to ensure that the following tactic is not interpreted as an argument.\n```\nexample (x : False) : False := by\n  revert x\n  exact id\n```\nHere, the `revert` tactic is followed by a list of `colGt ident`, because otherwise it would\ninterpret `exact` as an identifier and try to revert a variable named `exact`.\n\nThis parser has arity 0 - it does not capture anything. ", 571, 571);
x_7 = l_Lean_addBuiltinDocString(x_5, x_6, x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkColGt(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_epsilonInfo___lam__0___boxed), 1, 0);
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_epsilonInfo___lam__1___boxed), 1, 0);
x_4 = lean_box(1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_checkColGtFn), 3, 1);
lean_closure_set(x_6, 0, x_1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkLineEqFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 2);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 2);
lean_inc(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_ctor_get(x_7, 2);
lean_inc(x_8);
lean_dec(x_7);
lean_inc(x_8);
x_9 = l_Lean_FileMap_toPosition(x_8, x_6);
lean_dec(x_6);
x_10 = lean_ctor_get(x_3, 2);
lean_inc(x_10);
x_11 = l_Lean_FileMap_toPosition(x_8, x_10);
lean_dec(x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_ctor_get(x_9, 0);
lean_inc(x_13);
lean_dec(x_9);
x_14 = lean_nat_dec_eq(x_12, x_13);
lean_dec(x_13);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = l_Lean_Parser_ParserState_mkError(x_3, x_1);
return x_15;
}
else
{
lean_dec(x_1);
return x_3;
}
}
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_checkLineEq_docString__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("checkLineEq", 11, 11);
x_5 = l_Lean_Name_mkStr3(x_2, x_3, x_4);
x_6 = lean_mk_string_unchecked("The `lineEq` parser requires that the current token is on the same line as the saved position\n(see `withPosition`). This can be used to ensure that composite tokens are not \"broken up\" across\ndifferent lines. For example, `else if` is parsed using `lineEq` to ensure that the two tokens\nare on the same line.\n\nThis parser has arity 0 - it does not capture anything. ", 366, 366);
x_7 = l_Lean_addBuiltinDocString(x_5, x_6, x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkLineEq(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_epsilonInfo___lam__0___boxed), 1, 0);
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_epsilonInfo___lam__1___boxed), 1, 0);
x_4 = lean_box(1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_checkLineEqFn), 3, 1);
lean_closure_set(x_6, 0, x_1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_withPosition_docString__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("withPosition", 12, 12);
x_5 = l_Lean_Name_mkStr3(x_2, x_3, x_4);
x_6 = lean_mk_string_unchecked("`withPosition(p)` runs `p` while setting the \"saved position\" to the current position.\nThis has no effect on its own, but various other parsers access this position to achieve some\ncomposite effect:\n\n* `colGt`, `colGe`, `colEq` compare the column of the saved position to the current position,\n  used to implement Python-style indentation sensitive blocks\n* `lineEq` ensures that the current position is still on the same line as the saved position,\n  used to implement composite tokens\n\nThe saved position is only available in the read-only state, which is why this is a scoping parser:\nafter the `withPosition(..)` block the saved position will be restored to its original value.\n\nThis parser has the same arity as `p` - it just forwards the results of `p`. ", 760, 760);
x_7 = l_Lean_addBuiltinDocString(x_5, x_6, x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withPosition___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get_uint8(x_2, sizeof(void*)*4);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_ctor_get(x_2, 3);
lean_inc(x_8);
lean_inc(x_4);
lean_inc(x_3);
x_9 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_4);
lean_ctor_set(x_9, 2, x_7);
lean_ctor_set(x_9, 3, x_8);
lean_ctor_set_uint8(x_9, sizeof(void*)*4, x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withPosition___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
lean_inc(x_3);
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_withPosition___lam__0___boxed), 2, 1);
lean_closure_set(x_4, 0, x_3);
x_5 = l_Lean_Parser_adaptCacheableContextFn(x_4, x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withPosition(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_withPosition___lam__1), 3, 1);
lean_closure_set(x_4, 0, x_3);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withPosition___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_withPosition___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withPositionAfterLinebreak___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Parser_checkTailLinebreak(x_1);
if (x_4 == 0)
{
lean_inc(x_3);
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get_uint8(x_3, sizeof(void*)*4);
x_8 = lean_ctor_get(x_2, 2);
lean_inc(x_8);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_ctor_get(x_3, 3);
lean_inc(x_10);
lean_inc(x_6);
lean_inc(x_5);
x_11 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_6);
lean_ctor_set(x_11, 2, x_9);
lean_ctor_set(x_11, 3, x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*4, x_7);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withPositionAfterLinebreak___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = l_Lean_Parser_SyntaxStack_back(x_4);
lean_dec(x_4);
lean_inc(x_3);
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_withPositionAfterLinebreak___lam__0___boxed), 3, 2);
lean_closure_set(x_6, 0, x_5);
lean_closure_set(x_6, 1, x_3);
x_7 = l_Lean_Parser_adaptCacheableContextFn(x_6, x_1, x_2, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withPositionAfterLinebreak(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_withPositionAfterLinebreak___lam__1), 3, 1);
lean_closure_set(x_4, 0, x_3);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withPositionAfterLinebreak___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_withPositionAfterLinebreak___lam__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_withoutPosition_docString__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("withoutPosition", 15, 15);
x_5 = l_Lean_Name_mkStr3(x_2, x_3, x_4);
x_6 = lean_mk_string_unchecked("`withoutPosition(p)` runs `p` without the saved position, meaning that position-checking\nparsers like `colGt` will have no effect. This is usually used by bracketing constructs like\n`(...)` so that the user can locally override whitespace sensitivity.\n\nThis parser has the same arity as `p` - it just forwards the results of `p`. ", 330, 330);
x_7 = l_Lean_addBuiltinDocString(x_5, x_6, x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withoutPosition___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
x_5 = lean_box(0);
x_6 = lean_ctor_get(x_1, 3);
lean_inc(x_6);
lean_inc(x_3);
lean_inc(x_2);
x_7 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_3);
lean_ctor_set(x_7, 2, x_5);
lean_ctor_set(x_7, 3, x_6);
lean_ctor_set_uint8(x_7, sizeof(void*)*4, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withoutPosition(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_withoutPosition___lam__0___boxed), 1, 0);
x_3 = l_Lean_Parser_adaptCacheableContext(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withoutPosition___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_withoutPosition___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_withForbidden_docString__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("withForbidden", 13, 13);
x_5 = l_Lean_Name_mkStr3(x_2, x_3, x_4);
x_6 = lean_mk_string_unchecked("`withForbidden tk p` runs `p` with `tk` as a \"forbidden token\". This means that if the token\nappears anywhere in `p` (unless it is nested in `withoutForbidden`), parsing will immediately\nstop there, making `tk` effectively a lowest-precedence operator. This is used for parsers like\n`for x in arr do ...`: `arr` is parsed as `withForbidden \"do\" term` because otherwise `arr do ...`\nwould be treated as an application.\n\nThis parser has the same arity as `p` - it just forwards the results of `p`. ", 496, 496);
x_7 = l_Lean_addBuiltinDocString(x_5, x_6, x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withForbidden___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get_uint8(x_2, sizeof(void*)*4);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_1);
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_3);
x_8 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_4);
lean_ctor_set(x_8, 2, x_6);
lean_ctor_set(x_8, 3, x_7);
lean_ctor_set_uint8(x_8, sizeof(void*)*4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withForbidden(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_withForbidden___lam__0___boxed), 2, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = l_Lean_Parser_adaptCacheableContext(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withForbidden___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_withForbidden___lam__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_withoutForbidden_docString__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("withoutForbidden", 16, 16);
x_5 = l_Lean_Name_mkStr3(x_2, x_3, x_4);
x_6 = lean_mk_string_unchecked("`withoutForbidden(p)` runs `p` disabling the \"forbidden token\" (see `withForbidden`), if any.\nThis is usually used by bracketing constructs like `(...)` because there is no parsing ambiguity\ninside these nested constructs.\n\nThis parser has the same arity as `p` - it just forwards the results of `p`. ", 301, 301);
x_7 = l_Lean_addBuiltinDocString(x_5, x_6, x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withoutForbidden___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_box(0);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
x_7 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_3);
lean_ctor_set(x_7, 2, x_5);
lean_ctor_set(x_7, 3, x_6);
lean_ctor_set_uint8(x_7, sizeof(void*)*4, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withoutForbidden(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_withoutForbidden___lam__0___boxed), 1, 0);
x_3 = l_Lean_Parser_adaptCacheableContext(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withoutForbidden___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_withoutForbidden___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_eoiFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 2);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_string_utf8_at_end(x_5, x_3);
lean_dec(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_mk_string_unchecked("expected end of file", 20, 20);
x_8 = l_Lean_Parser_ParserState_mkError(x_2, x_7);
return x_8;
}
else
{
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_eoiFn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_eoiFn(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_eoi() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_epsilonInfo___lam__0___boxed), 1, 0);
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_epsilonInfo___lam__1___boxed), 1, 0);
x_3 = lean_box(1);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_eoiFn___boxed), 2, 0);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_insert___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_find___at___Lean_NameMap_contains_spec__0(lean_box(0), x_1, x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
x_7 = l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(x_1, x_2, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
lean_dec(x_4);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(x_1, x_2, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_insert(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_TokenMap_insert___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instInhabited(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instEmptyCollection(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instForInProdNameList(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_Lean_Name_quickCmp___boxed), 2, 0);
x_4 = l_Lean_RBMap_instForInProd(lean_box(0), lean_box(0), x_3, lean_box(0));
lean_dec(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedPrattParsingTables() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_1);
lean_ctor_set(x_3, 3, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_toCtorIdx(uint8_t x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Parser_LeadingIdentBehavior_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_noConfusion___redArg(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_OrElseOnAntiquotBehavior_noConfusion___redArg___lam__0___boxed), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_noConfusion(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_LeadingIdentBehavior_noConfusion___redArg(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_noConfusion___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lean_Parser_LeadingIdentBehavior_noConfusion___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_noConfusion___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_Lean_Parser_LeadingIdentBehavior_noConfusion(x_1, x_5, x_6, x_4);
return x_7;
}
}
static uint8_t _init_l_Lean_Parser_instInhabitedLeadingIdentBehavior() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = lean_box(0);
x_2 = lean_unbox(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Parser_Basic_0__Lean_Parser_beqLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8856_(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_Parser_LeadingIdentBehavior_toCtorIdx(x_1);
x_4 = l_Lean_Parser_LeadingIdentBehavior_toCtorIdx(x_2);
x_5 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_beqLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8856____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l___private_Lean_Parser_Basic_0__Lean_Parser_beqLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8856_(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Parser_instBEqLeadingIdentBehavior() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Parser_Basic_0__Lean_Parser_beqLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8856____boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8874_(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_12; lean_object* x_21; 
switch (x_1) {
case 0:
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_unsigned_to_nat(1024u);
x_31 = lean_nat_dec_le(x_30, x_2);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_unsigned_to_nat(2u);
x_33 = lean_nat_to_int(x_32);
x_3 = x_33;
goto block_11;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_nat_to_int(x_34);
x_3 = x_35;
goto block_11;
}
}
case 1:
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_unsigned_to_nat(1024u);
x_37 = lean_nat_dec_le(x_36, x_2);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_unsigned_to_nat(2u);
x_39 = lean_nat_to_int(x_38);
x_12 = x_39;
goto block_20;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_nat_to_int(x_40);
x_12 = x_41;
goto block_20;
}
}
default: 
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_unsigned_to_nat(1024u);
x_43 = lean_nat_dec_le(x_42, x_2);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_unsigned_to_nat(2u);
x_45 = lean_nat_to_int(x_44);
x_21 = x_45;
goto block_29;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_unsigned_to_nat(1u);
x_47 = lean_nat_to_int(x_46);
x_21 = x_47;
goto block_29;
}
}
}
block_11:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_4 = lean_mk_string_unchecked("Lean.Parser.LeadingIdentBehavior.default", 40, 40);
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
x_13 = lean_mk_string_unchecked("Lean.Parser.LeadingIdentBehavior.symbol", 39, 39);
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
block_29:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; 
x_22 = lean_mk_string_unchecked("Lean.Parser.LeadingIdentBehavior.both", 37, 37);
x_23 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_26, 0, x_24);
x_27 = lean_unbox(x_25);
lean_ctor_set_uint8(x_26, sizeof(void*)*1, x_27);
x_28 = l_Repr_addAppParen(x_26, x_2);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8874____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8874_(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_instReprLeadingIdentBehavior() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8874____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedParserCategory() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_1 = lean_box(0);
x_2 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_2);
x_4 = lean_box(0);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
lean_ctor_set(x_6, 2, x_4);
lean_ctor_set(x_6, 3, x_5);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_3);
lean_ctor_set(x_8, 2, x_6);
x_9 = lean_unbox(x_7);
lean_ctor_set_uint8(x_8, sizeof(void*)*3, x_9);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_indexed___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_find___at___Lean_NameMap_contains_spec__0(lean_box(0), x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
lean_dec(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_indexed___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Parser_peekToken(x_2, x_3);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_5, 1);
lean_dec(x_8);
x_9 = lean_ctor_get(x_5, 0);
lean_dec(x_9);
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
x_11 = lean_box(0);
lean_ctor_set(x_5, 1, x_11);
lean_ctor_set(x_5, 0, x_10);
return x_5;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_5);
x_12 = lean_ctor_get(x_6, 0);
lean_inc(x_12);
lean_dec(x_6);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_5);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_5, 0);
x_17 = lean_ctor_get(x_5, 1);
lean_dec(x_17);
x_18 = lean_ctor_get(x_6, 0);
lean_inc(x_18);
lean_dec(x_6);
switch (lean_obj_tag(x_18)) {
case 0:
{
lean_object* x_23; 
x_23 = lean_box(0);
lean_ctor_set(x_5, 1, x_23);
return x_5;
}
case 1:
{
lean_object* x_24; lean_object* x_25; 
lean_free_object(x_5);
x_24 = lean_ctor_get(x_18, 1);
lean_inc(x_24);
lean_dec(x_18);
x_25 = l_Lean_Parser_indexed___redArg___lam__0(x_1, x_16, x_24);
lean_dec(x_24);
return x_25;
}
case 2:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_free_object(x_5);
x_26 = lean_ctor_get(x_18, 1);
lean_inc(x_26);
lean_dec(x_18);
x_27 = lean_box(0);
x_28 = l_Lean_Name_str___override(x_27, x_26);
x_29 = l_Lean_Parser_indexed___redArg___lam__0(x_1, x_16, x_28);
lean_dec(x_28);
return x_29;
}
default: 
{
switch (x_4) {
case 0:
{
lean_dec(x_18);
lean_free_object(x_5);
goto block_22;
}
case 1:
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_18, 2);
lean_inc(x_30);
lean_dec(x_18);
x_31 = l_Lean_RBNode_find___at___Lean_NameMap_contains_spec__0(lean_box(0), x_1, x_30);
lean_dec(x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_free_object(x_5);
goto block_22;
}
else
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec(x_31);
lean_ctor_set(x_5, 1, x_32);
return x_5;
}
}
default: 
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_18, 2);
lean_inc(x_33);
lean_dec(x_18);
x_34 = l_Lean_RBNode_find___at___Lean_NameMap_contains_spec__0(lean_box(0), x_1, x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_dec(x_33);
lean_free_object(x_5);
goto block_22;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_mk_string_unchecked("ident", 5, 5);
x_37 = l_Lean_Name_mkStr1(x_36);
x_38 = lean_name_eq(x_33, x_37);
lean_dec(x_33);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = l_Lean_RBNode_find___at___Lean_NameMap_contains_spec__0(lean_box(0), x_1, x_37);
lean_dec(x_37);
if (lean_obj_tag(x_39) == 0)
{
lean_ctor_set(x_5, 1, x_35);
return x_5;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec(x_39);
x_41 = l_List_appendTR(lean_box(0), x_35, x_40);
lean_ctor_set(x_5, 1, x_41);
return x_5;
}
}
else
{
lean_dec(x_37);
lean_ctor_set(x_5, 1, x_35);
return x_5;
}
}
}
}
}
}
block_22:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_mk_string_unchecked("ident", 5, 5);
x_20 = l_Lean_Name_mkStr1(x_19);
x_21 = l_Lean_Parser_indexed___redArg___lam__0(x_1, x_16, x_20);
lean_dec(x_20);
return x_21;
}
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_5, 0);
lean_inc(x_42);
lean_dec(x_5);
x_43 = lean_ctor_get(x_6, 0);
lean_inc(x_43);
lean_dec(x_6);
switch (lean_obj_tag(x_43)) {
case 0:
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_box(0);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_42);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
case 1:
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_43, 1);
lean_inc(x_50);
lean_dec(x_43);
x_51 = l_Lean_Parser_indexed___redArg___lam__0(x_1, x_42, x_50);
lean_dec(x_50);
return x_51;
}
case 2:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_43, 1);
lean_inc(x_52);
lean_dec(x_43);
x_53 = lean_box(0);
x_54 = l_Lean_Name_str___override(x_53, x_52);
x_55 = l_Lean_Parser_indexed___redArg___lam__0(x_1, x_42, x_54);
lean_dec(x_54);
return x_55;
}
default: 
{
switch (x_4) {
case 0:
{
lean_dec(x_43);
goto block_47;
}
case 1:
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_43, 2);
lean_inc(x_56);
lean_dec(x_43);
x_57 = l_Lean_RBNode_find___at___Lean_NameMap_contains_spec__0(lean_box(0), x_1, x_56);
lean_dec(x_56);
if (lean_obj_tag(x_57) == 0)
{
goto block_47;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
lean_dec(x_57);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_42);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
default: 
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_43, 2);
lean_inc(x_60);
lean_dec(x_43);
x_61 = l_Lean_RBNode_find___at___Lean_NameMap_contains_spec__0(lean_box(0), x_1, x_60);
if (lean_obj_tag(x_61) == 0)
{
lean_dec(x_60);
goto block_47;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
lean_dec(x_61);
x_63 = lean_mk_string_unchecked("ident", 5, 5);
x_64 = l_Lean_Name_mkStr1(x_63);
x_65 = lean_name_eq(x_60, x_64);
lean_dec(x_60);
if (x_65 == 0)
{
lean_object* x_66; 
x_66 = l_Lean_RBNode_find___at___Lean_NameMap_contains_spec__0(lean_box(0), x_1, x_64);
lean_dec(x_64);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; 
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_42);
lean_ctor_set(x_67, 1, x_62);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_66, 0);
lean_inc(x_68);
lean_dec(x_66);
x_69 = l_List_appendTR(lean_box(0), x_62, x_68);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_42);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
else
{
lean_object* x_71; 
lean_dec(x_64);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_42);
lean_ctor_set(x_71, 1, x_62);
return x_71;
}
}
}
}
}
}
block_47:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_mk_string_unchecked("ident", 5, 5);
x_45 = l_Lean_Name_mkStr1(x_44);
x_46 = l_Lean_Parser_indexed___redArg___lam__0(x_1, x_42, x_45);
lean_dec(x_45);
return x_46;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_indexed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_indexed___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_indexed___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_indexed___redArg___lam__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_indexed___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_4);
lean_dec(x_4);
x_6 = l_Lean_Parser_indexed___redArg(x_1, x_2, x_3, x_5);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_indexed___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_5);
lean_dec(x_5);
x_7 = l_Lean_Parser_indexed(x_1, x_2, x_3, x_4, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initFn___lam__0____x40_Lean_Parser_Basic___hyg_9337_(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_whitespace(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_9337_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_initFn___lam__0____x40_Lean_Parser_Basic___hyg_9337____boxed), 3, 0);
x_3 = lean_st_mk_ref(x_2, x_1);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initFn___lam__0____x40_Lean_Parser_Basic___hyg_9337____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_initFn___lam__0____x40_Lean_Parser_Basic___hyg_9337_(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initFn___lam__0____x40_Lean_Parser_Basic___hyg_9363_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_st_ref_get(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_9363_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_2 = l_Lean_Parser_categoryParserFnRef;
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_initFn___lam__0____x40_Lean_Parser_Basic___hyg_9363____boxed), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = lean_box(0);
x_5 = lean_box(2);
x_6 = lean_unbox(x_5);
x_7 = l_Lean_registerEnvExtension___redArg(x_3, x_4, x_6, x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initFn___lam__0____x40_Lean_Parser_Basic___hyg_9363____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_initFn___lam__0____x40_Lean_Parser_Basic___hyg_9363_(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParserFn___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_inc(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParserFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_categoryParserFn___lam__0___boxed), 3, 0);
x_5 = l_Pi_instInhabited___redArg(x_4);
x_6 = l_Lean_Parser_categoryParserFnExtension;
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get_uint8(x_6, sizeof(void*)*3);
x_10 = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(x_5, x_6, x_8, x_9);
x_11 = lean_apply_3(x_10, x_1, x_2, x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParserFn___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_categoryParserFn___lam__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParser___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_ctor_get_uint8(x_2, sizeof(void*)*4);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_ctor_get(x_2, 3);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_7 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_3);
lean_ctor_set(x_7, 2, x_5);
lean_ctor_set(x_7, 3, x_6);
lean_ctor_set_uint8(x_7, sizeof(void*)*4, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParser(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_categoryParser___lam__0___boxed), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_epsilonInfo___lam__0___boxed), 1, 0);
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_epsilonInfo___lam__1___boxed), 1, 0);
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set(x_7, 2, x_6);
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_Parser_categoryParserFn), 3, 1);
lean_closure_set(x_8, 0, x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_Parser_withCacheFn), 4, 2);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_adaptCacheableContextFn), 4, 2);
lean_closure_set(x_10, 0, x_3);
lean_closure_set(x_10, 1, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParser___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_categoryParser___lam__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_termParser(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_mk_string_unchecked("term", 4, 4);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = l_Lean_Parser_categoryParser(x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("checkNoImmediateColon", 21, 21);
x_5 = l_Lean_Name_mkStr3(x_2, x_3, x_4);
x_6 = lean_mk_string_unchecked("Fail if previous token is immediately followed by ':'. ", 55, 55);
x_7 = l_Lean_addBuiltinDocString(x_5, x_6, x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoImmediateColon___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = l_Lean_Parser_SyntaxStack_back(x_3);
lean_dec(x_3);
x_5 = l_Lean_Parser_checkTailNoWs(x_4);
lean_dec(x_4);
if (x_5 == 0)
{
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_6, 0);
x_8 = lean_ctor_get(x_2, 2);
lean_inc(x_8);
x_9 = lean_string_utf8_at_end(x_7, x_8);
if (x_9 == 0)
{
uint32_t x_10; lean_object* x_11; uint32_t x_12; uint8_t x_13; 
x_10 = lean_string_utf8_get_fast(x_7, x_8);
lean_dec(x_8);
x_11 = lean_unsigned_to_nat(58u);
x_12 = l_Char_ofNat(x_11);
x_13 = l_instDecidableEqChar(x_10, x_12);
if (x_13 == 0)
{
return x_2;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_mk_string_unchecked("unexpected ':'", 14, 14);
x_15 = lean_box(0);
x_16 = l_Lean_Parser_ParserState_mkUnexpectedError(x_2, x_14, x_15, x_13);
return x_16;
}
}
else
{
lean_dec(x_8);
return x_2;
}
}
}
}
static lean_object* _init_l_Lean_Parser_checkNoImmediateColon() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_checkNoImmediateColon___lam__0___boxed), 2, 0);
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_epsilonInfo___lam__0___boxed), 1, 0);
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_epsilonInfo___lam__1___boxed), 1, 0);
x_4 = lean_box(1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoImmediateColon___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_checkNoImmediateColon___lam__0(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_setExpectedFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_apply_2(x_2, x_3, x_4);
x_6 = lean_ctor_get(x_5, 4);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_dec(x_1);
return x_5;
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_5, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_5, 3);
lean_inc(x_12);
x_13 = lean_ctor_get(x_8, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
lean_dec(x_8);
x_15 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set(x_15, 2, x_1);
lean_ctor_set(x_6, 0, x_15);
x_16 = !lean_is_exclusive(x_5);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_5, 4);
lean_dec(x_17);
x_18 = lean_ctor_get(x_5, 3);
lean_dec(x_18);
x_19 = lean_ctor_get(x_5, 2);
lean_dec(x_19);
x_20 = lean_ctor_get(x_5, 1);
lean_dec(x_20);
x_21 = lean_ctor_get(x_5, 0);
lean_dec(x_21);
return x_5;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_5, 5);
lean_inc(x_22);
lean_dec(x_5);
x_23 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_23, 0, x_9);
lean_ctor_set(x_23, 1, x_10);
lean_ctor_set(x_23, 2, x_11);
lean_ctor_set(x_23, 3, x_12);
lean_ctor_set(x_23, 4, x_6);
lean_ctor_set(x_23, 5, x_22);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_24 = lean_ctor_get(x_6, 0);
lean_inc(x_24);
lean_dec(x_6);
x_25 = lean_ctor_get(x_5, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_5, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_5, 2);
lean_inc(x_27);
x_28 = lean_ctor_get(x_5, 3);
lean_inc(x_28);
x_29 = lean_ctor_get(x_24, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_24, 1);
lean_inc(x_30);
lean_dec(x_24);
x_31 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_31, 2, x_1);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = lean_ctor_get(x_5, 5);
lean_inc(x_33);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 lean_ctor_release(x_5, 2);
 lean_ctor_release(x_5, 3);
 lean_ctor_release(x_5, 4);
 lean_ctor_release(x_5, 5);
 x_34 = x_5;
} else {
 lean_dec_ref(x_5);
 x_34 = lean_box(0);
}
if (lean_is_scalar(x_34)) {
 x_35 = lean_alloc_ctor(0, 6, 0);
} else {
 x_35 = x_34;
}
lean_ctor_set(x_35, 0, x_25);
lean_ctor_set(x_35, 1, x_26);
lean_ctor_set(x_35, 2, x_27);
lean_ctor_set(x_35, 3, x_28);
lean_ctor_set(x_35, 4, x_32);
lean_ctor_set(x_35, 5, x_33);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_setExpected(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_setExpectedFn), 4, 2);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_pushNone___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = l_Array_empty(lean_box(0));
x_4 = lean_mk_string_unchecked("null", 4, 4);
x_5 = l_Lean_Name_mkStr1(x_4);
x_6 = lean_box(2);
x_7 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set(x_7, 2, x_3);
x_8 = l_Lean_Parser_ParserState_pushSyntax(x_2, x_7);
return x_8;
}
}
static lean_object* _init_l_Lean_Parser_pushNone() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_pushNone___lam__0___boxed), 2, 0);
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_epsilonInfo___lam__0___boxed), 1, 0);
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_epsilonInfo___lam__1___boxed), 1, 0);
x_4 = lean_box(1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_pushNone___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_pushNone___lam__0(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_1 = lean_mk_string_unchecked("antiquotNestedExpr", 18, 18);
x_2 = l_Lean_Name_mkStr1(x_1);
x_3 = lean_mk_string_unchecked("(", 1, 1);
x_4 = l_Lean_Parser_symbolNoAntiquot(x_3);
lean_dec(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Lean_Parser_termParser(x_5);
x_7 = l_Lean_Parser_decQuotDepth(x_6);
x_8 = lean_mk_string_unchecked(")", 1, 1);
x_9 = l_Lean_Parser_symbolNoAntiquot(x_8);
lean_dec(x_8);
x_10 = l_Lean_Parser_andthen(x_7, x_9);
x_11 = l_Lean_Parser_andthen(x_4, x_10);
x_12 = l_Lean_Parser_node(x_2, x_11);
return x_12;
}
}
static lean_object* _init_l_Lean_Parser_antiquotExpr() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Parser_identNoAntiquot;
x_2 = lean_mk_string_unchecked("_", 1, 1);
x_3 = l_Lean_Parser_symbolNoAntiquot(x_2);
lean_dec(x_2);
x_4 = l_Lean_Parser_antiquotNestedExpr;
x_5 = l_Lean_Parser_orelse(x_3, x_4);
x_6 = l_Lean_Parser_orelse(x_1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_tokenAntiquotFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_2, 4);
lean_inc(x_3);
x_4 = lean_box(0);
x_5 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at___Lean_Parser_ParserState_mkNode_spec__0(x_3, x_4);
if (x_5 == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_6 = l_Lean_Parser_ParserState_stackSize(x_2);
x_7 = lean_mk_string_unchecked("no space before", 15, 15);
x_8 = l_Lean_Parser_checkNoWsBefore(x_7);
x_9 = lean_mk_string_unchecked("%", 1, 1);
x_10 = l_Lean_Parser_symbolNoAntiquot(x_9);
lean_dec(x_9);
x_11 = lean_mk_string_unchecked("$", 1, 1);
x_12 = l_Lean_Parser_symbolNoAntiquot(x_11);
lean_dec(x_11);
x_13 = l_Lean_Parser_antiquotExpr;
lean_inc(x_8);
x_14 = l_Lean_Parser_andthen(x_8, x_13);
x_15 = l_Lean_Parser_andthen(x_12, x_14);
x_16 = l_Lean_Parser_andthen(x_10, x_15);
x_17 = l_Lean_Parser_andthen(x_8, x_16);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
lean_inc(x_2);
x_19 = lean_apply_2(x_18, x_1, x_2);
x_20 = lean_ctor_get(x_19, 4);
lean_inc(x_20);
x_21 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at___Lean_Parser_ParserState_mkNode_spec__0(x_20, x_4);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_2, 2);
lean_inc(x_22);
lean_dec(x_2);
x_23 = l_Lean_Parser_ParserState_restore(x_19, x_6, x_22);
lean_dec(x_6);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_2);
x_24 = lean_mk_string_unchecked("token_antiquot", 14, 14);
x_25 = l_Lean_Name_mkStr1(x_24);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_sub(x_6, x_26);
lean_dec(x_6);
x_28 = l_Lean_Parser_ParserState_mkNode(x_19, x_25, x_27);
lean_dec(x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_tokenWithAntiquot___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint32_t x_8; lean_object* x_9; uint32_t x_10; uint8_t x_11; 
lean_inc(x_2);
x_4 = lean_apply_2(x_1, x_2, x_3);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_4, 2);
lean_inc(x_7);
x_8 = lean_string_utf8_get(x_6, x_7);
lean_dec(x_7);
lean_dec(x_6);
x_9 = lean_unsigned_to_nat(37u);
x_10 = l_Char_ofNat(x_9);
x_11 = l_instDecidableEqChar(x_8, x_10);
if (x_11 == 0)
{
lean_dec(x_2);
return x_4;
}
else
{
lean_object* x_12; 
x_12 = l_Lean_Parser_tokenAntiquotFn(x_2, x_4);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_tokenWithAntiquot(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_tokenWithAntiquot___lam__0), 3, 1);
lean_closure_set(x_4, 0, x_3);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_symbol(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Parser_symbolNoAntiquot(x_1);
x_3 = l_Lean_Parser_tokenWithAntiquot(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_symbol___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_symbol(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_instCoeStringParser() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_symbol___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbol(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Parser_nonReservedSymbolNoAntiquot(x_1, x_2);
x_4 = l_Lean_Parser_tokenWithAntiquot(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbol___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l_Lean_Parser_nonReservedSymbol(x_1, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbol(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Parser_unicodeSymbolNoAntiquot(x_1, x_2);
x_4 = l_Lean_Parser_tokenWithAntiquot(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbol___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_unicodeSymbol(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_mkAntiquot_docString__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("mkAntiquot", 10, 10);
x_5 = l_Lean_Name_mkStr3(x_2, x_3, x_4);
x_6 = lean_mk_string_unchecked("Define parser for `$e` (if `anonymous == true`) and `$e:name`.\n`kind` is embedded in the antiquotation's kind, and checked at syntax `match` unless `isPseudoKind` is true.\nAntiquotations can be escaped as in `$$e`, which produces the syntax tree for `$e`. ", 256, 256);
x_7 = l_Lean_addBuiltinDocString(x_5, x_6, x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_26; lean_object* x_27; 
if (x_4 == 0)
{
lean_object* x_52; 
x_52 = lean_box(0);
x_26 = x_3;
x_27 = x_52;
goto block_51;
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_mk_string_unchecked("pseudo", 6, 6);
x_54 = l_Lean_Name_mkStr1(x_53);
x_26 = x_3;
x_27 = x_54;
goto block_51;
}
block_25:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_7 = lean_unsigned_to_nat(1024u);
x_8 = lean_box(0);
x_9 = lean_mk_string_unchecked("$", 1, 1);
x_10 = l_Lean_Parser_symbol(x_9);
lean_dec(x_9);
lean_inc(x_10);
x_11 = l_Lean_Parser_setExpected(x_8, x_10);
x_12 = lean_mk_string_unchecked("", 0, 0);
x_13 = l_Lean_Parser_checkNoWsBefore(x_12);
x_14 = l_Lean_Parser_andthen(x_13, x_10);
x_15 = l_Lean_Parser_manyNoAntiquot(x_14);
x_16 = lean_mk_string_unchecked("no space before spliced term", 28, 28);
x_17 = l_Lean_Parser_checkNoWsBefore(x_16);
x_18 = l_Lean_Parser_antiquotExpr;
x_19 = l_Lean_Parser_andthen(x_18, x_6);
x_20 = l_Lean_Parser_andthen(x_17, x_19);
x_21 = l_Lean_Parser_andthen(x_15, x_20);
x_22 = l_Lean_Parser_andthen(x_11, x_21);
x_23 = l_Lean_Parser_atomic(x_22);
x_24 = l_Lean_Parser_leadingNode(x_5, x_7, x_23);
return x_24;
}
block_51:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_28 = l_Lean_Name_append(x_2, x_27);
x_29 = lean_mk_string_unchecked("antiquot", 8, 8);
x_30 = l_Lean_Name_mkStr1(x_29);
x_31 = l_Lean_Name_append(x_28, x_30);
x_32 = lean_mk_string_unchecked("antiquotName", 12, 12);
x_33 = l_Lean_Name_mkStr1(x_32);
x_34 = lean_mk_string_unchecked("no space before ':", 18, 18);
x_35 = lean_string_append(x_34, x_1);
x_36 = lean_mk_string_unchecked("'", 1, 1);
x_37 = lean_string_append(x_35, x_36);
lean_dec(x_36);
x_38 = l_Lean_Parser_checkNoWsBefore(x_37);
x_39 = lean_mk_string_unchecked(":", 1, 1);
x_40 = l_Lean_Parser_symbol(x_39);
lean_dec(x_39);
x_41 = lean_box(0);
x_42 = lean_unbox(x_41);
x_43 = l_Lean_Parser_nonReservedSymbol(x_1, x_42);
x_44 = l_Lean_Parser_andthen(x_40, x_43);
x_45 = l_Lean_Parser_andthen(x_38, x_44);
x_46 = l_Lean_Parser_node(x_33, x_45);
if (x_26 == 0)
{
x_5 = x_31;
x_6 = x_46;
goto block_25;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_47 = l_Lean_Parser_checkNoImmediateColon;
x_48 = l_Lean_Parser_pushNone;
x_49 = l_Lean_Parser_andthen(x_47, x_48);
x_50 = l_Lean_Parser_orelse(x_46, x_49);
x_5 = x_31;
x_6 = x_50;
goto block_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_3);
lean_dec(x_3);
x_6 = lean_unbox(x_4);
lean_dec(x_4);
x_7 = l_Lean_Parser_mkAntiquot(x_1, x_2, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotFn(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint32_t x_9; lean_object* x_10; uint32_t x_11; uint8_t x_12; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_ctor_get(x_5, 2);
lean_inc(x_8);
x_9 = lean_string_utf8_get(x_7, x_8);
lean_dec(x_8);
lean_dec(x_7);
x_10 = lean_unsigned_to_nat(36u);
x_11 = l_Char_ofNat(x_10);
x_12 = l_instDecidableEqChar(x_9, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_1);
x_13 = lean_apply_2(x_2, x_4, x_5);
return x_13;
}
else
{
if (x_3 == 0)
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_box(1);
x_15 = lean_unbox(x_14);
x_16 = l_Lean_Parser_orelseFnCore(x_1, x_2, x_15, x_4, x_5);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_17 = lean_box(0);
x_18 = lean_unbox(x_17);
x_19 = l_Lean_Parser_orelseFnCore(x_1, x_2, x_18, x_4, x_5);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_Lean_Parser_withAntiquotFn(x_1, x_2, x_6, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_withAntiquot_docString__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("withAntiquot", 12, 12);
x_5 = l_Lean_Name_mkStr3(x_2, x_3, x_4);
x_6 = lean_mk_string_unchecked("Optimized version of `mkAntiquot ... <|> p`. ", 45, 45);
x_7 = l_Lean_addBuiltinDocString(x_5, x_6, x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquot(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = l_Lean_Parser_orelseInfo(x_3, x_4);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_box(0);
x_9 = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotFn___boxed), 5, 3);
lean_closure_set(x_9, 0, x_6);
lean_closure_set(x_9, 1, x_7);
lean_closure_set(x_9, 2, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withoutInfo(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_epsilonInfo___lam__0___boxed), 1, 0);
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_epsilonInfo___lam__1___boxed), 1, 0);
x_4 = lean_box(1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withoutInfo___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_withoutInfo(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("mkAntiquotSplice", 16, 16);
x_5 = l_Lean_Name_mkStr3(x_2, x_3, x_4);
x_6 = lean_mk_string_unchecked("Parse `$[p]suffix`, e.g. `$[p],*`. ", 35, 35);
x_7 = l_Lean_addBuiltinDocString(x_5, x_6, x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquotSplice(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_4 = lean_mk_string_unchecked("antiquot_scope", 14, 14);
x_5 = l_Lean_Name_mkStr1(x_4);
x_6 = l_Lean_Name_append(x_1, x_5);
x_7 = lean_unsigned_to_nat(1024u);
x_8 = lean_box(0);
x_9 = lean_mk_string_unchecked("$", 1, 1);
x_10 = l_Lean_Parser_symbol(x_9);
lean_dec(x_9);
lean_inc(x_10);
x_11 = l_Lean_Parser_setExpected(x_8, x_10);
x_12 = lean_mk_string_unchecked("", 0, 0);
x_13 = l_Lean_Parser_checkNoWsBefore(x_12);
x_14 = l_Lean_Parser_andthen(x_13, x_10);
x_15 = l_Lean_Parser_manyNoAntiquot(x_14);
x_16 = lean_mk_string_unchecked("no space before spliced term", 28, 28);
x_17 = l_Lean_Parser_checkNoWsBefore(x_16);
x_18 = lean_mk_string_unchecked("[", 1, 1);
x_19 = l_Lean_Parser_symbol(x_18);
lean_dec(x_18);
x_20 = lean_mk_string_unchecked("null", 4, 4);
x_21 = l_Lean_Name_mkStr1(x_20);
x_22 = l_Lean_Parser_node(x_21, x_2);
x_23 = lean_mk_string_unchecked("]", 1, 1);
x_24 = l_Lean_Parser_symbol(x_23);
lean_dec(x_23);
x_25 = l_Lean_Parser_andthen(x_24, x_3);
x_26 = l_Lean_Parser_andthen(x_22, x_25);
x_27 = l_Lean_Parser_andthen(x_19, x_26);
x_28 = l_Lean_Parser_andthen(x_17, x_27);
x_29 = l_Lean_Parser_andthen(x_15, x_28);
x_30 = l_Lean_Parser_andthen(x_11, x_29);
x_31 = l_Lean_Parser_atomic(x_30);
x_32 = l_Lean_Parser_leadingNode(x_6, x_7, x_31);
return x_32;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSpliceFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
lean_inc(x_4);
x_5 = lean_apply_2(x_2, x_3, x_4);
x_6 = lean_ctor_get(x_5, 4);
lean_inc(x_6);
x_7 = lean_box(0);
x_8 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at___Lean_Parser_ParserState_mkNode_spec__0(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_1);
x_9 = l_Lean_Parser_ParserState_stackSize(x_4);
x_10 = lean_ctor_get(x_4, 2);
lean_inc(x_10);
lean_dec(x_4);
x_11 = l_Lean_Parser_ParserState_restore(x_5, x_9, x_10);
lean_dec(x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_4);
x_12 = lean_mk_string_unchecked("antiquot_suffix_splice", 22, 22);
x_13 = l_Lean_Name_mkStr1(x_12);
x_14 = l_Lean_Name_append(x_1, x_13);
x_15 = lean_ctor_get(x_5, 0);
lean_inc(x_15);
x_16 = l_Lean_Parser_SyntaxStack_size(x_15);
lean_dec(x_15);
x_17 = lean_unsigned_to_nat(2u);
x_18 = lean_nat_sub(x_16, x_17);
lean_dec(x_16);
x_19 = l_Lean_Parser_ParserState_mkNode(x_5, x_14, x_18);
lean_dec(x_18);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("withAntiquotSuffixSplice", 24, 24);
x_5 = l_Lean_Name_mkStr3(x_2, x_3, x_4);
x_6 = lean_mk_string_unchecked("Parse `suffix` after an antiquotation, e.g. `$x,*`, and put both into a new node. ", 82, 82);
x_7 = l_Lean_addBuiltinDocString(x_5, x_6, x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotSuffixSplice___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
lean_inc(x_4);
x_7 = lean_apply_2(x_6, x_4, x_5);
x_8 = lean_ctor_get(x_7, 4);
lean_inc(x_8);
x_9 = lean_box(0);
x_10 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at___Lean_Parser_ParserState_mkNode_spec__0(x_8, x_9);
if (x_10 == 0)
{
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
x_12 = l_Lean_Parser_SyntaxStack_back(x_11);
lean_dec(x_11);
x_13 = l_Lean_Syntax_isAntiquots(x_12);
if (x_13 == 0)
{
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_14);
lean_dec(x_2);
x_15 = l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSpliceFn(x_3, x_14, x_4, x_7);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotSuffixSplice(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_inc(x_3);
lean_inc(x_2);
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotSuffixSplice___lam__0), 5, 3);
lean_closure_set(x_4, 0, x_2);
lean_closure_set(x_4, 1, x_3);
lean_closure_set(x_4, 2, x_1);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
lean_dec(x_3);
x_7 = l_Lean_Parser_andthenInfo(x_5, x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotSpliceAndSuffix(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = l_Lean_Parser_withoutInfo(x_2);
lean_inc(x_3);
lean_inc(x_1);
x_5 = l_Lean_Parser_mkAntiquotSplice(x_1, x_4, x_3);
x_6 = l_Lean_Parser_withAntiquotSuffixSplice(x_1, x_2, x_3);
x_7 = l_Lean_Parser_withAntiquot(x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nodeWithAntiquot(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_box(0);
x_6 = lean_unbox(x_5);
lean_inc(x_2);
x_7 = l_Lean_Parser_mkAntiquot(x_1, x_2, x_4, x_6);
x_8 = l_Lean_Parser_node(x_2, x_3);
x_9 = l_Lean_Parser_withAntiquot(x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nodeWithAntiquot___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_4);
lean_dec(x_4);
x_6 = l_Lean_Parser_nodeWithAntiquot(x_1, x_2, x_3, x_5);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepByElemParser(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_3 = lean_mk_string_unchecked("sepBy", 5, 5);
x_4 = l_Lean_Name_mkStr1(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_string_utf8_byte_size(x_2);
x_7 = l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(x_2, x_6, x_5);
x_8 = l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(x_2, x_7, x_6);
x_9 = lean_string_utf8_extract(x_2, x_7, x_8);
lean_dec(x_8);
lean_dec(x_7);
x_10 = lean_mk_string_unchecked("*", 1, 1);
x_11 = lean_string_append(x_9, x_10);
lean_dec(x_10);
x_12 = l_Lean_Parser_symbol(x_11);
lean_dec(x_11);
x_13 = l_Lean_Parser_withAntiquotSpliceAndSuffix(x_4, x_1, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepByElemParser___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_sepByElemParser(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Parser_sepByElemParser(x_1, x_2);
x_6 = l_Lean_Parser_sepByNoAntiquot(x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_4);
lean_dec(x_4);
x_6 = l_Lean_Parser_sepBy(x_1, x_2, x_3, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Parser_sepByElemParser(x_1, x_2);
x_6 = l_Lean_Parser_sepBy1NoAntiquot(x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_4);
lean_dec(x_4);
x_6 = l_Lean_Parser_sepBy1(x_1, x_2, x_3, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_mkResult(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = l_Lean_Parser_ParserState_stackSize(x_1);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_add(x_2, x_4);
x_6 = lean_nat_dec_eq(x_3, x_5);
lean_dec(x_5);
lean_dec(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_mk_string_unchecked("null", 4, 4);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = l_Lean_Parser_ParserState_mkNode(x_1, x_8, x_2);
return x_9;
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_mkResult___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Parser_Basic_0__Lean_Parser_mkResult(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_leadingParserAux(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_7 = l_Lean_Parser_indexed___redArg(x_6, x_4, x_5, x_3);
lean_dec(x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_ctor_get(x_9, 4);
lean_inc(x_11);
x_12 = lean_box(0);
x_13 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at___Lean_Parser_ParserState_mkNode_spec__0(x_11, x_12);
if (x_13 == 0)
{
lean_free_object(x_7);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_14);
lean_dec(x_2);
x_15 = l_List_appendTR(lean_box(0), x_14, x_10);
x_16 = l_List_isEmpty___redArg(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_free_object(x_7);
lean_dec(x_1);
x_17 = l_Lean_Parser_ParserState_stackSize(x_5);
lean_dec(x_5);
x_18 = lean_box(0);
x_19 = l_Lean_Parser_longestMatchFn(x_18, x_15, x_4, x_9);
x_20 = l___private_Lean_Parser_Basic_0__Lean_Parser_mkResult(x_19, x_17);
lean_dec(x_17);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_29; uint8_t x_30; 
lean_dec(x_15);
lean_dec(x_5);
x_21 = lean_box(0);
x_22 = lean_alloc_closure((void*)(l_Lean_Parser_identEqFn___lam__0___boxed), 2, 1);
lean_closure_set(x_22, 0, x_21);
x_23 = l_Lean_Name_toString(x_1, x_16, x_22);
x_24 = lean_box(0);
lean_inc(x_23);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 1, x_24);
lean_ctor_set(x_7, 0, x_23);
x_25 = l_Lean_Parser_tokenFn(x_7, x_4, x_9);
x_29 = lean_ctor_get(x_25, 4);
lean_inc(x_29);
x_30 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at___Lean_Parser_ParserState_mkNode_spec__0(x_29, x_12);
if (x_30 == 0)
{
if (x_16 == 0)
{
goto block_28;
}
else
{
lean_dec(x_23);
return x_25;
}
}
else
{
goto block_28;
}
block_28:
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_unsigned_to_nat(0u);
x_27 = l_Lean_Parser_ParserState_mkUnexpectedTokenError(x_25, x_23, x_26);
lean_dec(x_25);
return x_27;
}
}
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_31 = lean_ctor_get(x_7, 0);
x_32 = lean_ctor_get(x_7, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_7);
x_33 = lean_ctor_get(x_31, 4);
lean_inc(x_33);
x_34 = lean_box(0);
x_35 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at___Lean_Parser_ParserState_mkNode_spec__0(x_33, x_34);
if (x_35 == 0)
{
lean_dec(x_32);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_31;
}
else
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = lean_ctor_get(x_2, 1);
lean_inc(x_36);
lean_dec(x_2);
x_37 = l_List_appendTR(lean_box(0), x_36, x_32);
x_38 = l_List_isEmpty___redArg(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_1);
x_39 = l_Lean_Parser_ParserState_stackSize(x_5);
lean_dec(x_5);
x_40 = lean_box(0);
x_41 = l_Lean_Parser_longestMatchFn(x_40, x_37, x_4, x_31);
x_42 = l___private_Lean_Parser_Basic_0__Lean_Parser_mkResult(x_41, x_39);
lean_dec(x_39);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_52; uint8_t x_53; 
lean_dec(x_37);
lean_dec(x_5);
x_43 = lean_box(0);
x_44 = lean_alloc_closure((void*)(l_Lean_Parser_identEqFn___lam__0___boxed), 2, 1);
lean_closure_set(x_44, 0, x_43);
x_45 = l_Lean_Name_toString(x_1, x_38, x_44);
x_46 = lean_box(0);
lean_inc(x_45);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = l_Lean_Parser_tokenFn(x_47, x_4, x_31);
x_52 = lean_ctor_get(x_48, 4);
lean_inc(x_52);
x_53 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at___Lean_Parser_ParserState_mkNode_spec__0(x_52, x_34);
if (x_53 == 0)
{
if (x_38 == 0)
{
goto block_51;
}
else
{
lean_dec(x_45);
return x_48;
}
}
else
{
goto block_51;
}
block_51:
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_unsigned_to_nat(0u);
x_50 = l_Lean_Parser_ParserState_mkUnexpectedTokenError(x_48, x_45, x_49);
lean_dec(x_48);
return x_50;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_leadingParserAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_Lean_Parser_leadingParserAux(x_1, x_2, x_6, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_leadingParser(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_7 = lean_box(x_3);
x_8 = lean_alloc_closure((void*)(l_Lean_Parser_leadingParserAux___boxed), 5, 3);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_2);
lean_closure_set(x_8, 2, x_7);
x_9 = lean_box(1);
x_10 = lean_unbox(x_9);
x_11 = l_Lean_Parser_withAntiquotFn(x_4, x_8, x_10, x_5, x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_leadingParser___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l_Lean_Parser_leadingParser(x_1, x_2, x_7, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_trailingLoopStep(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_2);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
lean_dec(x_1);
x_8 = l_List_appendTR(lean_box(0), x_3, x_7);
x_9 = l_Lean_Parser_longestMatchFn(x_6, x_8, x_4, x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_trailingLoop(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
x_5 = lean_box(0);
x_6 = lean_unbox(x_5);
lean_inc(x_3);
lean_inc(x_2);
x_7 = l_Lean_Parser_indexed___redArg(x_4, x_2, x_3, x_6);
lean_dec(x_4);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Parser_ParserState_stackSize(x_3);
x_11 = lean_ctor_get(x_3, 2);
lean_inc(x_11);
lean_dec(x_3);
x_28 = lean_ctor_get(x_8, 4);
lean_inc(x_28);
x_29 = lean_box(0);
x_30 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at___Lean_Parser_ParserState_mkNode_spec__0(x_28, x_29);
if (x_30 == 0)
{
lean_object* x_31; 
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_31 = l_Lean_Parser_ParserState_restore(x_8, x_10, x_11);
lean_dec(x_10);
return x_31;
}
else
{
uint8_t x_32; 
x_32 = l_List_isEmpty___redArg(x_9);
if (x_32 == 0)
{
x_12 = x_32;
goto block_27;
}
else
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_1, 3);
lean_inc(x_33);
x_34 = l_List_isEmpty___redArg(x_33);
lean_dec(x_33);
x_12 = x_34;
goto block_27;
}
}
block_27:
{
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_13 = lean_ctor_get(x_8, 0);
lean_inc(x_13);
x_14 = l_Lean_Parser_SyntaxStack_back(x_13);
lean_dec(x_13);
x_15 = l_Lean_Parser_ParserState_popSyntax(x_8);
lean_inc(x_2);
lean_inc(x_14);
lean_inc(x_1);
x_16 = l_Lean_Parser_trailingLoopStep(x_1, x_14, x_9, x_2, x_15);
x_17 = lean_ctor_get(x_16, 4);
lean_inc(x_17);
x_18 = lean_box(0);
x_19 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at___Lean_Parser_ParserState_mkNode_spec__0(x_17, x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
lean_dec(x_2);
lean_dec(x_1);
x_20 = lean_ctor_get(x_16, 2);
lean_inc(x_20);
x_21 = l_instDecidableEqPos(x_20, x_11);
lean_dec(x_20);
if (x_21 == 0)
{
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
return x_16;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_sub(x_10, x_22);
lean_dec(x_10);
x_24 = l_Lean_Parser_ParserState_restore(x_16, x_23, x_11);
lean_dec(x_23);
x_25 = l_Lean_Parser_ParserState_pushSyntax(x_24, x_14);
return x_25;
}
}
else
{
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
x_3 = x_16;
goto _start;
}
}
else
{
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_prattParser(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
lean_inc(x_5);
lean_inc(x_2);
x_7 = l_Lean_Parser_leadingParser(x_1, x_2, x_3, x_4, x_5, x_6);
x_8 = lean_ctor_get(x_7, 4);
lean_inc(x_8);
x_9 = lean_box(0);
x_10 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at___Lean_Parser_ParserState_mkNode_spec__0(x_8, x_9);
if (x_10 == 0)
{
lean_dec(x_5);
lean_dec(x_2);
return x_7;
}
else
{
lean_object* x_11; 
x_11 = l_Lean_Parser_trailingLoop(x_2, x_5, x_7);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_prattParser___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l_Lean_Parser_prattParser(x_1, x_2, x_7, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_fieldIdxFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_10; lean_object* x_11; uint32_t x_12; uint8_t x_13; lean_object* x_22; uint32_t x_23; uint8_t x_24; 
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_decimalNumberFn_parseOptExp___lam__0___boxed), 1, 0);
x_4 = l_Lean_Parser_ParserState_stackSize(x_2);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_string_utf8_get(x_11, x_5);
lean_dec(x_11);
x_22 = lean_unsigned_to_nat(48u);
x_23 = lean_uint32_of_nat(x_22);
x_24 = lean_uint32_dec_le(x_23, x_12);
if (x_24 == 0)
{
x_13 = x_24;
goto block_21;
}
else
{
lean_object* x_25; uint32_t x_26; uint8_t x_27; 
x_25 = lean_unsigned_to_nat(57u);
x_26 = lean_uint32_of_nat(x_25);
x_27 = lean_uint32_dec_le(x_12, x_26);
x_13 = x_27;
goto block_21;
}
block_9:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_mk_string_unchecked("field index", 11, 11);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_4);
x_8 = l_Lean_Parser_ParserState_mkErrorAt(x_2, x_6, x_5, x_7);
lean_dec(x_7);
lean_dec(x_2);
return x_8;
}
block_21:
{
if (x_13 == 0)
{
lean_dec(x_3);
lean_dec(x_1);
goto block_9;
}
else
{
lean_object* x_14; uint32_t x_15; uint8_t x_16; 
x_14 = lean_unsigned_to_nat(48u);
x_15 = l_Char_ofNat(x_14);
x_16 = l_instDecidableEqChar(x_12, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_4);
x_17 = l_Lean_Parser_takeWhileFn(x_3, x_1, x_2);
x_18 = lean_mk_string_unchecked("fieldIdx", 8, 8);
x_19 = l_Lean_Name_mkStr1(x_18);
x_20 = l_Lean_Parser_mkNodeToken(x_19, x_5, x_1, x_17);
return x_20;
}
else
{
lean_dec(x_3);
lean_dec(x_1);
goto block_9;
}
}
}
}
}
static lean_object* _init_l_Lean_Parser_fieldIdx() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_1 = lean_mk_string_unchecked("fieldIdx", 8, 8);
lean_inc(x_1);
x_2 = l_Lean_Name_mkStr1(x_1);
x_3 = lean_box(1);
x_4 = lean_box(0);
x_5 = lean_unbox(x_3);
x_6 = lean_unbox(x_4);
x_7 = l_Lean_Parser_mkAntiquot(x_1, x_2, x_5, x_6);
x_8 = l_Lean_Parser_mkAtomicInfo(x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_Parser_fieldIdxFn), 2, 0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = l_Lean_Parser_withAntiquot(x_7, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_skip___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_2);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_skip() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_skip___lam__0___boxed), 2, 0);
x_2 = l_Lean_Parser_epsilonInfo;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_skip___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_skip___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = l_Lean_Syntax_getArgs(x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_get_size(x_5);
x_8 = lean_nat_dec_lt(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_apply_2(x_10, lean_box(0), x_4);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = lean_nat_dec_le(x_7, x_7);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_apply_2(x_14, lean_box(0), x_4);
return x_15;
}
else
{
lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_16 = lean_alloc_closure((void*)(l_flip), 6, 4);
lean_closure_set(x_16, 0, lean_box(0));
lean_closure_set(x_16, 1, lean_box(0));
lean_closure_set(x_16, 2, lean_box(0));
lean_closure_set(x_16, 3, x_3);
x_17 = lean_usize_of_nat(x_6);
x_18 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_19 = l_Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_1, x_16, x_5, x_17, x_18, x_4);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Syntax_foldArgsM___redArg(x_2, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Syntax_foldArgsM___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Syntax_foldArgsM(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Syntax_foldArgsM___at___Lean_Syntax_foldArgs_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; 
x_7 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_8 = lean_apply_2(x_1, x_7, x_5);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_usize_of_nat(x_9);
x_11 = lean_usize_add(x_3, x_10);
x_3 = x_11;
x_5 = x_8;
goto _start;
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Syntax_foldArgsM___at___Lean_Syntax_foldArgs_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_foldlMUnsafe_fold___at___Lean_Syntax_foldArgsM___at___Lean_Syntax_foldArgs_spec__0_spec__0___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM___at___Lean_Syntax_foldArgs_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = l_Lean_Syntax_getArgs(x_1);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_array_get_size(x_4);
x_7 = lean_nat_dec_lt(x_5, x_6);
if (x_7 == 0)
{
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
return x_3;
}
else
{
uint8_t x_8; 
x_8 = lean_nat_dec_le(x_6, x_6);
if (x_8 == 0)
{
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
return x_3;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_usize_of_nat(x_5);
x_10 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_11 = l_Array_foldlMUnsafe_fold___at___Lean_Syntax_foldArgsM___at___Lean_Syntax_foldArgs_spec__0_spec__0___redArg(x_2, x_4, x_9, x_10, x_3);
lean_dec(x_4);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM___at___Lean_Syntax_foldArgs_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Syntax_foldArgsM___at___Lean_Syntax_foldArgs_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgs___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Syntax_foldArgsM___at___Lean_Syntax_foldArgs_spec__0___redArg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Syntax_foldArgsM___at___Lean_Syntax_foldArgs_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Syntax_foldArgsM___at___Lean_Syntax_foldArgs_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at___Lean_Syntax_foldArgsM___at___Lean_Syntax_foldArgs_spec__0_spec__0___redArg(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Syntax_foldArgsM___at___Lean_Syntax_foldArgs_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_foldlMUnsafe_fold___at___Lean_Syntax_foldArgsM___at___Lean_Syntax_foldArgs_spec__0_spec__0(x_1, x_2, x_3, x_7, x_8, x_6);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM___at___Lean_Syntax_foldArgs_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Syntax_foldArgsM___at___Lean_Syntax_foldArgs_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM___at___Lean_Syntax_foldArgs_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Syntax_foldArgsM___at___Lean_Syntax_foldArgs_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgs___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Syntax_foldArgs___redArg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Syntax_foldArgs(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_forArgsM___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_1(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_forArgsM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_alloc_closure((void*)(l_Lean_Syntax_forArgsM___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_4, 0, x_3);
x_5 = lean_box(0);
x_6 = l_Lean_Syntax_foldArgsM___redArg(x_1, x_2, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_forArgsM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Syntax_forArgsM___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_forArgsM___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Syntax_forArgsM___redArg___lam__0(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_forArgsM___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Syntax_forArgsM___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_forArgsM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Syntax_forArgsM(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* initialize_Lean_Parser_Types(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Parser_Basic(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Parser_Types(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_epsilonInfo = _init_l_Lean_Parser_epsilonInfo();
lean_mark_persistent(l_Lean_Parser_epsilonInfo);
l_Lean_Parser_instAndThenParser = _init_l_Lean_Parser_instAndThenParser();
lean_mark_persistent(l_Lean_Parser_instAndThenParser);
if (builtin) {res = l___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_instBEqOrElseOnAntiquotBehavior = _init_l_Lean_Parser_instBEqOrElseOnAntiquotBehavior();
lean_mark_persistent(l_Lean_Parser_instBEqOrElseOnAntiquotBehavior);
if (builtin) {res = l___regBuiltin_Lean_Parser_orelse_docString__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_instOrElseParser = _init_l_Lean_Parser_instOrElseParser();
lean_mark_persistent(l_Lean_Parser_instOrElseParser);
if (builtin) {res = l___regBuiltin_Lean_Parser_atomic_docString__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_instBEqRecoveryContext = _init_l_Lean_Parser_instBEqRecoveryContext();
lean_mark_persistent(l_Lean_Parser_instBEqRecoveryContext);
l_Lean_Parser_instReprRecoveryContext = _init_l_Lean_Parser_instReprRecoveryContext();
lean_mark_persistent(l_Lean_Parser_instReprRecoveryContext);
if (builtin) {res = l___regBuiltin_Lean_Parser_recover_x27_docString__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_recover_docString__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_lookahead_docString__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_notFollowedBy_docString__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_checkWsBefore_docString__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_numLitNoAntiquot = _init_l_Lean_Parser_numLitNoAntiquot();
lean_mark_persistent(l_Lean_Parser_numLitNoAntiquot);
l_Lean_Parser_scientificLitNoAntiquot = _init_l_Lean_Parser_scientificLitNoAntiquot();
lean_mark_persistent(l_Lean_Parser_scientificLitNoAntiquot);
l_Lean_Parser_strLitNoAntiquot = _init_l_Lean_Parser_strLitNoAntiquot();
lean_mark_persistent(l_Lean_Parser_strLitNoAntiquot);
l_Lean_Parser_charLitNoAntiquot = _init_l_Lean_Parser_charLitNoAntiquot();
lean_mark_persistent(l_Lean_Parser_charLitNoAntiquot);
l_Lean_Parser_nameLitNoAntiquot = _init_l_Lean_Parser_nameLitNoAntiquot();
lean_mark_persistent(l_Lean_Parser_nameLitNoAntiquot);
l_Lean_Parser_identNoAntiquot = _init_l_Lean_Parser_identNoAntiquot();
lean_mark_persistent(l_Lean_Parser_identNoAntiquot);
l_Lean_Parser_rawIdentNoAntiquot = _init_l_Lean_Parser_rawIdentNoAntiquot();
lean_mark_persistent(l_Lean_Parser_rawIdentNoAntiquot);
l_Lean_Parser_hygieneInfoNoAntiquot = _init_l_Lean_Parser_hygieneInfoNoAntiquot();
lean_mark_persistent(l_Lean_Parser_hygieneInfoNoAntiquot);
if (builtin) {res = l___regBuiltin_Lean_Parser_checkColEq_docString__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_checkColGe_docString__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_checkColGt_docString__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_checkLineEq_docString__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_withPosition_docString__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_withoutPosition_docString__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_withForbidden_docString__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_withoutForbidden_docString__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_eoi = _init_l_Lean_Parser_eoi();
lean_mark_persistent(l_Lean_Parser_eoi);
l_Lean_Parser_instInhabitedPrattParsingTables = _init_l_Lean_Parser_instInhabitedPrattParsingTables();
lean_mark_persistent(l_Lean_Parser_instInhabitedPrattParsingTables);
l_Lean_Parser_instInhabitedLeadingIdentBehavior = _init_l_Lean_Parser_instInhabitedLeadingIdentBehavior();
l_Lean_Parser_instBEqLeadingIdentBehavior = _init_l_Lean_Parser_instBEqLeadingIdentBehavior();
lean_mark_persistent(l_Lean_Parser_instBEqLeadingIdentBehavior);
l_Lean_Parser_instReprLeadingIdentBehavior = _init_l_Lean_Parser_instReprLeadingIdentBehavior();
lean_mark_persistent(l_Lean_Parser_instReprLeadingIdentBehavior);
l_Lean_Parser_instInhabitedParserCategory = _init_l_Lean_Parser_instInhabitedParserCategory();
lean_mark_persistent(l_Lean_Parser_instInhabitedParserCategory);
if (builtin) {res = l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_9337_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Parser_categoryParserFnRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Parser_categoryParserFnRef);
lean_dec_ref(res);
}if (builtin) {res = l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_9363_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Parser_categoryParserFnExtension = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Parser_categoryParserFnExtension);
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_checkNoImmediateColon = _init_l_Lean_Parser_checkNoImmediateColon();
lean_mark_persistent(l_Lean_Parser_checkNoImmediateColon);
l_Lean_Parser_pushNone = _init_l_Lean_Parser_pushNone();
lean_mark_persistent(l_Lean_Parser_pushNone);
l_Lean_Parser_antiquotNestedExpr = _init_l_Lean_Parser_antiquotNestedExpr();
lean_mark_persistent(l_Lean_Parser_antiquotNestedExpr);
l_Lean_Parser_antiquotExpr = _init_l_Lean_Parser_antiquotExpr();
lean_mark_persistent(l_Lean_Parser_antiquotExpr);
l_Lean_Parser_instCoeStringParser = _init_l_Lean_Parser_instCoeStringParser();
lean_mark_persistent(l_Lean_Parser_instCoeStringParser);
if (builtin) {res = l___regBuiltin_Lean_Parser_mkAntiquot_docString__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_withAntiquot_docString__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_fieldIdx = _init_l_Lean_Parser_fieldIdx();
lean_mark_persistent(l_Lean_Parser_fieldIdx);
l_Lean_Parser_skip = _init_l_Lean_Parser_skip();
lean_mark_persistent(l_Lean_Parser_skip);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
