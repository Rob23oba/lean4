// Lean compiler output
// Module: Lean.PrettyPrinter.Formatter
// Imports: Lean.CoreM Lean.Parser.Extension Lean.Parser.StrInterpolation Lean.KeyedDeclsAttribute Lean.ParserCompiler.Attribute Lean.PrettyPrinter.Basic
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkKind___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_setStack___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_pushToken(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_setLhsPrec_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_PrettyPrinter_Formatter_categoryFormatterCore_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_PrettyPrinter_Formatter_interpolatedStr_formatter_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goUp___at___Lean_PrettyPrinter_Formatter_visitArgs_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_withAntiquotSuffixSplice_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_Traverser_down(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_instCoeForallFormatterAliasValue;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_pushAlign(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_notFollowedBy_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_instInhabitedFormat;
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Formatter_0__Lean_PrettyPrinter_Formatter_SourceInfo_getExprPos_x3f(lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_formatStx(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkWsBefore_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_pushToken___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5154_(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkPrec_formatter___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_pushLine___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_PrettyPrinter_Formatter_unicodeSymbolNoAntiquot_formatter_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_registerAliasCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_parseToken(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkStackTop_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkKind___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_orelse_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Formatter_0__Lean_PrettyPrinter_Formatter_SourceInfo_getExprPos_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_fill(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_rawIdentNoAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkNoImmediateColon_formatter___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___lam__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentD(lean_object*);
uint8_t l_Array_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_setLhsPrec_formatter___redArg(lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_parseToken___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_PrettyPrinter_Formatter_categoryFormatterCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Format_fill(lean_object*);
lean_object* l_Lean_Syntax_Traverser_fromSyntax(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkKind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkPrec_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isAntiquotSuffixSplice(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_instOrElseFormatterM(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_pushNone_formatter___redArg(lean_object*, lean_object*);
lean_object* l_Lean_isTracingEnabledFor___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20_spec__20___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_getStackSize___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Array_reverse(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkColGt_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_sepByNoAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_pushToken___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkLineEq_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_pushWhitespace___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_skip_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Formatter_0__Lean_PrettyPrinter_Formatter_getExprPos_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_FormatterM_orElse___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goDown___at___Lean_PrettyPrinter_Formatter_visitArgs_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5637_(lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_andthenFn(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_PrettyPrinter_Formatter_unicodeSymbolNoAntiquot_formatter_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_formatterForKindUnsafe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_throwBacktrack(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_rawIdentNoAntiquot_formatter___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkNoWsBefore_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_format(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_error_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_takeWhileAux___at___Lean_PrettyPrinter_format_spec__0(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_FormatterM_orElse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_identEq_formatter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkLhsPrec_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_fieldIdx_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_eoi_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goDown___at___Lean_PrettyPrinter_Formatter_visitArgs_spec__3___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_Traverser_left(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_tokenWithAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_throwBacktrack___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_getStack(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_rawCh_formatter(uint32_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_forM_loop___at___Lean_PrettyPrinter_Formatter_manyNoAntiquot_formatter_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_charLitNoAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_parseToken___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lean_Parser_ParserFn_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Substring_takeRightWhileAux___at___Lean_PrettyPrinter_Formatter_pushToken_spec__1(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkTailWs_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_Format_isNil(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_withMaybeTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_PrettyPrinter_format_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkKind___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goUp___at___Lean_PrettyPrinter_Formatter_visitArgs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_instInhabitedNat;
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___Lean_PrettyPrinter_Formatter_visitArgs_spec__2___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Parser_getTokenTable(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_skip_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_InternalExceptionId_0__Lean_beqInternalExceptionId____x40_Lean_InternalExceptionId___hyg_26_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Formatter_0__Lean_PrettyPrinter_Formatter_push___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_takeRightWhileAux___at___Lean_PrettyPrinter_Formatter_pushToken_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_trailingNode_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_errorAtSavedPos_formatter___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_getStack___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_withoutInfo_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_withFn_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_recover_x27_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkTailWs_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_categoryFormatterCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_pretty_printer_formatter_interpret_parser_descr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Formatter_0__Lean_PrettyPrinter_Formatter_getExprPos_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_formatTerm(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_addConstInfo___at___Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Formatter_0__Lean_PrettyPrinter_Formatter_push___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_concat___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Nat_forM_loop___at___Lean_PrettyPrinter_Formatter_manyNoAntiquot_formatter_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_instCoeForallFormatterAliasValue___lam__0(lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_instCoeForallForallFormatterAliasValue;
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_PrettyPrinter_Formatter_concat_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Substring_takeWhileAux___at___Lean_PrettyPrinter_Formatter_pushToken_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_pushToken___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_formatCommand(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_instCoeForallForallFormatterAliasValue___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_getStack___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_pushWhitespace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_manyNoAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkWsBefore_formatter___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter_spec__0___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_PrettyPrinter_Formatter_unicodeSymbolNoAntiquot_formatter_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkPrec_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_shrink___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_withAntiquotSuffixSplice_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_hygieneInfoNoAntiquot_formatter___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_PrettyPrinter_Formatter_categoryFormatterCore_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_withAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goUp___at___Lean_PrettyPrinter_Formatter_visitArgs_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkParserState(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Formatter_0__Lean_PrettyPrinter_Formatter_push(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_pushToken___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkNoWsBefore_formatter___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_visitAtom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_parserOfStack_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_hygieneInfoNoAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_many1Unbox_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_tokenFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___Lean_PrettyPrinter_Formatter_visitArgs_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_PrettyPrinter_Formatter_categoryFormatterCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goDown___at___Lean_PrettyPrinter_Formatter_visitArgs_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Attribute_Builtin_getIdent(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extract(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_hygieneInfoNoAntiquot_formatter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_nameLitNoAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_PrettyPrinter_Formatter_categoryFormatterCore_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_registerAlias(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_back_x21(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_hygieneInfoNoAntiquot_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FileMap_ofString(lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_pushWhitespace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkStackTop_formatter___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkWsBefore_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_notFollowedBy_formatter___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkColGe_formatter___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___lam__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_getStackSize___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_optionalNoAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_pushLine___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_forRevM_loop___at___Lean_PrettyPrinter_Formatter_sepByNoAntiquot_formatter_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_format___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_lookahead_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_takeRightWhileAux___at___Lean_PrettyPrinter_Formatter_pushToken_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_PrettyPrinter_Formatter_categoryFormatterCore_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_pushAlign___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_nonReservedSymbolNoAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_forRevM_loop___at___Lean_PrettyPrinter_Formatter_sepByNoAntiquot_formatter_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkColGe_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_pushLine___redArg(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_PrettyPrinter_Formatter_categoryFormatterCore_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkColGt_formatter___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkColGt_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PrettyPrinter_Formatter_rawIdentNoAntiquot_formatter___lam__0(lean_object*);
lean_object* lean_mk_antiquot_formatter(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_PrettyPrinter_Formatter_unicodeSymbolNoAntiquot_formatter_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_prev(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_rawCh_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5055_(lean_object*);
uint8_t l_Lean_Syntax_isTokenAntiquot(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkTailWs_formatter___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___Lean_PrettyPrinter_Formatter_visitArgs_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_instCoeFormatterAliasValue;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_pp_oneline;
lean_object* l_instMonadEIO___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_setStack___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* lean_int_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___Lean_PrettyPrinter_Formatter_visitArgs_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_pushNone_formatter___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_notFollowedBy_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_formatterAliasesRef;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_pushLine(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_setStack___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_parserOfStack_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkColEq_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_PrettyPrinter_Formatter_categoryFormatterCore_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkLinebreakBefore_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_PrettyPrinter_Formatter_interpolatedStr_formatter_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_pushNone_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_combinatorFormatterAttribute;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_pushToken___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_withAntiquotSuffixSplice_formatter___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_String_anyAux___at___Lean_Parser_checkTailLinebreak_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_format___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isToken(lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_registerCombinatorAttribute(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_format___lam__2___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkWsBefore_formatter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___Lean_PrettyPrinter_Formatter_visitArgs_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_String_findAux(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___Lean_throwUnknownIdentifier___at___Lean_throwUnknownConstant___at___Lean_filterFieldList___at___Lean_realizeGlobalConstCore_spec__0_spec__2_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_categoryFormatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_simp_macro_scopes(lean_object*);
uint8_t l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_lookahead_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_scientificLitNoAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_PrettyPrinter_Formatter_concat_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_group(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Format_pretty_x27(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_pushAlign___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkLineEq_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkStackTop_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_eoi_formatter___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_format___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_visitArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_withAntiquotSuffixSplice_formatter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_errorAtSavedPos_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_init___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_setStack(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isLit_x3f(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkNoImmediateColon_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_sepBy1NoAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkNoImmediateColon_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_throwBacktrack___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___Lean_PrettyPrinter_Formatter_visitArgs_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_eoi_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goUp___at___Lean_PrettyPrinter_Formatter_visitArgs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_takeRightWhileAux___at___Lean_PrettyPrinter_Formatter_pushToken_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Data_Trie_find_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_PrettyPrinter_format_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_concat___lam__0___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_runForNodeKind___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_error_formatter___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Substring_prevn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PrettyPrinter_format___lam__2(uint32_t);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Format_getIndent(lean_object*);
lean_object* l_Lean_Option_register___at___Lean_initFn____x40_Lean_Util_Profile___hyg_5__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_PrettyPrinter_backtrackExceptionId;
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___Lean_PrettyPrinter_Formatter_visitArgs_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_andthen_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_errorAtSavedPos_formatter(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkLhsPrec_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_indent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkColGe_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_mkAntiquot_formatter_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_pushNone_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_parseToken___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_strLitNoAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_forM_loop___at___Lean_PrettyPrinter_Formatter_manyNoAntiquot_formatter_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_getStackSize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_takeWhileAux___at___Lean_PrettyPrinter_Formatter_pushToken_spec__2(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_formatCategory(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_withMaybeTag___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_seqRight(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_skip_formatter___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_recover_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Substring_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_getStackSize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_many1NoAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_takeWhileAux___at___Lean_PrettyPrinter_format_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_Traverser_up(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_panic___at___Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter_spec__0___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_withFn_formatter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedSyntax;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_lookahead_formatter___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_formatterAttribute;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goDown___at___Lean_PrettyPrinter_Formatter_visitArgs_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_pushAlign___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_format___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Parser_isValidSyntaxNodeKind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___Lean_PrettyPrinter_Formatter_visitArgs_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Formatter_0__Lean_PrettyPrinter_Formatter_push___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_takeRightWhileAux___at___Lean_PrettyPrinter_Formatter_pushToken_spec__3(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_whitespace(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkLinebreakBefore_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_instCoeFormatterAliasValue___lam__0(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_mkCombinatorFormatterAttribute(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_categoryParser_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_takeRightWhileAux___at___Lean_PrettyPrinter_Formatter_pushToken_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_withFn_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_unicodeSymbolNoAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_parserOfStack_formatter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_error_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkLhsPrec_formatter___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_getStack___redArg___boxed(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_identEq_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkLinebreakBefore_formatter___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_formatTactic(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkNoWsBefore_formatter___redArg(lean_object*, lean_object*);
uint8_t l_instDecidableEqChar(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_setLhsPrec_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_concat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_optionalNoAntiquot_formatter___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_optionalNoAntiquot_formatter___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkNoWsBefore_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_numLitNoAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkColEq_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_forRevM_loop___at___Lean_PrettyPrinter_Formatter_sepByNoAntiquot_formatter_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t l_Char_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkLineEq_formatter___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_pushWhitespace___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_node_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_parserOfStack_formatter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkColEq_formatter___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_identEq_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_FormatterM_orElse___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_st_ref_get(x_4, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_11 = lean_apply_5(x_1, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_23; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
x_14 = l_Lean_PrettyPrinter_backtrackExceptionId;
x_23 = l_Lean_Exception_isInterrupt(x_12);
if (x_23 == 0)
{
uint8_t x_24; 
x_24 = l_Lean_Exception_isRuntime(x_12);
x_15 = x_24;
goto block_22;
}
else
{
x_15 = x_23;
goto block_22;
}
block_22:
{
if (x_15 == 0)
{
if (lean_obj_tag(x_12) == 0)
{
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
lean_dec(x_12);
x_17 = l___private_Lean_InternalExceptionId_0__Lean_beqInternalExceptionId____x40_Lean_InternalExceptionId___hyg_26_(x_14, x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_11);
x_18 = lean_st_ref_set(x_4, x_9, x_13);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_box(0);
x_21 = lean_apply_6(x_2, x_20, x_3, x_4, x_5, x_6, x_19);
return x_21;
}
}
}
else
{
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_FormatterM_orElse(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_st_ref_get(x_5, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_12 = lean_apply_5(x_2, x_4, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_24; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
x_15 = l_Lean_PrettyPrinter_backtrackExceptionId;
x_24 = l_Lean_Exception_isInterrupt(x_13);
if (x_24 == 0)
{
uint8_t x_25; 
x_25 = l_Lean_Exception_isRuntime(x_13);
x_16 = x_25;
goto block_23;
}
else
{
x_16 = x_24;
goto block_23;
}
block_23:
{
if (x_16 == 0)
{
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_13, 0);
lean_inc(x_17);
lean_dec(x_13);
x_18 = l___private_Lean_InternalExceptionId_0__Lean_beqInternalExceptionId____x40_Lean_InternalExceptionId___hyg_26_(x_15, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_12);
x_19 = lean_st_ref_set(x_5, x_10, x_14);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_box(0);
x_22 = lean_apply_6(x_3, x_21, x_4, x_5, x_6, x_7, x_20);
return x_22;
}
}
}
else
{
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_instOrElseFormatterM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_FormatterM_orElse), 8, 1);
lean_closure_set(x_2, 0, lean_box(0));
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___lam__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_10 = x_7;
} else {
 lean_dec_ref(x_7);
 x_10 = lean_box(0);
}
lean_inc(x_1);
lean_inc(x_5);
lean_inc(x_4);
x_11 = lean_apply_4(x_1, x_8, x_4, x_5, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Attribute_Builtin_getIdent(x_3, x_4, x_5, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_17 = x_14;
} else {
 lean_dec_ref(x_14);
 x_17 = lean_box(0);
}
x_18 = l_Lean_Syntax_getId(x_15);
if (x_2 == 0)
{
goto block_70;
}
else
{
lean_object* x_71; uint8_t x_72; lean_object* x_73; 
x_71 = lean_box(0);
x_72 = lean_unbox(x_71);
lean_inc(x_18);
lean_inc(x_12);
x_73 = l_Lean_Environment_find_x3f(x_12, x_18, x_72);
if (lean_obj_tag(x_73) == 0)
{
goto block_70;
}
else
{
lean_dec(x_73);
lean_dec(x_12);
lean_dec(x_10);
x_35 = x_4;
x_36 = x_5;
x_37 = x_16;
goto block_56;
}
}
block_34:
{
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_15);
if (lean_is_scalar(x_17)) {
 x_23 = lean_alloc_ctor(0, 2, 0);
} else {
 x_23 = x_17;
}
lean_ctor_set(x_23, 0, x_18);
lean_ctor_set(x_23, 1, x_19);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_17);
x_24 = lean_box(0);
lean_inc(x_18);
x_25 = l_Lean_Elab_addConstInfo___at___Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(x_15, x_18, x_24, x_21, x_20, x_19);
lean_dec(x_20);
lean_dec(x_21);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
lean_ctor_set(x_25, 0, x_18);
return x_25;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_18);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
else
{
uint8_t x_30; 
lean_dec(x_18);
x_30 = !lean_is_exclusive(x_25);
if (x_30 == 0)
{
return x_25;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_25, 0);
x_32 = lean_ctor_get(x_25, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_25);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
block_56:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_st_ref_get(x_36, x_37);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
lean_inc(x_36);
lean_inc(x_35);
x_41 = lean_apply_4(x_1, x_39, x_35, x_36, x_40);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_49; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_st_ref_get(x_36, x_43);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_box(1);
x_48 = lean_unbox(x_47);
lean_inc(x_18);
x_49 = l_Lean_Environment_contains(x_42, x_18, x_48);
if (x_49 == 0)
{
lean_dec(x_45);
x_19 = x_46;
x_20 = x_36;
x_21 = x_35;
x_22 = x_49;
goto block_34;
}
else
{
lean_object* x_50; uint8_t x_51; 
x_50 = lean_ctor_get(x_45, 6);
lean_inc(x_50);
lean_dec(x_45);
x_51 = lean_ctor_get_uint8(x_50, sizeof(void*)*3);
lean_dec(x_50);
x_19 = x_46;
x_20 = x_36;
x_21 = x_35;
x_22 = x_51;
goto block_34;
}
}
else
{
uint8_t x_52; 
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
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
block_70:
{
uint8_t x_57; 
lean_inc(x_18);
x_57 = l_Lean_Parser_isValidSyntaxNodeKind(x_12, x_18);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_1);
x_58 = lean_mk_string_unchecked("invalid [formatter] argument, unknown syntax kind '", 51, 51);
x_59 = l_Lean_stringToMessageData(x_58);
lean_dec(x_58);
x_60 = l_Lean_MessageData_ofName(x_18);
if (lean_is_scalar(x_10)) {
 x_61 = lean_alloc_ctor(7, 2, 0);
} else {
 x_61 = x_10;
 lean_ctor_set_tag(x_61, 7);
}
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_mk_string_unchecked("'", 1, 1);
x_63 = l_Lean_stringToMessageData(x_62);
lean_dec(x_62);
x_64 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_63);
x_65 = l_Lean_throwError___at___Lean_throwUnknownIdentifier___at___Lean_throwUnknownConstant___at___Lean_filterFieldList___at___Lean_realizeGlobalConstCore_spec__0_spec__2_spec__2_spec__2___redArg(x_64, x_4, x_5, x_16);
lean_dec(x_5);
lean_dec(x_4);
x_66 = !lean_is_exclusive(x_65);
if (x_66 == 0)
{
return x_65;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_65, 0);
x_68 = lean_ctor_get(x_65, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_65);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
else
{
lean_dec(x_10);
x_35 = x_4;
x_36 = x_5;
x_37 = x_16;
goto block_56;
}
}
}
else
{
uint8_t x_74; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_74 = !lean_is_exclusive(x_14);
if (x_74 == 0)
{
return x_14;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_14, 0);
x_76 = lean_ctor_get(x_14, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_14);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_78 = !lean_is_exclusive(x_11);
if (x_78 == 0)
{
return x_11;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_11, 0);
x_80 = lean_ctor_get(x_11, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_11);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_mkFormatterAttribute___lam__0___boxed), 5, 0);
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_mkFormatterAttribute___lam__1___boxed), 4, 0);
x_4 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_mkFormatterAttribute___lam__2___boxed), 6, 1);
lean_closure_set(x_4, 0, x_3);
x_5 = lean_mk_string_unchecked("builtin_formatter", 17, 17);
x_6 = l_Lean_Name_mkStr1(x_5);
x_7 = lean_mk_string_unchecked("formatter", 9, 9);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("Register a formatter for a parser.\n\n  [formatter k] registers a declaration of type `Lean.PrettyPrinter.Formatter` for the `SyntaxNodeKind` `k`.", 144, 144);
x_10 = lean_mk_string_unchecked("Lean", 4, 4);
x_11 = lean_mk_string_unchecked("PrettyPrinter", 13, 13);
x_12 = lean_mk_string_unchecked("Formatter", 9, 9);
lean_inc(x_11);
lean_inc(x_10);
x_13 = l_Lean_Name_mkStr3(x_10, x_11, x_12);
x_14 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_14, 0, x_6);
lean_ctor_set(x_14, 1, x_8);
lean_ctor_set(x_14, 2, x_9);
lean_ctor_set(x_14, 3, x_13);
lean_ctor_set(x_14, 4, x_4);
lean_ctor_set(x_14, 5, x_2);
x_15 = lean_mk_string_unchecked("formatterAttribute", 18, 18);
x_16 = l_Lean_Name_mkStr3(x_10, x_11, x_15);
x_17 = l_Lean_KeyedDeclsAttribute_init___redArg(x_14, x_16, x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l_Lean_PrettyPrinter_mkFormatterAttribute___lam__0(x_6, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_mkFormatterAttribute___lam__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_2);
lean_dec(x_2);
x_8 = l_Lean_PrettyPrinter_mkFormatterAttribute___lam__2(x_1, x_7, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_mkCombinatorFormatterAttribute(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("combinator_formatter", 20, 20);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_mk_string_unchecked("Register a formatter for a parser combinator.\n\n  [combinator_formatter c] registers a declaration of type `Lean.PrettyPrinter.Formatter` for the `Parser` declaration `c`.\n  Note that, unlike with [formatter], this is not a node kind since combinators usually do not introduce their own node kinds.\n  The tagged declaration may optionally accept parameters corresponding to (a prefix of) those of `c`, where `Parser` is replaced\n  with `Formatter` in the parameter types.", 470, 470);
x_5 = lean_mk_string_unchecked("Lean", 4, 4);
x_6 = lean_mk_string_unchecked("PrettyPrinter", 13, 13);
x_7 = lean_mk_string_unchecked("mkCombinatorFormatterAttribute", 30, 30);
x_8 = l_Lean_Name_mkStr3(x_5, x_6, x_7);
x_9 = l_Lean_ParserCompiler_registerCombinatorAttribute(x_3, x_4, x_8, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_throwBacktrack___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_PrettyPrinter_backtrackExceptionId;
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_throwBacktrack(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Formatter_throwBacktrack___redArg(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_throwBacktrack___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Formatter_throwBacktrack(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_st_ref_get(x_2, x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
lean_ctor_set(x_6, 0, x_9);
return x_6;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_6, 0);
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_6);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_7 = lean_st_ref_take(x_3, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
x_11 = lean_ctor_get_uint8(x_8, sizeof(void*)*3);
x_12 = lean_ctor_get_uint8(x_8, sizeof(void*)*3 + 1);
x_13 = lean_ctor_get_uint8(x_8, sizeof(void*)*3 + 2);
x_14 = lean_ctor_get(x_8, 2);
lean_inc(x_14);
lean_dec(x_8);
x_15 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_10);
lean_ctor_set(x_15, 2, x_14);
lean_ctor_set_uint8(x_15, sizeof(void*)*3, x_11);
lean_ctor_set_uint8(x_15, sizeof(void*)*3 + 1, x_12);
lean_ctor_set_uint8(x_15, sizeof(void*)*3 + 2, x_13);
x_16 = lean_st_ref_set(x_3, x_15, x_9);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
x_19 = lean_box(0);
lean_ctor_set(x_16, 0, x_19);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_8 = lean_st_ref_take(x_4, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
x_12 = lean_apply_1(x_2, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
x_16 = lean_ctor_get_uint8(x_9, sizeof(void*)*3);
x_17 = lean_ctor_get_uint8(x_9, sizeof(void*)*3 + 1);
x_18 = lean_ctor_get_uint8(x_9, sizeof(void*)*3 + 2);
x_19 = lean_ctor_get(x_9, 2);
lean_inc(x_19);
lean_dec(x_9);
x_20 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_20, 0, x_14);
lean_ctor_set(x_20, 1, x_15);
lean_ctor_set(x_20, 2, x_19);
lean_ctor_set_uint8(x_20, sizeof(void*)*3, x_16);
lean_ctor_set_uint8(x_20, sizeof(void*)*3 + 1, x_17);
lean_ctor_set_uint8(x_20, sizeof(void*)*3 + 2, x_18);
x_21 = lean_st_ref_set(x_4, x_20, x_10);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
lean_ctor_set(x_21, 0, x_13);
return x_21;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_13);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___lam__0___boxed), 5, 0);
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___lam__1___boxed), 6, 0);
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___lam__2___boxed), 7, 0);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___lam__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_getStack___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_st_ref_get(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
lean_dec(x_5);
lean_ctor_set(x_3, 0, x_6);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_3);
x_9 = lean_ctor_get(x_7, 2);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_getStack(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Formatter_getStack___redArg(x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_getStack___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PrettyPrinter_Formatter_getStack___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_getStack___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Formatter_getStack(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_getStackSize___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_PrettyPrinter_Formatter_getStack___redArg(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_array_get_size(x_5);
lean_dec(x_5);
lean_ctor_set(x_3, 0, x_6);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_3);
x_9 = lean_array_get_size(x_7);
lean_dec(x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_getStackSize(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Formatter_getStackSize___redArg(x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_getStackSize___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PrettyPrinter_Formatter_getStackSize___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_getStackSize___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Formatter_getStackSize(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_setStack___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_4 = lean_st_ref_take(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
x_9 = lean_ctor_get_uint8(x_5, sizeof(void*)*3);
x_10 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 1);
x_11 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 2);
lean_dec(x_5);
x_12 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_8);
lean_ctor_set(x_12, 2, x_1);
lean_ctor_set_uint8(x_12, sizeof(void*)*3, x_9);
lean_ctor_set_uint8(x_12, sizeof(void*)*3 + 1, x_10);
lean_ctor_set_uint8(x_12, sizeof(void*)*3 + 2, x_11);
x_13 = lean_st_ref_set(x_2, x_12, x_6);
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_setStack(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Formatter_setStack___redArg(x_1, x_3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_setStack___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PrettyPrinter_Formatter_setStack___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_setStack___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Formatter_setStack(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Formatter_0__Lean_PrettyPrinter_Formatter_push___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; uint8_t x_17; 
x_4 = lean_st_ref_take(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
x_9 = lean_ctor_get_uint8(x_5, sizeof(void*)*3);
x_10 = lean_box(0);
x_11 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 2);
x_12 = lean_ctor_get(x_5, 2);
lean_inc(x_12);
lean_dec(x_5);
x_13 = lean_array_push(x_12, x_1);
x_14 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_8);
lean_ctor_set(x_14, 2, x_13);
lean_ctor_set_uint8(x_14, sizeof(void*)*3, x_9);
x_15 = lean_unbox(x_10);
lean_ctor_set_uint8(x_14, sizeof(void*)*3 + 1, x_15);
lean_ctor_set_uint8(x_14, sizeof(void*)*3 + 2, x_11);
x_16 = lean_st_ref_set(x_2, x_14, x_6);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
x_19 = lean_box(0);
lean_ctor_set(x_16, 0, x_19);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Formatter_0__Lean_PrettyPrinter_Formatter_push(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_PrettyPrinter_Formatter_0__Lean_PrettyPrinter_Formatter_push___redArg(x_1, x_3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Formatter_0__Lean_PrettyPrinter_Formatter_push___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_PrettyPrinter_Formatter_0__Lean_PrettyPrinter_Formatter_push___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Formatter_0__Lean_PrettyPrinter_Formatter_push___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_PrettyPrinter_Formatter_0__Lean_PrettyPrinter_Formatter_push(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_pushWhitespace___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; uint8_t x_18; 
x_4 = l___private_Lean_PrettyPrinter_Formatter_0__Lean_PrettyPrinter_Formatter_push___redArg(x_1, x_2, x_3);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_st_ref_take(x_2, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = lean_mk_string_unchecked("", 0, 0);
x_11 = lean_box(0);
x_12 = lean_ctor_get_uint8(x_7, sizeof(void*)*3 + 2);
x_13 = lean_ctor_get(x_7, 2);
lean_inc(x_13);
lean_dec(x_7);
x_14 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_14, 0, x_9);
lean_ctor_set(x_14, 1, x_10);
lean_ctor_set(x_14, 2, x_13);
x_15 = lean_unbox(x_11);
lean_ctor_set_uint8(x_14, sizeof(void*)*3, x_15);
x_16 = lean_unbox(x_11);
lean_ctor_set_uint8(x_14, sizeof(void*)*3 + 1, x_16);
lean_ctor_set_uint8(x_14, sizeof(void*)*3 + 2, x_12);
x_17 = lean_st_ref_set(x_2, x_14, x_8);
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
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_pushWhitespace(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Formatter_pushWhitespace___redArg(x_1, x_3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_pushWhitespace___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PrettyPrinter_Formatter_pushWhitespace___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_pushWhitespace___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Formatter_pushWhitespace(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_pushLine___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(1);
x_4 = l_Lean_PrettyPrinter_Formatter_pushWhitespace___redArg(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_pushLine(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Formatter_pushLine___redArg(x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_pushLine___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PrettyPrinter_Formatter_pushLine___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_pushLine___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Formatter_pushLine(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_pushAlign___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(2, 0, 1);
lean_ctor_set_uint8(x_4, 0, x_1);
x_5 = l_Lean_PrettyPrinter_Formatter_pushWhitespace___redArg(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_pushAlign(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Formatter_pushAlign___redArg(x_1, x_3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_pushAlign___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_PrettyPrinter_Formatter_pushAlign___redArg(x_4, x_2, x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_pushAlign___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_1);
lean_dec(x_1);
x_8 = l_Lean_PrettyPrinter_Formatter_pushAlign(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goUp___at___Lean_PrettyPrinter_Formatter_visitArgs_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_3 = lean_st_ref_take(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = l_Lean_Syntax_Traverser_up(x_6);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
x_9 = lean_ctor_get_uint8(x_4, sizeof(void*)*3);
x_10 = lean_ctor_get_uint8(x_4, sizeof(void*)*3 + 1);
x_11 = lean_ctor_get_uint8(x_4, sizeof(void*)*3 + 2);
x_12 = lean_ctor_get(x_4, 2);
lean_inc(x_12);
lean_dec(x_4);
x_13 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set_uint8(x_13, sizeof(void*)*3, x_9);
lean_ctor_set_uint8(x_13, sizeof(void*)*3 + 1, x_10);
lean_ctor_set_uint8(x_13, sizeof(void*)*3 + 2, x_11);
x_14 = lean_st_ref_set(x_1, x_13, x_5);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
x_17 = lean_box(0);
lean_ctor_set(x_14, 0, x_17);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goUp___at___Lean_PrettyPrinter_Formatter_visitArgs_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Syntax_MonadTraverser_goUp___at___Lean_PrettyPrinter_Formatter_visitArgs_spec__0___redArg(x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___Lean_PrettyPrinter_Formatter_visitArgs_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_3 = lean_st_ref_take(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = l_Lean_Syntax_Traverser_left(x_6);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
x_9 = lean_ctor_get_uint8(x_4, sizeof(void*)*3);
x_10 = lean_ctor_get_uint8(x_4, sizeof(void*)*3 + 1);
x_11 = lean_ctor_get_uint8(x_4, sizeof(void*)*3 + 2);
x_12 = lean_ctor_get(x_4, 2);
lean_inc(x_12);
lean_dec(x_4);
x_13 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set_uint8(x_13, sizeof(void*)*3, x_9);
lean_ctor_set_uint8(x_13, sizeof(void*)*3 + 1, x_10);
lean_ctor_set_uint8(x_13, sizeof(void*)*3 + 2, x_11);
x_14 = lean_st_ref_set(x_1, x_13, x_5);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
x_17 = lean_box(0);
lean_ctor_set(x_14, 0, x_17);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___Lean_PrettyPrinter_Formatter_visitArgs_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Syntax_MonadTraverser_goLeft___at___Lean_PrettyPrinter_Formatter_visitArgs_spec__1___redArg(x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___Lean_PrettyPrinter_Formatter_visitArgs_spec__2___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_st_ref_get(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
lean_ctor_set(x_3, 0, x_7);
return x_3;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_3);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___Lean_PrettyPrinter_Formatter_visitArgs_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Syntax_MonadTraverser_getCur___at___Lean_PrettyPrinter_Formatter_visitArgs_spec__2___redArg(x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goDown___at___Lean_PrettyPrinter_Formatter_visitArgs_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_4 = lean_st_ref_take(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = l_Lean_Syntax_Traverser_down(x_7, x_1);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
x_10 = lean_ctor_get_uint8(x_5, sizeof(void*)*3);
x_11 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 1);
x_12 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 2);
x_13 = lean_ctor_get(x_5, 2);
lean_inc(x_13);
lean_dec(x_5);
x_14 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_9);
lean_ctor_set(x_14, 2, x_13);
lean_ctor_set_uint8(x_14, sizeof(void*)*3, x_10);
lean_ctor_set_uint8(x_14, sizeof(void*)*3 + 1, x_11);
lean_ctor_set_uint8(x_14, sizeof(void*)*3 + 2, x_12);
x_15 = lean_st_ref_set(x_2, x_14, x_6);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
x_18 = lean_box(0);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goDown___at___Lean_PrettyPrinter_Formatter_visitArgs_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Syntax_MonadTraverser_goDown___at___Lean_PrettyPrinter_Formatter_visitArgs_spec__3___redArg(x_1, x_3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_visitArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_7 = l_Lean_Syntax_MonadTraverser_getCur___at___Lean_PrettyPrinter_Formatter_visitArgs_spec__2___redArg(x_3, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Syntax_getArgs(x_8);
lean_dec(x_8);
x_11 = lean_array_get_size(x_10);
lean_dec(x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_11, x_12);
lean_dec(x_11);
x_14 = l_Lean_Syntax_MonadTraverser_goDown___at___Lean_PrettyPrinter_Formatter_visitArgs_spec__3___redArg(x_13, x_3, x_9);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
lean_inc(x_3);
x_16 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Lean_Syntax_MonadTraverser_goUp___at___Lean_PrettyPrinter_Formatter_visitArgs_spec__0___redArg(x_3, x_17);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = l_Lean_Syntax_MonadTraverser_goLeft___at___Lean_PrettyPrinter_Formatter_visitArgs_spec__1___redArg(x_3, x_19);
lean_dec(x_3);
return x_20;
}
else
{
lean_dec(x_3);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goUp___at___Lean_PrettyPrinter_Formatter_visitArgs_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_MonadTraverser_goUp___at___Lean_PrettyPrinter_Formatter_visitArgs_spec__0___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goUp___at___Lean_PrettyPrinter_Formatter_visitArgs_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Syntax_MonadTraverser_goUp___at___Lean_PrettyPrinter_Formatter_visitArgs_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___Lean_PrettyPrinter_Formatter_visitArgs_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_MonadTraverser_goLeft___at___Lean_PrettyPrinter_Formatter_visitArgs_spec__1___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___Lean_PrettyPrinter_Formatter_visitArgs_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Syntax_MonadTraverser_goLeft___at___Lean_PrettyPrinter_Formatter_visitArgs_spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___Lean_PrettyPrinter_Formatter_visitArgs_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_MonadTraverser_getCur___at___Lean_PrettyPrinter_Formatter_visitArgs_spec__2___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___Lean_PrettyPrinter_Formatter_visitArgs_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Syntax_MonadTraverser_getCur___at___Lean_PrettyPrinter_Formatter_visitArgs_spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goDown___at___Lean_PrettyPrinter_Formatter_visitArgs_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Syntax_MonadTraverser_goDown___at___Lean_PrettyPrinter_Formatter_visitArgs_spec__3___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goDown___at___Lean_PrettyPrinter_Formatter_visitArgs_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Syntax_MonadTraverser_goDown___at___Lean_PrettyPrinter_Formatter_visitArgs_spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_fold(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = l_Lean_PrettyPrinter_Formatter_getStackSize___redArg(x_4, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_4);
x_11 = lean_apply_5(x_2, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_PrettyPrinter_Formatter_getStack___redArg(x_4, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_array_get_size(x_14);
lean_inc(x_9);
x_17 = l_Array_extract(lean_box(0), x_14, x_9, x_16);
x_18 = lean_apply_1(x_1, x_17);
x_19 = l_Array_shrink___redArg(x_14, x_9);
lean_dec(x_9);
x_20 = lean_array_push(x_19, x_18);
x_21 = l_Lean_PrettyPrinter_Formatter_setStack___redArg(x_20, x_4, x_15);
lean_dec(x_4);
return x_21;
}
else
{
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_1);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_PrettyPrinter_Formatter_concat_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_2, x_3);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_uget(x_1, x_2);
x_13 = l_Std_Format_isNil(x_4);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_4);
x_5 = x_14;
goto block_10;
}
else
{
lean_dec(x_4);
x_5 = x_12;
goto block_10;
}
}
else
{
return x_4;
}
block_10:
{
lean_object* x_6; size_t x_7; size_t x_8; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_usize_of_nat(x_6);
x_8 = lean_usize_add(x_2, x_7);
x_2 = x_8;
x_4 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_concat___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_box(0);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
lean_dec(x_4);
return x_2;
}
else
{
uint8_t x_6; 
x_6 = lean_nat_dec_le(x_4, x_4);
if (x_6 == 0)
{
lean_dec(x_4);
return x_2;
}
else
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_usize_of_nat(x_3);
x_8 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_9 = l_Array_foldlMUnsafe_fold___at___Lean_PrettyPrinter_Formatter_concat_spec__0(x_1, x_7, x_8, x_2);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_concat(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_concat___lam__0___boxed), 1, 0);
x_8 = l_Lean_PrettyPrinter_Formatter_fold(x_7, x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_PrettyPrinter_Formatter_concat_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Lean_PrettyPrinter_Formatter_concat_spec__0(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_concat___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Formatter_concat___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_indent(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_24; 
lean_inc(x_4);
lean_inc(x_3);
x_24 = l_Lean_PrettyPrinter_Formatter_concat(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_3, 0);
lean_inc(x_63);
lean_dec(x_3);
x_64 = l_Std_Format_getIndent(x_63);
lean_dec(x_63);
x_65 = lean_nat_to_int(x_64);
x_26 = x_65;
goto block_62;
}
else
{
lean_object* x_66; 
lean_dec(x_3);
x_66 = lean_ctor_get(x_2, 0);
lean_inc(x_66);
lean_dec(x_2);
x_26 = x_66;
goto block_62;
}
block_62:
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_st_ref_take(x_4, x_25);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_27, 1);
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
x_33 = lean_ctor_get_uint8(x_29, sizeof(void*)*3);
x_34 = lean_ctor_get_uint8(x_29, sizeof(void*)*3 + 1);
x_35 = lean_ctor_get_uint8(x_29, sizeof(void*)*3 + 2);
x_36 = lean_ctor_get(x_29, 2);
lean_inc(x_36);
lean_dec(x_29);
x_37 = lean_array_get_size(x_36);
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_nat_sub(x_37, x_38);
x_40 = lean_nat_dec_lt(x_39, x_37);
lean_dec(x_37);
if (x_40 == 0)
{
lean_dec(x_39);
lean_free_object(x_27);
lean_dec(x_26);
x_8 = x_31;
x_9 = x_34;
x_10 = x_30;
x_11 = x_33;
x_12 = x_35;
x_13 = x_32;
x_14 = x_36;
goto block_23;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_array_fget(x_36, x_39);
x_42 = lean_box(0);
x_43 = lean_array_fset(x_36, x_39, x_42);
lean_ctor_set_tag(x_27, 4);
lean_ctor_set(x_27, 1, x_41);
lean_ctor_set(x_27, 0, x_26);
x_44 = lean_array_fset(x_43, x_39, x_27);
lean_dec(x_39);
x_8 = x_31;
x_9 = x_34;
x_10 = x_30;
x_11 = x_33;
x_12 = x_35;
x_13 = x_32;
x_14 = x_44;
goto block_23;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_45 = lean_ctor_get(x_27, 0);
x_46 = lean_ctor_get(x_27, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_27);
x_47 = lean_ctor_get(x_45, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
x_49 = lean_ctor_get_uint8(x_45, sizeof(void*)*3);
x_50 = lean_ctor_get_uint8(x_45, sizeof(void*)*3 + 1);
x_51 = lean_ctor_get_uint8(x_45, sizeof(void*)*3 + 2);
x_52 = lean_ctor_get(x_45, 2);
lean_inc(x_52);
lean_dec(x_45);
x_53 = lean_array_get_size(x_52);
x_54 = lean_unsigned_to_nat(1u);
x_55 = lean_nat_sub(x_53, x_54);
x_56 = lean_nat_dec_lt(x_55, x_53);
lean_dec(x_53);
if (x_56 == 0)
{
lean_dec(x_55);
lean_dec(x_26);
x_8 = x_47;
x_9 = x_50;
x_10 = x_46;
x_11 = x_49;
x_12 = x_51;
x_13 = x_48;
x_14 = x_52;
goto block_23;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_57 = lean_array_fget(x_52, x_55);
x_58 = lean_box(0);
x_59 = lean_array_fset(x_52, x_55, x_58);
x_60 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_60, 0, x_26);
lean_ctor_set(x_60, 1, x_57);
x_61 = lean_array_fset(x_59, x_55, x_60);
lean_dec(x_55);
x_8 = x_47;
x_9 = x_50;
x_10 = x_46;
x_11 = x_49;
x_12 = x_51;
x_13 = x_48;
x_14 = x_61;
goto block_23;
}
}
}
}
else
{
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_24;
}
block_23:
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_13);
lean_ctor_set(x_15, 2, x_14);
lean_ctor_set_uint8(x_15, sizeof(void*)*3, x_11);
lean_ctor_set_uint8(x_15, sizeof(void*)*3 + 1, x_9);
lean_ctor_set_uint8(x_15, sizeof(void*)*3 + 2, x_12);
x_16 = lean_st_ref_set(x_4, x_15, x_10);
lean_dec(x_4);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
x_19 = lean_box(0);
lean_ctor_set(x_16, 0, x_19);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_fill(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_3);
x_7 = l_Lean_PrettyPrinter_Formatter_concat(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_st_ref_take(x_3, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
x_14 = lean_ctor_get_uint8(x_10, sizeof(void*)*3);
x_15 = lean_box(0);
x_16 = lean_ctor_get_uint8(x_10, sizeof(void*)*3 + 2);
x_28 = lean_ctor_get(x_10, 2);
lean_inc(x_28);
lean_dec(x_10);
x_29 = lean_array_get_size(x_28);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_sub(x_29, x_30);
x_32 = lean_nat_dec_lt(x_31, x_29);
lean_dec(x_29);
if (x_32 == 0)
{
lean_dec(x_31);
x_17 = x_28;
goto block_27;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_array_fget(x_28, x_31);
x_34 = lean_box(0);
x_35 = lean_array_fset(x_28, x_31, x_34);
x_36 = l_Std_Format_fill(x_33);
x_37 = lean_array_fset(x_35, x_31, x_36);
lean_dec(x_31);
x_17 = x_37;
goto block_27;
}
block_27:
{
lean_object* x_18; uint8_t x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_13);
lean_ctor_set(x_18, 2, x_17);
lean_ctor_set_uint8(x_18, sizeof(void*)*3, x_14);
x_19 = lean_unbox(x_15);
lean_ctor_set_uint8(x_18, sizeof(void*)*3 + 1, x_19);
lean_ctor_set_uint8(x_18, sizeof(void*)*3 + 2, x_16);
x_20 = lean_st_ref_set(x_3, x_18, x_11);
lean_dec(x_3);
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
}
else
{
lean_dec(x_3);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_group(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_3);
x_7 = l_Lean_PrettyPrinter_Formatter_concat(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_st_ref_take(x_3, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
x_14 = lean_ctor_get_uint8(x_10, sizeof(void*)*3);
x_15 = lean_box(0);
x_16 = lean_ctor_get_uint8(x_10, sizeof(void*)*3 + 2);
x_28 = lean_ctor_get(x_10, 2);
lean_inc(x_28);
lean_dec(x_10);
x_29 = lean_array_get_size(x_28);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_sub(x_29, x_30);
x_32 = lean_nat_dec_lt(x_31, x_29);
lean_dec(x_29);
if (x_32 == 0)
{
lean_dec(x_31);
x_17 = x_28;
goto block_27;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; 
x_33 = lean_array_fget(x_28, x_31);
x_34 = lean_box(0);
x_35 = lean_array_fset(x_28, x_31, x_34);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_37, 0, x_33);
x_38 = lean_unbox(x_36);
lean_ctor_set_uint8(x_37, sizeof(void*)*1, x_38);
x_39 = lean_array_fset(x_35, x_31, x_37);
lean_dec(x_31);
x_17 = x_39;
goto block_27;
}
block_27:
{
lean_object* x_18; uint8_t x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_13);
lean_ctor_set(x_18, 2, x_17);
lean_ctor_set_uint8(x_18, sizeof(void*)*3, x_14);
x_19 = lean_unbox(x_15);
lean_ctor_set_uint8(x_18, sizeof(void*)*3 + 1, x_19);
lean_ctor_set_uint8(x_18, sizeof(void*)*3 + 2, x_16);
x_20 = lean_st_ref_set(x_3, x_18, x_11);
lean_dec(x_3);
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
}
else
{
lean_dec(x_3);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_withMaybeTag(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_8; 
x_8 = lean_apply_5(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_10 = l_Lean_PrettyPrinter_Formatter_concat(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_st_ref_take(x_4, x_11);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
x_18 = lean_ctor_get_uint8(x_14, sizeof(void*)*3);
x_19 = lean_ctor_get_uint8(x_14, sizeof(void*)*3 + 1);
x_20 = lean_ctor_get_uint8(x_14, sizeof(void*)*3 + 2);
x_31 = lean_ctor_get(x_14, 2);
lean_inc(x_31);
lean_dec(x_14);
x_32 = lean_array_get_size(x_31);
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_nat_sub(x_32, x_33);
x_35 = lean_nat_dec_lt(x_34, x_32);
lean_dec(x_32);
if (x_35 == 0)
{
lean_dec(x_34);
lean_free_object(x_12);
x_21 = x_31;
goto block_30;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_array_fget(x_31, x_34);
x_37 = lean_box(0);
x_38 = lean_array_fset(x_31, x_34, x_37);
if (lean_obj_tag(x_36) == 7)
{
lean_free_object(x_12);
x_39 = x_36;
goto block_41;
}
else
{
lean_inc(x_9);
lean_ctor_set_tag(x_12, 7);
lean_ctor_set(x_12, 1, x_36);
lean_ctor_set(x_12, 0, x_9);
x_39 = x_12;
goto block_41;
}
block_41:
{
lean_object* x_40; 
x_40 = lean_array_fset(x_38, x_34, x_39);
lean_dec(x_34);
x_21 = x_40;
goto block_30;
}
}
block_30:
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_22, 0, x_16);
lean_ctor_set(x_22, 1, x_17);
lean_ctor_set(x_22, 2, x_21);
lean_ctor_set_uint8(x_22, sizeof(void*)*3, x_18);
lean_ctor_set_uint8(x_22, sizeof(void*)*3 + 1, x_19);
lean_ctor_set_uint8(x_22, sizeof(void*)*3 + 2, x_20);
x_23 = lean_st_ref_set(x_4, x_22, x_15);
lean_dec(x_4);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
x_26 = lean_box(0);
lean_ctor_set(x_23, 0, x_26);
return x_23;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
lean_dec(x_23);
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
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; lean_object* x_49; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_42 = lean_ctor_get(x_12, 0);
x_43 = lean_ctor_get(x_12, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_12);
x_44 = lean_ctor_get(x_42, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
x_46 = lean_ctor_get_uint8(x_42, sizeof(void*)*3);
x_47 = lean_ctor_get_uint8(x_42, sizeof(void*)*3 + 1);
x_48 = lean_ctor_get_uint8(x_42, sizeof(void*)*3 + 2);
x_57 = lean_ctor_get(x_42, 2);
lean_inc(x_57);
lean_dec(x_42);
x_58 = lean_array_get_size(x_57);
x_59 = lean_unsigned_to_nat(1u);
x_60 = lean_nat_sub(x_58, x_59);
x_61 = lean_nat_dec_lt(x_60, x_58);
lean_dec(x_58);
if (x_61 == 0)
{
lean_dec(x_60);
x_49 = x_57;
goto block_56;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_62 = lean_array_fget(x_57, x_60);
x_63 = lean_box(0);
x_64 = lean_array_fset(x_57, x_60, x_63);
if (lean_obj_tag(x_62) == 7)
{
x_65 = x_62;
goto block_67;
}
else
{
lean_object* x_68; 
lean_inc(x_9);
x_68 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_68, 0, x_9);
lean_ctor_set(x_68, 1, x_62);
x_65 = x_68;
goto block_67;
}
block_67:
{
lean_object* x_66; 
x_66 = lean_array_fset(x_64, x_60, x_65);
lean_dec(x_60);
x_49 = x_66;
goto block_56;
}
}
block_56:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_50 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_50, 0, x_44);
lean_ctor_set(x_50, 1, x_45);
lean_ctor_set(x_50, 2, x_49);
lean_ctor_set_uint8(x_50, sizeof(void*)*3, x_46);
lean_ctor_set_uint8(x_50, sizeof(void*)*3 + 1, x_47);
lean_ctor_set_uint8(x_50, sizeof(void*)*3 + 2, x_48);
x_51 = lean_st_ref_set(x_4, x_50, x_43);
lean_dec(x_4);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_53 = x_51;
} else {
 lean_dec_ref(x_51);
 x_53 = lean_box(0);
}
x_54 = lean_box(0);
if (lean_is_scalar(x_53)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_53;
}
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_52);
return x_55;
}
}
}
else
{
lean_dec(x_4);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_withMaybeTag___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Formatter_withMaybeTag(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_orelse_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_8 = l_Lean_Syntax_MonadTraverser_getCur___at___Lean_PrettyPrinter_Formatter_visitArgs_spec__2___redArg(x_4, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Syntax_getKind(x_9);
x_12 = lean_mk_string_unchecked("choice", 6, 6);
x_13 = l_Lean_Name_mkStr1(x_12);
x_14 = lean_name_eq(x_11, x_13);
lean_dec(x_13);
lean_dec(x_11);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_st_ref_get(x_4, x_10);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_18 = lean_apply_5(x_1, x_3, x_4, x_5, x_6, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_29; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
x_21 = l_Lean_PrettyPrinter_backtrackExceptionId;
x_29 = l_Lean_Exception_isInterrupt(x_19);
if (x_29 == 0)
{
uint8_t x_30; 
x_30 = l_Lean_Exception_isRuntime(x_19);
x_22 = x_30;
goto block_28;
}
else
{
x_22 = x_29;
goto block_28;
}
block_28:
{
if (x_22 == 0)
{
if (lean_obj_tag(x_19) == 0)
{
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_18;
}
else
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_19, 0);
lean_inc(x_23);
lean_dec(x_19);
x_24 = l___private_Lean_InternalExceptionId_0__Lean_beqInternalExceptionId____x40_Lean_InternalExceptionId___hyg_26_(x_21, x_23);
lean_dec(x_23);
if (x_24 == 0)
{
lean_dec(x_20);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_18;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_18);
x_25 = lean_st_ref_set(x_4, x_16, x_20);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_apply_5(x_2, x_3, x_4, x_5, x_6, x_26);
return x_27;
}
}
}
else
{
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_18;
}
}
}
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter), 7, 2);
lean_closure_set(x_31, 0, x_1);
lean_closure_set(x_31, 1, x_2);
x_32 = l_Lean_PrettyPrinter_Formatter_visitArgs(x_31, x_3, x_4, x_5, x_6, x_10);
return x_32;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_recover_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_recover_x27_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_mkAntiquot_formatter_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = lean_mk_antiquot_formatter(x_1, x_2, x_10, x_11, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_pretty_printer_formatter_interpret_parser_descr(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Formatter_0__Lean_PrettyPrinter_Formatter_SourceInfo_getExprPos_x3f(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Formatter_0__Lean_PrettyPrinter_Formatter_SourceInfo_getExprPos_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_PrettyPrinter_Formatter_0__Lean_PrettyPrinter_Formatter_SourceInfo_getExprPos_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Formatter_0__Lean_PrettyPrinter_Formatter_getExprPos_x3f(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = l___private_Lean_PrettyPrinter_Formatter_0__Lean_PrettyPrinter_Formatter_SourceInfo_getExprPos_x3f(x_3);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Formatter_0__Lean_PrettyPrinter_Formatter_getExprPos_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_PrettyPrinter_Formatter_0__Lean_PrettyPrinter_Formatter_getExprPos_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_formatterForKindUnsafe(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_mk_string_unchecked("missing", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_name_eq(x_1, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = l_Lean_Syntax_MonadTraverser_getCur___at___Lean_PrettyPrinter_Formatter_visitArgs_spec__2___redArg(x_3, x_6);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_PrettyPrinter_formatterAttribute;
x_14 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_interpretParserDescr_x27___boxed), 4, 0);
lean_inc(x_5);
lean_inc(x_4);
x_15 = l_Lean_PrettyPrinter_runForNodeKind___redArg(x_13, x_1, x_14, x_4, x_5, x_12);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l___private_Lean_PrettyPrinter_Formatter_0__Lean_PrettyPrinter_Formatter_getExprPos_x3f(x_11);
lean_dec(x_11);
x_19 = l_Lean_PrettyPrinter_Formatter_withMaybeTag(x_18, x_16, x_2, x_3, x_4, x_5, x_17);
lean_dec(x_18);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_20 = !lean_is_exclusive(x_15);
if (x_20 == 0)
{
return x_15;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_15, 0);
x_22 = lean_ctor_get(x_15, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_15);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_24 = lean_mk_string_unchecked("<missing>", 9, 9);
x_25 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = l___private_Lean_PrettyPrinter_Formatter_0__Lean_PrettyPrinter_Formatter_push___redArg(x_25, x_3, x_6);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = l_Lean_Syntax_MonadTraverser_goLeft___at___Lean_PrettyPrinter_Formatter_visitArgs_spec__1___redArg(x_3, x_27);
lean_dec(x_3);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_withAntiquot_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_withAntiquotSuffixSplice_formatter___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_8 = lean_apply_5(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_apply_5(x_2, x_3, x_4, x_5, x_6, x_9);
return x_10;
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_withAntiquotSuffixSplice_formatter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = l_Lean_Syntax_MonadTraverser_getCur___at___Lean_PrettyPrinter_Formatter_visitArgs_spec__2___redArg(x_4, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Syntax_isAntiquotSuffixSplice(x_9);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_2);
x_12 = lean_apply_5(x_1, x_3, x_4, x_5, x_6, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_withAntiquotSuffixSplice_formatter___redArg___lam__0), 7, 2);
lean_closure_set(x_13, 0, x_2);
lean_closure_set(x_13, 1, x_1);
x_14 = l_Lean_PrettyPrinter_Formatter_visitArgs(x_13, x_3, x_4, x_5, x_6, x_10);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_withAntiquotSuffixSplice_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PrettyPrinter_Formatter_withAntiquotSuffixSplice_formatter___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_withAntiquotSuffixSplice_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PrettyPrinter_Formatter_withAntiquotSuffixSplice_formatter(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_tokenWithAntiquot_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = l_Lean_Syntax_MonadTraverser_getCur___at___Lean_PrettyPrinter_Formatter_visitArgs_spec__2___redArg(x_3, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Syntax_isTokenAntiquot(x_8);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_9);
return x_11;
}
else
{
lean_object* x_12; 
x_12 = l_Lean_PrettyPrinter_Formatter_visitArgs(x_1, x_2, x_3, x_4, x_5, x_9);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_PrettyPrinter_Formatter_categoryFormatterCore_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_PrettyPrinter_Formatter_categoryFormatterCore_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_isTracingEnabledFor___at___Lean_PrettyPrinter_Formatter_categoryFormatterCore_spec__0___redArg(x_1, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_PrettyPrinter_Formatter_categoryFormatterCore_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0(x_2, x_3, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_st_ref_take(x_4, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint64_t x_18; lean_object* x_19; lean_object* x_20; double x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_ctor_get(x_3, 5);
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_11, 2);
lean_inc(x_16);
x_17 = lean_ctor_get(x_11, 3);
lean_inc(x_17);
x_18 = lean_ctor_get_uint64(x_17, sizeof(void*)*1);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_float_of_nat(x_20);
x_22 = lean_box(0);
x_23 = lean_mk_string_unchecked("", 0, 0);
x_24 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set_float(x_24, sizeof(void*)*2, x_21);
lean_ctor_set_float(x_24, sizeof(void*)*2 + 8, x_21);
x_25 = lean_unbox(x_22);
lean_ctor_set_uint8(x_24, sizeof(void*)*2 + 16, x_25);
x_26 = lean_mk_empty_array_with_capacity(x_20);
x_27 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_7);
lean_ctor_set(x_27, 2, x_26);
lean_inc(x_13);
lean_ctor_set(x_9, 1, x_27);
lean_ctor_set(x_9, 0, x_13);
x_28 = l_Lean_PersistentArray_push___redArg(x_19, x_9);
x_29 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set_uint64(x_29, sizeof(void*)*1, x_18);
x_30 = lean_ctor_get(x_11, 4);
lean_inc(x_30);
x_31 = lean_ctor_get(x_11, 5);
lean_inc(x_31);
x_32 = lean_ctor_get(x_11, 6);
lean_inc(x_32);
x_33 = lean_ctor_get(x_11, 7);
lean_inc(x_33);
lean_dec(x_11);
x_34 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_34, 0, x_14);
lean_ctor_set(x_34, 1, x_15);
lean_ctor_set(x_34, 2, x_16);
lean_ctor_set(x_34, 3, x_29);
lean_ctor_set(x_34, 4, x_30);
lean_ctor_set(x_34, 5, x_31);
lean_ctor_set(x_34, 6, x_32);
lean_ctor_set(x_34, 7, x_33);
x_35 = lean_st_ref_set(x_4, x_34, x_12);
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
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint64_t x_49; lean_object* x_50; lean_object* x_51; double x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_42 = lean_ctor_get(x_9, 0);
x_43 = lean_ctor_get(x_9, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_9);
x_44 = lean_ctor_get(x_3, 5);
x_45 = lean_ctor_get(x_42, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_42, 1);
lean_inc(x_46);
x_47 = lean_ctor_get(x_42, 2);
lean_inc(x_47);
x_48 = lean_ctor_get(x_42, 3);
lean_inc(x_48);
x_49 = lean_ctor_get_uint64(x_48, sizeof(void*)*1);
x_50 = lean_ctor_get(x_48, 0);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_unsigned_to_nat(0u);
x_52 = lean_float_of_nat(x_51);
x_53 = lean_box(0);
x_54 = lean_mk_string_unchecked("", 0, 0);
x_55 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_55, 0, x_1);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set_float(x_55, sizeof(void*)*2, x_52);
lean_ctor_set_float(x_55, sizeof(void*)*2 + 8, x_52);
x_56 = lean_unbox(x_53);
lean_ctor_set_uint8(x_55, sizeof(void*)*2 + 16, x_56);
x_57 = lean_mk_empty_array_with_capacity(x_51);
x_58 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_7);
lean_ctor_set(x_58, 2, x_57);
lean_inc(x_44);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_44);
lean_ctor_set(x_59, 1, x_58);
x_60 = l_Lean_PersistentArray_push___redArg(x_50, x_59);
x_61 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set_uint64(x_61, sizeof(void*)*1, x_49);
x_62 = lean_ctor_get(x_42, 4);
lean_inc(x_62);
x_63 = lean_ctor_get(x_42, 5);
lean_inc(x_63);
x_64 = lean_ctor_get(x_42, 6);
lean_inc(x_64);
x_65 = lean_ctor_get(x_42, 7);
lean_inc(x_65);
lean_dec(x_42);
x_66 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_66, 0, x_45);
lean_ctor_set(x_66, 1, x_46);
lean_ctor_set(x_66, 2, x_47);
lean_ctor_set(x_66, 3, x_61);
lean_ctor_set(x_66, 4, x_62);
lean_ctor_set(x_66, 5, x_63);
lean_ctor_set(x_66, 6, x_64);
lean_ctor_set(x_66, 7, x_65);
x_67 = lean_st_ref_set(x_4, x_66, x_43);
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_69 = x_67;
} else {
 lean_dec_ref(x_67);
 x_69 = lean_box(0);
}
x_70 = lean_box(0);
if (lean_is_scalar(x_69)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_69;
}
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_68);
return x_71;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_PrettyPrinter_Formatter_categoryFormatterCore_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_addTrace___at___Lean_PrettyPrinter_Formatter_categoryFormatterCore_spec__1___redArg(x_1, x_2, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = l_Lean_Syntax_MonadTraverser_getCur___at___Lean_PrettyPrinter_Formatter_visitArgs_spec__2___redArg(x_2, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_Syntax_getKind(x_7);
x_10 = l_Lean_PrettyPrinter_Formatter_formatterForKindUnsafe(x_9, x_1, x_2, x_3, x_4, x_8);
return x_10;
}
}
LEAN_EXPORT uint8_t l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___lam__1(uint8_t x_1, lean_object* x_2) {
_start:
{
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l___private_Lean_PrettyPrinter_Formatter_0__Lean_PrettyPrinter_Formatter_push___redArg(x_1, x_3, x_6);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_Syntax_MonadTraverser_goLeft___at___Lean_PrettyPrinter_Formatter_visitArgs_spec__1___redArg(x_3, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_categoryFormatterCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_25; lean_object* x_26; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_43 = lean_st_ref_take(x_3, x_6);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_ctor_get(x_44, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
x_48 = lean_ctor_get_uint8(x_44, sizeof(void*)*3);
x_49 = lean_box(0);
x_50 = lean_box(1);
x_51 = lean_ctor_get(x_44, 2);
lean_inc(x_51);
lean_dec(x_44);
x_52 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_52, 0, x_46);
lean_ctor_set(x_52, 1, x_47);
lean_ctor_set(x_52, 2, x_51);
lean_ctor_set_uint8(x_52, sizeof(void*)*3, x_48);
x_53 = lean_unbox(x_49);
lean_ctor_set_uint8(x_52, sizeof(void*)*3 + 1, x_53);
x_54 = lean_unbox(x_50);
lean_ctor_set_uint8(x_52, sizeof(void*)*3 + 2, x_54);
x_55 = lean_st_ref_set(x_3, x_52, x_45);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
x_57 = l_Lean_Syntax_MonadTraverser_getCur___at___Lean_PrettyPrinter_Formatter_visitArgs_spec__2___redArg(x_3, x_56);
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_59 = lean_ctor_get(x_57, 0);
x_60 = lean_ctor_get(x_57, 1);
x_61 = lean_mk_string_unchecked("PrettyPrinter", 13, 13);
x_62 = lean_mk_string_unchecked("format", 6, 6);
x_63 = l_Lean_Name_mkStr2(x_61, x_62);
lean_inc(x_63);
x_64 = l_Lean_isTracingEnabledFor___at___Lean_PrettyPrinter_Formatter_categoryFormatterCore_spec__0___redArg(x_63, x_4, x_60);
x_65 = !lean_is_exclusive(x_64);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_102; 
x_66 = lean_ctor_get(x_64, 0);
x_67 = lean_ctor_get(x_64, 1);
x_68 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___lam__0), 5, 0);
x_102 = lean_unbox(x_66);
lean_dec(x_66);
if (x_102 == 0)
{
lean_free_object(x_64);
lean_dec(x_63);
lean_free_object(x_57);
x_69 = x_2;
x_70 = x_3;
x_71 = x_4;
x_72 = x_5;
x_73 = x_67;
goto block_101;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_103 = lean_mk_string_unchecked("formatting ", 11, 11);
x_104 = l_Lean_stringToMessageData(x_103);
lean_dec(x_103);
x_105 = lean_box(0);
x_106 = lean_unbox(x_49);
lean_inc(x_59);
x_107 = l_Lean_Syntax_formatStx(x_59, x_105, x_106);
x_108 = l_Lean_MessageData_ofFormat(x_107);
x_109 = l_Lean_indentD(x_108);
lean_ctor_set_tag(x_64, 7);
lean_ctor_set(x_64, 1, x_109);
lean_ctor_set(x_64, 0, x_104);
x_110 = lean_mk_string_unchecked("", 0, 0);
x_111 = l_Lean_stringToMessageData(x_110);
lean_dec(x_110);
lean_ctor_set_tag(x_57, 7);
lean_ctor_set(x_57, 1, x_111);
lean_ctor_set(x_57, 0, x_64);
x_112 = l_Lean_addTrace___at___Lean_PrettyPrinter_Formatter_categoryFormatterCore_spec__1___redArg(x_63, x_57, x_4, x_5, x_67);
x_113 = lean_ctor_get(x_112, 1);
lean_inc(x_113);
lean_dec(x_112);
x_69 = x_2;
x_70 = x_3;
x_71 = x_4;
x_72 = x_5;
x_73 = x_113;
goto block_101;
}
block_101:
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
lean_inc(x_59);
x_74 = l_Lean_Syntax_getKind(x_59);
x_75 = lean_mk_string_unchecked("choice", 6, 6);
x_76 = l_Lean_Name_mkStr1(x_75);
x_77 = lean_name_eq(x_74, x_76);
lean_dec(x_76);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; 
lean_dec(x_68);
x_78 = lean_mk_string_unchecked("rawStx", 6, 6);
x_79 = l_Lean_Name_mkStr1(x_78);
x_80 = lean_name_eq(x_1, x_79);
lean_dec(x_79);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_59);
x_81 = lean_box(x_80);
x_82 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___lam__1___boxed), 2, 1);
lean_closure_set(x_82, 0, x_81);
x_83 = lean_unbox(x_50);
lean_inc(x_1);
x_84 = l_Lean_Name_toString(x_1, x_83, x_82);
x_85 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_mkAntiquot_formatter_x27___boxed), 9, 4);
lean_closure_set(x_85, 0, x_84);
lean_closure_set(x_85, 1, x_1);
lean_closure_set(x_85, 2, x_50);
lean_closure_set(x_85, 3, x_50);
x_86 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_formatterForKindUnsafe), 6, 1);
lean_closure_set(x_86, 0, x_74);
lean_inc(x_70);
x_87 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_85, x_86, x_69, x_70, x_71, x_72, x_73);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; 
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
lean_dec(x_87);
x_25 = x_70;
x_26 = x_88;
goto block_42;
}
else
{
lean_dec(x_70);
return x_87;
}
}
else
{
lean_object* x_89; lean_object* x_90; uint8_t x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_74);
x_89 = lean_box(x_77);
x_90 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___lam__1___boxed), 2, 1);
lean_closure_set(x_90, 0, x_89);
x_91 = lean_unbox(x_50);
lean_inc(x_1);
x_92 = l_Lean_Name_toString(x_1, x_91, x_90);
x_93 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_mkAntiquot_formatter_x27___boxed), 9, 4);
lean_closure_set(x_93, 0, x_92);
lean_closure_set(x_93, 1, x_1);
lean_closure_set(x_93, 2, x_50);
lean_closure_set(x_93, 3, x_50);
x_94 = lean_box(0);
x_95 = l_Lean_Syntax_formatStx(x_59, x_94, x_77);
x_96 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___lam__3___boxed), 6, 1);
lean_closure_set(x_96, 0, x_95);
lean_inc(x_70);
x_97 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_93, x_96, x_69, x_70, x_71, x_72, x_73);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; 
x_98 = lean_ctor_get(x_97, 1);
lean_inc(x_98);
lean_dec(x_97);
x_25 = x_70;
x_26 = x_98;
goto block_42;
}
else
{
lean_dec(x_70);
return x_97;
}
}
}
else
{
lean_object* x_99; 
lean_dec(x_74);
lean_dec(x_59);
lean_dec(x_1);
lean_inc(x_70);
x_99 = l_Lean_PrettyPrinter_Formatter_visitArgs(x_68, x_69, x_70, x_71, x_72, x_73);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; 
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
lean_dec(x_99);
x_25 = x_70;
x_26 = x_100;
goto block_42;
}
else
{
lean_dec(x_70);
return x_99;
}
}
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_150; 
x_114 = lean_ctor_get(x_64, 0);
x_115 = lean_ctor_get(x_64, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_64);
x_116 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___lam__0), 5, 0);
x_150 = lean_unbox(x_114);
lean_dec(x_114);
if (x_150 == 0)
{
lean_dec(x_63);
lean_free_object(x_57);
x_117 = x_2;
x_118 = x_3;
x_119 = x_4;
x_120 = x_5;
x_121 = x_115;
goto block_149;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_151 = lean_mk_string_unchecked("formatting ", 11, 11);
x_152 = l_Lean_stringToMessageData(x_151);
lean_dec(x_151);
x_153 = lean_box(0);
x_154 = lean_unbox(x_49);
lean_inc(x_59);
x_155 = l_Lean_Syntax_formatStx(x_59, x_153, x_154);
x_156 = l_Lean_MessageData_ofFormat(x_155);
x_157 = l_Lean_indentD(x_156);
x_158 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_158, 0, x_152);
lean_ctor_set(x_158, 1, x_157);
x_159 = lean_mk_string_unchecked("", 0, 0);
x_160 = l_Lean_stringToMessageData(x_159);
lean_dec(x_159);
lean_ctor_set_tag(x_57, 7);
lean_ctor_set(x_57, 1, x_160);
lean_ctor_set(x_57, 0, x_158);
x_161 = l_Lean_addTrace___at___Lean_PrettyPrinter_Formatter_categoryFormatterCore_spec__1___redArg(x_63, x_57, x_4, x_5, x_115);
x_162 = lean_ctor_get(x_161, 1);
lean_inc(x_162);
lean_dec(x_161);
x_117 = x_2;
x_118 = x_3;
x_119 = x_4;
x_120 = x_5;
x_121 = x_162;
goto block_149;
}
block_149:
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; 
lean_inc(x_59);
x_122 = l_Lean_Syntax_getKind(x_59);
x_123 = lean_mk_string_unchecked("choice", 6, 6);
x_124 = l_Lean_Name_mkStr1(x_123);
x_125 = lean_name_eq(x_122, x_124);
lean_dec(x_124);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; uint8_t x_128; 
lean_dec(x_116);
x_126 = lean_mk_string_unchecked("rawStx", 6, 6);
x_127 = l_Lean_Name_mkStr1(x_126);
x_128 = lean_name_eq(x_1, x_127);
lean_dec(x_127);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; uint8_t x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec(x_59);
x_129 = lean_box(x_128);
x_130 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___lam__1___boxed), 2, 1);
lean_closure_set(x_130, 0, x_129);
x_131 = lean_unbox(x_50);
lean_inc(x_1);
x_132 = l_Lean_Name_toString(x_1, x_131, x_130);
x_133 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_mkAntiquot_formatter_x27___boxed), 9, 4);
lean_closure_set(x_133, 0, x_132);
lean_closure_set(x_133, 1, x_1);
lean_closure_set(x_133, 2, x_50);
lean_closure_set(x_133, 3, x_50);
x_134 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_formatterForKindUnsafe), 6, 1);
lean_closure_set(x_134, 0, x_122);
lean_inc(x_118);
x_135 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_133, x_134, x_117, x_118, x_119, x_120, x_121);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; 
x_136 = lean_ctor_get(x_135, 1);
lean_inc(x_136);
lean_dec(x_135);
x_25 = x_118;
x_26 = x_136;
goto block_42;
}
else
{
lean_dec(x_118);
return x_135;
}
}
else
{
lean_object* x_137; lean_object* x_138; uint8_t x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec(x_122);
x_137 = lean_box(x_125);
x_138 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___lam__1___boxed), 2, 1);
lean_closure_set(x_138, 0, x_137);
x_139 = lean_unbox(x_50);
lean_inc(x_1);
x_140 = l_Lean_Name_toString(x_1, x_139, x_138);
x_141 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_mkAntiquot_formatter_x27___boxed), 9, 4);
lean_closure_set(x_141, 0, x_140);
lean_closure_set(x_141, 1, x_1);
lean_closure_set(x_141, 2, x_50);
lean_closure_set(x_141, 3, x_50);
x_142 = lean_box(0);
x_143 = l_Lean_Syntax_formatStx(x_59, x_142, x_125);
x_144 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___lam__3___boxed), 6, 1);
lean_closure_set(x_144, 0, x_143);
lean_inc(x_118);
x_145 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_141, x_144, x_117, x_118, x_119, x_120, x_121);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; 
x_146 = lean_ctor_get(x_145, 1);
lean_inc(x_146);
lean_dec(x_145);
x_25 = x_118;
x_26 = x_146;
goto block_42;
}
else
{
lean_dec(x_118);
return x_145;
}
}
}
else
{
lean_object* x_147; 
lean_dec(x_122);
lean_dec(x_59);
lean_dec(x_1);
lean_inc(x_118);
x_147 = l_Lean_PrettyPrinter_Formatter_visitArgs(x_116, x_117, x_118, x_119, x_120, x_121);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; 
x_148 = lean_ctor_get(x_147, 1);
lean_inc(x_148);
lean_dec(x_147);
x_25 = x_118;
x_26 = x_148;
goto block_42;
}
else
{
lean_dec(x_118);
return x_147;
}
}
}
}
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; uint8_t x_206; 
x_163 = lean_ctor_get(x_57, 0);
x_164 = lean_ctor_get(x_57, 1);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_57);
x_165 = lean_mk_string_unchecked("PrettyPrinter", 13, 13);
x_166 = lean_mk_string_unchecked("format", 6, 6);
x_167 = l_Lean_Name_mkStr2(x_165, x_166);
lean_inc(x_167);
x_168 = l_Lean_isTracingEnabledFor___at___Lean_PrettyPrinter_Formatter_categoryFormatterCore_spec__0___redArg(x_167, x_4, x_164);
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_168, 1);
lean_inc(x_170);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 x_171 = x_168;
} else {
 lean_dec_ref(x_168);
 x_171 = lean_box(0);
}
x_172 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___lam__0), 5, 0);
x_206 = lean_unbox(x_169);
lean_dec(x_169);
if (x_206 == 0)
{
lean_dec(x_171);
lean_dec(x_167);
x_173 = x_2;
x_174 = x_3;
x_175 = x_4;
x_176 = x_5;
x_177 = x_170;
goto block_205;
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; uint8_t x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_207 = lean_mk_string_unchecked("formatting ", 11, 11);
x_208 = l_Lean_stringToMessageData(x_207);
lean_dec(x_207);
x_209 = lean_box(0);
x_210 = lean_unbox(x_49);
lean_inc(x_163);
x_211 = l_Lean_Syntax_formatStx(x_163, x_209, x_210);
x_212 = l_Lean_MessageData_ofFormat(x_211);
x_213 = l_Lean_indentD(x_212);
if (lean_is_scalar(x_171)) {
 x_214 = lean_alloc_ctor(7, 2, 0);
} else {
 x_214 = x_171;
 lean_ctor_set_tag(x_214, 7);
}
lean_ctor_set(x_214, 0, x_208);
lean_ctor_set(x_214, 1, x_213);
x_215 = lean_mk_string_unchecked("", 0, 0);
x_216 = l_Lean_stringToMessageData(x_215);
lean_dec(x_215);
x_217 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_217, 0, x_214);
lean_ctor_set(x_217, 1, x_216);
x_218 = l_Lean_addTrace___at___Lean_PrettyPrinter_Formatter_categoryFormatterCore_spec__1___redArg(x_167, x_217, x_4, x_5, x_170);
x_219 = lean_ctor_get(x_218, 1);
lean_inc(x_219);
lean_dec(x_218);
x_173 = x_2;
x_174 = x_3;
x_175 = x_4;
x_176 = x_5;
x_177 = x_219;
goto block_205;
}
block_205:
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; uint8_t x_181; 
lean_inc(x_163);
x_178 = l_Lean_Syntax_getKind(x_163);
x_179 = lean_mk_string_unchecked("choice", 6, 6);
x_180 = l_Lean_Name_mkStr1(x_179);
x_181 = lean_name_eq(x_178, x_180);
lean_dec(x_180);
if (x_181 == 0)
{
lean_object* x_182; lean_object* x_183; uint8_t x_184; 
lean_dec(x_172);
x_182 = lean_mk_string_unchecked("rawStx", 6, 6);
x_183 = l_Lean_Name_mkStr1(x_182);
x_184 = lean_name_eq(x_1, x_183);
lean_dec(x_183);
if (x_184 == 0)
{
lean_object* x_185; lean_object* x_186; uint8_t x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
lean_dec(x_163);
x_185 = lean_box(x_184);
x_186 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___lam__1___boxed), 2, 1);
lean_closure_set(x_186, 0, x_185);
x_187 = lean_unbox(x_50);
lean_inc(x_1);
x_188 = l_Lean_Name_toString(x_1, x_187, x_186);
x_189 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_mkAntiquot_formatter_x27___boxed), 9, 4);
lean_closure_set(x_189, 0, x_188);
lean_closure_set(x_189, 1, x_1);
lean_closure_set(x_189, 2, x_50);
lean_closure_set(x_189, 3, x_50);
x_190 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_formatterForKindUnsafe), 6, 1);
lean_closure_set(x_190, 0, x_178);
lean_inc(x_174);
x_191 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_189, x_190, x_173, x_174, x_175, x_176, x_177);
if (lean_obj_tag(x_191) == 0)
{
lean_object* x_192; 
x_192 = lean_ctor_get(x_191, 1);
lean_inc(x_192);
lean_dec(x_191);
x_25 = x_174;
x_26 = x_192;
goto block_42;
}
else
{
lean_dec(x_174);
return x_191;
}
}
else
{
lean_object* x_193; lean_object* x_194; uint8_t x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
lean_dec(x_178);
x_193 = lean_box(x_181);
x_194 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___lam__1___boxed), 2, 1);
lean_closure_set(x_194, 0, x_193);
x_195 = lean_unbox(x_50);
lean_inc(x_1);
x_196 = l_Lean_Name_toString(x_1, x_195, x_194);
x_197 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_mkAntiquot_formatter_x27___boxed), 9, 4);
lean_closure_set(x_197, 0, x_196);
lean_closure_set(x_197, 1, x_1);
lean_closure_set(x_197, 2, x_50);
lean_closure_set(x_197, 3, x_50);
x_198 = lean_box(0);
x_199 = l_Lean_Syntax_formatStx(x_163, x_198, x_181);
x_200 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___lam__3___boxed), 6, 1);
lean_closure_set(x_200, 0, x_199);
lean_inc(x_174);
x_201 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_197, x_200, x_173, x_174, x_175, x_176, x_177);
if (lean_obj_tag(x_201) == 0)
{
lean_object* x_202; 
x_202 = lean_ctor_get(x_201, 1);
lean_inc(x_202);
lean_dec(x_201);
x_25 = x_174;
x_26 = x_202;
goto block_42;
}
else
{
lean_dec(x_174);
return x_201;
}
}
}
else
{
lean_object* x_203; 
lean_dec(x_178);
lean_dec(x_163);
lean_dec(x_1);
lean_inc(x_174);
x_203 = l_Lean_PrettyPrinter_Formatter_visitArgs(x_172, x_173, x_174, x_175, x_176, x_177);
if (lean_obj_tag(x_203) == 0)
{
lean_object* x_204; 
x_204 = lean_ctor_get(x_203, 1);
lean_inc(x_204);
lean_dec(x_203);
x_25 = x_174;
x_26 = x_204;
goto block_42;
}
else
{
lean_dec(x_174);
return x_203;
}
}
}
}
block_24:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; uint8_t x_20; 
x_15 = lean_box(1);
x_16 = lean_ctor_get(x_12, 2);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_17, 0, x_13);
lean_ctor_set(x_17, 1, x_7);
lean_ctor_set(x_17, 2, x_16);
lean_ctor_set_uint8(x_17, sizeof(void*)*3, x_10);
lean_ctor_set_uint8(x_17, sizeof(void*)*3 + 1, x_14);
x_18 = lean_unbox(x_15);
lean_ctor_set_uint8(x_17, sizeof(void*)*3 + 2, x_18);
x_19 = lean_st_ref_set(x_8, x_17, x_11);
lean_dec(x_8);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
lean_ctor_set(x_19, 0, x_9);
return x_19;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_9);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
block_42:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_27 = lean_st_ref_take(x_25, x_26);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_box(0);
x_31 = lean_ctor_get_uint8(x_28, sizeof(void*)*3 + 2);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; uint8_t x_36; 
x_32 = lean_ctor_get(x_28, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_28, 1);
lean_inc(x_33);
x_34 = lean_ctor_get_uint8(x_28, sizeof(void*)*3);
x_35 = lean_box(1);
x_36 = lean_unbox(x_35);
x_7 = x_33;
x_8 = x_25;
x_9 = x_30;
x_10 = x_34;
x_11 = x_29;
x_12 = x_28;
x_13 = x_32;
x_14 = x_36;
goto block_24;
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; uint8_t x_41; 
x_37 = lean_ctor_get(x_28, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_28, 1);
lean_inc(x_38);
x_39 = lean_ctor_get_uint8(x_28, sizeof(void*)*3);
x_40 = lean_box(0);
x_41 = lean_unbox(x_40);
x_7 = x_38;
x_8 = x_25;
x_9 = x_30;
x_10 = x_39;
x_11 = x_29;
x_12 = x_28;
x_13 = x_37;
x_14 = x_41;
goto block_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_PrettyPrinter_Formatter_categoryFormatterCore_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isTracingEnabledFor___at___Lean_PrettyPrinter_Formatter_categoryFormatterCore_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_PrettyPrinter_Formatter_categoryFormatterCore_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_isTracingEnabledFor___at___Lean_PrettyPrinter_Formatter_categoryFormatterCore_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_PrettyPrinter_Formatter_categoryFormatterCore_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_addTrace___at___Lean_PrettyPrinter_Formatter_categoryFormatterCore_spec__1___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_PrettyPrinter_Formatter_categoryFormatterCore_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_addTrace___at___Lean_PrettyPrinter_Formatter_categoryFormatterCore_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___lam__1(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___lam__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_categoryParser_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_categoryFormatterCore), 6, 1);
lean_closure_set(x_7, 0, x_1);
lean_inc(x_3);
lean_inc(x_2);
x_8 = l_Lean_PrettyPrinter_Formatter_concat(x_7, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_st_ref_get(x_3, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get_uint8(x_11, sizeof(void*)*3 + 1);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_st_ref_take(x_3, x_13);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; lean_object* x_23; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
x_20 = lean_ctor_get_uint8(x_16, sizeof(void*)*3);
x_21 = lean_ctor_get_uint8(x_16, sizeof(void*)*3 + 1);
x_22 = lean_ctor_get_uint8(x_16, sizeof(void*)*3 + 2);
x_33 = lean_ctor_get(x_16, 2);
lean_inc(x_33);
lean_dec(x_16);
x_34 = lean_array_get_size(x_33);
x_35 = lean_unsigned_to_nat(1u);
x_36 = lean_nat_sub(x_34, x_35);
x_37 = lean_nat_dec_lt(x_36, x_34);
lean_dec(x_34);
if (x_37 == 0)
{
lean_dec(x_36);
lean_free_object(x_14);
lean_dec(x_2);
x_23 = x_33;
goto block_32;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_38 = lean_ctor_get(x_2, 0);
lean_inc(x_38);
lean_dec(x_2);
x_39 = l_Std_Format_getIndent(x_38);
lean_dec(x_38);
x_40 = lean_array_fget(x_33, x_36);
x_41 = lean_box(0);
x_42 = lean_array_fset(x_33, x_36, x_41);
x_43 = lean_nat_to_int(x_39);
lean_ctor_set_tag(x_14, 4);
lean_ctor_set(x_14, 1, x_40);
lean_ctor_set(x_14, 0, x_43);
x_44 = l_Std_Format_fill(x_14);
x_45 = lean_array_fset(x_42, x_36, x_44);
lean_dec(x_36);
x_23 = x_45;
goto block_32;
}
block_32:
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_24, 0, x_18);
lean_ctor_set(x_24, 1, x_19);
lean_ctor_set(x_24, 2, x_23);
lean_ctor_set_uint8(x_24, sizeof(void*)*3, x_20);
lean_ctor_set_uint8(x_24, sizeof(void*)*3 + 1, x_21);
lean_ctor_set_uint8(x_24, sizeof(void*)*3 + 2, x_22);
x_25 = lean_st_ref_set(x_3, x_24, x_17);
lean_dec(x_3);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
x_28 = lean_box(0);
lean_ctor_set(x_25, 0, x_28);
return x_25;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
lean_dec(x_25);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; lean_object* x_53; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_46 = lean_ctor_get(x_14, 0);
x_47 = lean_ctor_get(x_14, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_14);
x_48 = lean_ctor_get(x_46, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
x_50 = lean_ctor_get_uint8(x_46, sizeof(void*)*3);
x_51 = lean_ctor_get_uint8(x_46, sizeof(void*)*3 + 1);
x_52 = lean_ctor_get_uint8(x_46, sizeof(void*)*3 + 2);
x_61 = lean_ctor_get(x_46, 2);
lean_inc(x_61);
lean_dec(x_46);
x_62 = lean_array_get_size(x_61);
x_63 = lean_unsigned_to_nat(1u);
x_64 = lean_nat_sub(x_62, x_63);
x_65 = lean_nat_dec_lt(x_64, x_62);
lean_dec(x_62);
if (x_65 == 0)
{
lean_dec(x_64);
lean_dec(x_2);
x_53 = x_61;
goto block_60;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_66 = lean_ctor_get(x_2, 0);
lean_inc(x_66);
lean_dec(x_2);
x_67 = l_Std_Format_getIndent(x_66);
lean_dec(x_66);
x_68 = lean_array_fget(x_61, x_64);
x_69 = lean_box(0);
x_70 = lean_array_fset(x_61, x_64, x_69);
x_71 = lean_nat_to_int(x_67);
x_72 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_68);
x_73 = l_Std_Format_fill(x_72);
x_74 = lean_array_fset(x_70, x_64, x_73);
lean_dec(x_64);
x_53 = x_74;
goto block_60;
}
block_60:
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_54 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_54, 0, x_48);
lean_ctor_set(x_54, 1, x_49);
lean_ctor_set(x_54, 2, x_53);
lean_ctor_set_uint8(x_54, sizeof(void*)*3, x_50);
lean_ctor_set_uint8(x_54, sizeof(void*)*3 + 1, x_51);
lean_ctor_set_uint8(x_54, sizeof(void*)*3 + 2, x_52);
x_55 = lean_st_ref_set(x_3, x_54, x_47);
lean_dec(x_3);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_57 = x_55;
} else {
 lean_dec_ref(x_55);
 x_57 = lean_box(0);
}
x_58 = lean_box(0);
if (lean_is_scalar(x_57)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_57;
}
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_56);
return x_59;
}
}
}
else
{
uint8_t x_75; 
lean_dec(x_3);
lean_dec(x_2);
x_75 = !lean_is_exclusive(x_10);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_10, 0);
lean_dec(x_76);
x_77 = lean_box(0);
lean_ctor_set(x_10, 0, x_77);
return x_10;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_10, 1);
lean_inc(x_78);
lean_dec(x_10);
x_79 = lean_box(0);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
}
}
else
{
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_categoryFormatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_categoryFormatterCore), 6, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = lean_box(0);
x_9 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_indent), 7, 2);
lean_closure_set(x_9, 0, x_7);
lean_closure_set(x_9, 1, x_8);
x_10 = l_Lean_PrettyPrinter_Formatter_fill(x_9, x_2, x_3, x_4, x_5, x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_parserOfStack_formatter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_7 = lean_st_ref_get(x_3, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_instInhabitedSyntax;
x_11 = l_instInhabitedNat;
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
x_14 = l_Array_back_x21(lean_box(0), x_10, x_13);
lean_dec(x_13);
x_15 = lean_ctor_get(x_12, 2);
lean_inc(x_15);
lean_dec(x_12);
x_16 = l_Array_back_x21(lean_box(0), x_11, x_15);
lean_dec(x_15);
x_17 = lean_nat_sub(x_16, x_1);
lean_dec(x_16);
x_18 = l_Lean_Syntax_getArg(x_14, x_17);
lean_dec(x_17);
lean_dec(x_14);
x_19 = l_Lean_Syntax_getKind(x_18);
x_20 = l_Lean_PrettyPrinter_Formatter_formatterForKindUnsafe(x_19, x_2, x_3, x_4, x_5, x_9);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_parserOfStack_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Formatter_parserOfStack_formatter___redArg(x_1, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_parserOfStack_formatter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Formatter_parserOfStack_formatter___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_parserOfStack_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Formatter_parserOfStack_formatter(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_error_formatter___redArg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_error_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Formatter_error_formatter___redArg(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_error_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Formatter_error_formatter(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_errorAtSavedPos_formatter___redArg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_errorAtSavedPos_formatter(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Formatter_errorAtSavedPos_formatter___redArg(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_errorAtSavedPos_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Lean_PrettyPrinter_Formatter_errorAtSavedPos_formatter(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_lookahead_formatter___redArg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_lookahead_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Formatter_lookahead_formatter___redArg(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_lookahead_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Formatter_lookahead_formatter(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_notFollowedBy_formatter___redArg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_notFollowedBy_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Formatter_notFollowedBy_formatter___redArg(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_notFollowedBy_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Formatter_notFollowedBy_formatter(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_andthen_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_8 = lean_apply_5(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_apply_5(x_1, x_3, x_4, x_5, x_6, x_9);
return x_10;
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkKind___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_Lean_Syntax_MonadTraverser_getCur___at___Lean_PrettyPrinter_Formatter_visitArgs_spec__2___redArg(x_2, x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
x_10 = l_Lean_Syntax_getKind(x_8);
x_11 = lean_name_eq(x_1, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_free_object(x_6);
x_12 = lean_mk_string_unchecked("PrettyPrinter", 13, 13);
x_13 = lean_mk_string_unchecked("format", 6, 6);
x_14 = lean_mk_string_unchecked("backtrack", 9, 9);
x_15 = l_Lean_Name_mkStr3(x_12, x_13, x_14);
lean_inc(x_15);
x_16 = l_Lean_isTracingEnabledFor___at___Lean_PrettyPrinter_Formatter_categoryFormatterCore_spec__0___redArg(x_15, x_3, x_9);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_unbox(x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_1);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = l_Lean_PrettyPrinter_Formatter_throwBacktrack___redArg(x_19);
return x_20;
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_16);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_22 = lean_ctor_get(x_16, 1);
x_23 = lean_ctor_get(x_16, 0);
lean_dec(x_23);
x_24 = lean_mk_string_unchecked("unexpected node kind '", 22, 22);
x_25 = l_Lean_stringToMessageData(x_24);
lean_dec(x_24);
x_26 = l_Lean_MessageData_ofName(x_10);
lean_ctor_set_tag(x_16, 7);
lean_ctor_set(x_16, 1, x_26);
lean_ctor_set(x_16, 0, x_25);
x_27 = lean_mk_string_unchecked("', expected '", 13, 13);
x_28 = l_Lean_stringToMessageData(x_27);
lean_dec(x_27);
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_16);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_MessageData_ofName(x_1);
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_mk_string_unchecked("'", 1, 1);
x_33 = l_Lean_stringToMessageData(x_32);
lean_dec(x_32);
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_33);
x_35 = l_Lean_addTrace___at___Lean_PrettyPrinter_Formatter_categoryFormatterCore_spec__1___redArg(x_15, x_34, x_3, x_4, x_22);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = l_Lean_PrettyPrinter_Formatter_throwBacktrack___redArg(x_36);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_38 = lean_ctor_get(x_16, 1);
lean_inc(x_38);
lean_dec(x_16);
x_39 = lean_mk_string_unchecked("unexpected node kind '", 22, 22);
x_40 = l_Lean_stringToMessageData(x_39);
lean_dec(x_39);
x_41 = l_Lean_MessageData_ofName(x_10);
x_42 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_mk_string_unchecked("', expected '", 13, 13);
x_44 = l_Lean_stringToMessageData(x_43);
lean_dec(x_43);
x_45 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_44);
x_46 = l_Lean_MessageData_ofName(x_1);
x_47 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_mk_string_unchecked("'", 1, 1);
x_49 = l_Lean_stringToMessageData(x_48);
lean_dec(x_48);
x_50 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_49);
x_51 = l_Lean_addTrace___at___Lean_PrettyPrinter_Formatter_categoryFormatterCore_spec__1___redArg(x_15, x_50, x_3, x_4, x_38);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec(x_51);
x_53 = l_Lean_PrettyPrinter_Formatter_throwBacktrack___redArg(x_52);
return x_53;
}
}
}
else
{
lean_object* x_54; 
lean_dec(x_10);
lean_dec(x_1);
x_54 = lean_box(0);
lean_ctor_set(x_6, 0, x_54);
return x_6;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_55 = lean_ctor_get(x_6, 0);
x_56 = lean_ctor_get(x_6, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_6);
x_57 = l_Lean_Syntax_getKind(x_55);
x_58 = lean_name_eq(x_1, x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_59 = lean_mk_string_unchecked("PrettyPrinter", 13, 13);
x_60 = lean_mk_string_unchecked("format", 6, 6);
x_61 = lean_mk_string_unchecked("backtrack", 9, 9);
x_62 = l_Lean_Name_mkStr3(x_59, x_60, x_61);
lean_inc(x_62);
x_63 = l_Lean_isTracingEnabledFor___at___Lean_PrettyPrinter_Formatter_categoryFormatterCore_spec__0___redArg(x_62, x_3, x_56);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_unbox(x_64);
lean_dec(x_64);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; 
lean_dec(x_62);
lean_dec(x_57);
lean_dec(x_1);
x_66 = lean_ctor_get(x_63, 1);
lean_inc(x_66);
lean_dec(x_63);
x_67 = l_Lean_PrettyPrinter_Formatter_throwBacktrack___redArg(x_66);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_68 = lean_ctor_get(x_63, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_69 = x_63;
} else {
 lean_dec_ref(x_63);
 x_69 = lean_box(0);
}
x_70 = lean_mk_string_unchecked("unexpected node kind '", 22, 22);
x_71 = l_Lean_stringToMessageData(x_70);
lean_dec(x_70);
x_72 = l_Lean_MessageData_ofName(x_57);
if (lean_is_scalar(x_69)) {
 x_73 = lean_alloc_ctor(7, 2, 0);
} else {
 x_73 = x_69;
 lean_ctor_set_tag(x_73, 7);
}
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
x_74 = lean_mk_string_unchecked("', expected '", 13, 13);
x_75 = l_Lean_stringToMessageData(x_74);
lean_dec(x_74);
x_76 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set(x_76, 1, x_75);
x_77 = l_Lean_MessageData_ofName(x_1);
x_78 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
x_79 = lean_mk_string_unchecked("'", 1, 1);
x_80 = l_Lean_stringToMessageData(x_79);
lean_dec(x_79);
x_81 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_80);
x_82 = l_Lean_addTrace___at___Lean_PrettyPrinter_Formatter_categoryFormatterCore_spec__1___redArg(x_62, x_81, x_3, x_4, x_68);
x_83 = lean_ctor_get(x_82, 1);
lean_inc(x_83);
lean_dec(x_82);
x_84 = l_Lean_PrettyPrinter_Formatter_throwBacktrack___redArg(x_83);
return x_84;
}
}
else
{
lean_object* x_85; lean_object* x_86; 
lean_dec(x_57);
lean_dec(x_1);
x_85 = lean_box(0);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_56);
return x_86;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkKind(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Formatter_checkKind___redArg(x_1, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkKind___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Formatter_checkKind___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkKind___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Formatter_checkKind(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_node_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Formatter_checkKind___redArg(x_1, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Lean_PrettyPrinter_Formatter_visitArgs(x_2, x_3, x_4, x_5, x_6, x_9);
return x_10;
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_withFn_formatter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_withFn_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_apply_5(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_withFn_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Formatter_withFn_formatter(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_mk_string_unchecked("foo", 3, 3);
x_10 = l_Lean_Name_mkStr1(x_9);
x_11 = l_Lean_PrettyPrinter_Formatter_categoryParser_formatter(x_10, x_2, x_3, x_4, x_5, x_8);
return x_11;
}
else
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Formatter_checkKind___redArg(x_1, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___redArg___lam__0), 6, 1);
lean_closure_set(x_10, 0, x_2);
x_11 = l_Lean_PrettyPrinter_Formatter_visitArgs(x_10, x_3, x_4, x_5, x_6, x_9);
return x_11;
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_trailingNode_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___redArg(x_1, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_PrettyPrinter_Formatter_trailingNode_formatter(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_parseToken___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_st_ref_get(x_4, x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_ctor_get(x_3, 2);
x_11 = lean_alloc_closure((void*)(l_Lean_Parser_whitespace), 2, 0);
x_12 = lean_box(0);
x_13 = lean_alloc_closure((void*)(l_Lean_Parser_tokenFn), 3, 1);
lean_closure_set(x_13, 0, x_12);
x_14 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_14, 0, x_11);
lean_closure_set(x_14, 1, x_13);
x_15 = lean_mk_string_unchecked("", 0, 0);
lean_inc(x_15);
x_16 = l_Lean_FileMap_ofString(x_15);
lean_inc(x_1);
x_17 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_15);
lean_ctor_set(x_17, 2, x_16);
x_18 = lean_box(0);
x_19 = lean_box(0);
lean_inc(x_10);
x_20 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_20, 0, x_9);
lean_ctor_set(x_20, 1, x_10);
lean_ctor_set(x_20, 2, x_18);
lean_ctor_set(x_20, 3, x_19);
x_21 = lean_ctor_get(x_2, 1);
lean_inc(x_21);
lean_dec(x_2);
x_22 = l_Lean_Parser_mkParserState(x_1);
lean_dec(x_1);
x_23 = l_Lean_Parser_ParserFn_run(x_14, x_17, x_20, x_21, x_22);
lean_ctor_set(x_6, 0, x_23);
return x_6;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_24 = lean_ctor_get(x_6, 0);
x_25 = lean_ctor_get(x_6, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_6);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_ctor_get(x_3, 2);
x_28 = lean_alloc_closure((void*)(l_Lean_Parser_whitespace), 2, 0);
x_29 = lean_box(0);
x_30 = lean_alloc_closure((void*)(l_Lean_Parser_tokenFn), 3, 1);
lean_closure_set(x_30, 0, x_29);
x_31 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_31, 0, x_28);
lean_closure_set(x_31, 1, x_30);
x_32 = lean_mk_string_unchecked("", 0, 0);
lean_inc(x_32);
x_33 = l_Lean_FileMap_ofString(x_32);
lean_inc(x_1);
x_34 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_34, 0, x_1);
lean_ctor_set(x_34, 1, x_32);
lean_ctor_set(x_34, 2, x_33);
x_35 = lean_box(0);
x_36 = lean_box(0);
lean_inc(x_27);
x_37 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_37, 0, x_26);
lean_ctor_set(x_37, 1, x_27);
lean_ctor_set(x_37, 2, x_35);
lean_ctor_set(x_37, 3, x_36);
x_38 = lean_ctor_get(x_2, 1);
lean_inc(x_38);
lean_dec(x_2);
x_39 = l_Lean_Parser_mkParserState(x_1);
lean_dec(x_1);
x_40 = l_Lean_Parser_ParserFn_run(x_31, x_34, x_37, x_38, x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_25);
return x_41;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_parseToken(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Formatter_parseToken___redArg(x_1, x_2, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_parseToken___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Formatter_parseToken___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_parseToken___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Formatter_parseToken(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Substring_takeRightWhileAux___at___Lean_PrettyPrinter_Formatter_pushToken_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_string_utf8_byte_size(x_1);
lean_inc(x_6);
lean_inc(x_1);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set(x_7, 2, x_6);
x_8 = lean_unsigned_to_nat(1u);
lean_inc(x_6);
x_9 = l_Substring_prevn(x_7, x_8, x_6);
lean_dec(x_7);
x_10 = lean_mk_string_unchecked(" ", 1, 1);
x_11 = lean_string_utf8_byte_size(x_10);
x_12 = lean_nat_dec_lt(x_3, x_4);
if (x_12 == 0)
{
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; uint8_t x_17; uint32_t x_20; uint8_t x_21; uint8_t x_26; lean_object* x_31; uint32_t x_32; uint8_t x_33; 
lean_inc(x_1);
x_13 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_9);
lean_ctor_set(x_13, 2, x_6);
x_14 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_5);
lean_ctor_set(x_14, 2, x_11);
x_15 = l_Substring_beq(x_13, x_14);
x_16 = lean_string_utf8_prev(x_2, x_4);
x_20 = lean_string_utf8_get(x_2, x_16);
x_31 = lean_unsigned_to_nat(32u);
x_32 = l_Char_ofNat(x_31);
x_33 = l_instDecidableEqChar(x_20, x_32);
if (x_33 == 0)
{
lean_object* x_34; uint32_t x_35; uint8_t x_36; 
x_34 = lean_unsigned_to_nat(9u);
x_35 = l_Char_ofNat(x_34);
x_36 = l_instDecidableEqChar(x_20, x_35);
x_26 = x_36;
goto block_30;
}
else
{
x_26 = x_15;
goto block_30;
}
block_19:
{
if (x_17 == 0)
{
lean_dec(x_16);
lean_dec(x_1);
return x_4;
}
else
{
lean_dec(x_4);
x_4 = x_16;
goto _start;
}
}
block_25:
{
if (x_21 == 0)
{
lean_object* x_22; uint32_t x_23; uint8_t x_24; 
x_22 = lean_unsigned_to_nat(10u);
x_23 = l_Char_ofNat(x_22);
x_24 = l_instDecidableEqChar(x_20, x_23);
x_17 = x_24;
goto block_19;
}
else
{
x_17 = x_15;
goto block_19;
}
}
block_30:
{
if (x_26 == 0)
{
lean_object* x_27; uint32_t x_28; uint8_t x_29; 
x_27 = lean_unsigned_to_nat(13u);
x_28 = l_Char_ofNat(x_27);
x_29 = l_instDecidableEqChar(x_20, x_28);
x_21 = x_29;
goto block_25;
}
else
{
x_21 = x_15;
goto block_25;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_takeRightWhileAux___at___Lean_PrettyPrinter_Formatter_pushToken_spec__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; uint8_t x_7; uint32_t x_10; uint8_t x_11; uint8_t x_16; lean_object* x_21; uint32_t x_22; uint8_t x_23; 
x_6 = lean_string_utf8_prev(x_2, x_4);
x_10 = lean_string_utf8_get(x_2, x_6);
x_21 = lean_unsigned_to_nat(32u);
x_22 = l_Char_ofNat(x_21);
x_23 = l_instDecidableEqChar(x_10, x_22);
if (x_23 == 0)
{
lean_object* x_24; uint32_t x_25; uint8_t x_26; 
x_24 = lean_unsigned_to_nat(9u);
x_25 = l_Char_ofNat(x_24);
x_26 = l_instDecidableEqChar(x_10, x_25);
x_16 = x_26;
goto block_20;
}
else
{
x_16 = x_1;
goto block_20;
}
block_9:
{
if (x_7 == 0)
{
lean_dec(x_6);
return x_4;
}
else
{
lean_dec(x_4);
x_4 = x_6;
goto _start;
}
}
block_15:
{
if (x_11 == 0)
{
lean_object* x_12; uint32_t x_13; uint8_t x_14; 
x_12 = lean_unsigned_to_nat(10u);
x_13 = l_Char_ofNat(x_12);
x_14 = l_instDecidableEqChar(x_10, x_13);
x_7 = x_14;
goto block_9;
}
else
{
x_7 = x_1;
goto block_9;
}
}
block_20:
{
if (x_16 == 0)
{
lean_object* x_17; uint32_t x_18; uint8_t x_19; 
x_17 = lean_unsigned_to_nat(13u);
x_18 = l_Char_ofNat(x_17);
x_19 = l_instDecidableEqChar(x_10, x_18);
x_11 = x_19;
goto block_15;
}
else
{
x_11 = x_1;
goto block_15;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_takeWhileAux___at___Lean_PrettyPrinter_Formatter_pushToken_spec__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_9; 
x_9 = lean_nat_dec_lt(x_4, x_3);
if (x_9 == 0)
{
return x_4;
}
else
{
uint32_t x_10; uint8_t x_11; lean_object* x_19; uint32_t x_20; uint8_t x_21; 
x_10 = lean_string_utf8_get(x_2, x_4);
x_19 = lean_unsigned_to_nat(32u);
x_20 = l_Char_ofNat(x_19);
x_21 = l_instDecidableEqChar(x_10, x_20);
if (x_21 == 0)
{
lean_object* x_22; uint32_t x_23; uint8_t x_24; 
x_22 = lean_unsigned_to_nat(9u);
x_23 = l_Char_ofNat(x_22);
x_24 = l_instDecidableEqChar(x_10, x_23);
x_11 = x_24;
goto block_18;
}
else
{
x_11 = x_1;
goto block_18;
}
block_18:
{
if (x_11 == 0)
{
lean_object* x_12; uint32_t x_13; uint8_t x_14; 
x_12 = lean_unsigned_to_nat(13u);
x_13 = l_Char_ofNat(x_12);
x_14 = l_instDecidableEqChar(x_10, x_13);
if (x_14 == 0)
{
lean_object* x_15; uint32_t x_16; uint8_t x_17; 
x_15 = lean_unsigned_to_nat(10u);
x_16 = l_Char_ofNat(x_15);
x_17 = l_instDecidableEqChar(x_10, x_16);
x_5 = x_17;
goto block_8;
}
else
{
x_5 = x_1;
goto block_8;
}
}
else
{
x_5 = x_1;
goto block_8;
}
}
}
block_8:
{
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; 
x_6 = lean_string_utf8_next(x_2, x_4);
lean_dec(x_4);
x_4 = x_6;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_takeRightWhileAux___at___Lean_PrettyPrinter_Formatter_pushToken_spec__3(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; uint8_t x_7; uint32_t x_10; lean_object* x_11; uint32_t x_12; uint8_t x_13; 
x_6 = lean_string_utf8_prev(x_2, x_4);
x_10 = lean_string_utf8_get(x_2, x_6);
x_11 = lean_unsigned_to_nat(32u);
x_12 = l_Char_ofNat(x_11);
x_13 = l_instDecidableEqChar(x_10, x_12);
if (x_13 == 0)
{
lean_object* x_14; uint32_t x_15; uint8_t x_16; 
x_14 = lean_unsigned_to_nat(9u);
x_15 = l_Char_ofNat(x_14);
x_16 = l_instDecidableEqChar(x_10, x_15);
if (x_16 == 0)
{
lean_object* x_17; uint32_t x_18; uint8_t x_19; 
x_17 = lean_unsigned_to_nat(13u);
x_18 = l_Char_ofNat(x_17);
x_19 = l_instDecidableEqChar(x_10, x_18);
if (x_19 == 0)
{
lean_object* x_20; uint32_t x_21; uint8_t x_22; 
x_20 = lean_unsigned_to_nat(10u);
x_21 = l_Char_ofNat(x_20);
x_22 = l_instDecidableEqChar(x_10, x_21);
x_7 = x_22;
goto block_9;
}
else
{
x_7 = x_1;
goto block_9;
}
}
else
{
x_7 = x_1;
goto block_9;
}
}
else
{
x_7 = x_1;
goto block_9;
}
block_9:
{
if (x_7 == 0)
{
lean_dec(x_6);
return x_4;
}
else
{
lean_dec(x_4);
x_4 = x_6;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_pushToken___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_28 = lean_ctor_get(x_1, 0);
lean_inc(x_28);
lean_dec(x_1);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_28, 2);
lean_inc(x_31);
lean_dec(x_28);
x_32 = l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(x_29, x_31, x_30);
lean_inc(x_31);
x_33 = l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(x_29, x_32, x_31);
x_34 = lean_nat_sub(x_33, x_32);
x_35 = lean_unsigned_to_nat(0u);
x_36 = lean_nat_dec_eq(x_34, x_35);
lean_dec(x_34);
if (x_36 == 0)
{
uint8_t x_37; 
lean_inc(x_33);
x_37 = l_String_anyAux___at___Lean_Parser_checkTailLinebreak_spec__0(x_29, x_31, x_33);
lean_dec(x_31);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_38 = l_Lean_PrettyPrinter_Formatter_pushLine___redArg(x_4, x_7);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_string_utf8_extract(x_29, x_32, x_33);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_29);
x_41 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = l___private_Lean_PrettyPrinter_Formatter_0__Lean_PrettyPrinter_Formatter_push___redArg(x_41, x_4, x_39);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_8 = x_4;
x_9 = x_43;
goto block_27;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_44 = lean_ctor_get(x_5, 2);
lean_inc(x_44);
x_45 = lean_string_utf8_extract(x_29, x_32, x_33);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_29);
x_46 = lean_mk_string_unchecked("\n", 1, 1);
x_47 = lean_string_append(x_45, x_46);
lean_dec(x_46);
x_48 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_49 = lean_alloc_closure((void*)(l___private_Lean_PrettyPrinter_Formatter_0__Lean_PrettyPrinter_Formatter_push___boxed), 6, 1);
lean_closure_set(x_49, 0, x_48);
x_50 = lean_nat_to_int(x_35);
x_51 = l_Std_Format_getIndent(x_44);
lean_dec(x_44);
x_52 = lean_nat_to_int(x_51);
x_53 = lean_int_sub(x_50, x_52);
lean_dec(x_52);
lean_dec(x_50);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
lean_inc(x_4);
x_55 = l_Lean_PrettyPrinter_Formatter_indent(x_49, x_54, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
x_8 = x_4;
x_9 = x_56;
goto block_27;
}
else
{
lean_dec(x_4);
return x_55;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_57 = lean_box(0);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_7);
return x_58;
}
}
else
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_59 = lean_box(0);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_7);
return x_60;
}
block_27:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_10 = lean_st_ref_take(x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = lean_mk_string_unchecked("", 0, 0);
x_15 = lean_ctor_get_uint8(x_11, sizeof(void*)*3);
x_16 = lean_ctor_get_uint8(x_11, sizeof(void*)*3 + 1);
x_17 = lean_ctor_get_uint8(x_11, sizeof(void*)*3 + 2);
x_18 = lean_ctor_get(x_11, 2);
lean_inc(x_18);
lean_dec(x_11);
x_19 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_14);
lean_ctor_set(x_19, 2, x_18);
lean_ctor_set_uint8(x_19, sizeof(void*)*3, x_15);
lean_ctor_set_uint8(x_19, sizeof(void*)*3 + 1, x_16);
lean_ctor_set_uint8(x_19, sizeof(void*)*3 + 2, x_17);
x_20 = lean_st_ref_set(x_8, x_19, x_12);
lean_dec(x_8);
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
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_pushToken___lam__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_155; uint8_t x_156; uint8_t x_169; 
x_61 = lean_st_ref_get(x_6, x_9);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
x_65 = lean_mk_string_unchecked("", 0, 0);
x_169 = lean_string_dec_eq(x_64, x_65);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; lean_object* x_174; lean_object* x_175; uint8_t x_176; 
x_170 = lean_box(1);
x_171 = lean_unsigned_to_nat(0u);
x_172 = lean_string_utf8_byte_size(x_3);
x_173 = lean_unbox(x_170);
x_174 = l_Substring_takeRightWhileAux___at___Lean_PrettyPrinter_Formatter_pushToken_spec__3(x_173, x_3, x_171, x_172);
x_175 = lean_string_utf8_extract(x_3, x_171, x_174);
lean_dec(x_174);
x_176 = lean_string_dec_eq(x_175, x_3);
lean_dec(x_175);
if (x_176 == 0)
{
lean_dec(x_62);
goto block_110;
}
else
{
if (x_1 == 0)
{
uint8_t x_177; 
lean_dec(x_62);
x_177 = lean_unbox(x_170);
x_155 = x_177;
x_156 = x_1;
goto block_168;
}
else
{
uint8_t x_178; 
x_178 = lean_ctor_get_uint8(x_62, sizeof(void*)*3);
lean_dec(x_62);
if (x_178 == 0)
{
uint8_t x_179; 
x_179 = lean_unbox(x_170);
x_155 = x_179;
x_156 = x_178;
goto block_168;
}
else
{
uint8_t x_180; 
lean_dec(x_64);
x_180 = lean_unbox(x_170);
x_111 = x_180;
x_112 = x_5;
x_113 = x_6;
x_114 = x_7;
x_115 = x_8;
x_116 = x_63;
goto block_132;
}
}
}
}
else
{
lean_dec(x_62);
goto block_110;
}
block_26:
{
uint8_t x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_ctor_get_uint8(x_11, sizeof(void*)*3 + 1);
x_20 = lean_ctor_get_uint8(x_11, sizeof(void*)*3 + 2);
x_21 = lean_ctor_get(x_11, 2);
lean_inc(x_21);
lean_dec(x_11);
x_22 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_22, 0, x_14);
lean_ctor_set(x_22, 1, x_18);
lean_ctor_set(x_22, 2, x_21);
lean_ctor_set_uint8(x_22, sizeof(void*)*3, x_1);
lean_ctor_set_uint8(x_22, sizeof(void*)*3 + 1, x_19);
lean_ctor_set_uint8(x_22, sizeof(void*)*3 + 2, x_20);
x_23 = lean_st_ref_set(x_17, x_22, x_13);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_apply_6(x_2, x_16, x_15, x_17, x_12, x_10, x_24);
return x_25;
}
block_43:
{
uint8_t x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_36 = lean_ctor_get_uint8(x_34, sizeof(void*)*3 + 1);
x_37 = lean_ctor_get_uint8(x_34, sizeof(void*)*3 + 2);
x_38 = lean_ctor_get(x_34, 2);
lean_inc(x_38);
lean_dec(x_34);
x_39 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_39, 0, x_33);
lean_ctor_set(x_39, 1, x_35);
lean_ctor_set(x_39, 2, x_38);
lean_ctor_set_uint8(x_39, sizeof(void*)*3, x_1);
lean_ctor_set_uint8(x_39, sizeof(void*)*3 + 1, x_36);
lean_ctor_set_uint8(x_39, sizeof(void*)*3 + 2, x_37);
x_40 = lean_st_ref_set(x_29, x_39, x_32);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_42 = lean_apply_6(x_2, x_31, x_28, x_29, x_27, x_30, x_41);
return x_42;
}
block_60:
{
uint8_t x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_53 = lean_ctor_get_uint8(x_46, sizeof(void*)*3 + 1);
x_54 = lean_ctor_get_uint8(x_46, sizeof(void*)*3 + 2);
x_55 = lean_ctor_get(x_46, 2);
lean_inc(x_55);
lean_dec(x_46);
x_56 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_56, 0, x_48);
lean_ctor_set(x_56, 1, x_52);
lean_ctor_set(x_56, 2, x_55);
lean_ctor_set_uint8(x_56, sizeof(void*)*3, x_1);
lean_ctor_set_uint8(x_56, sizeof(void*)*3 + 1, x_53);
lean_ctor_set_uint8(x_56, sizeof(void*)*3 + 2, x_54);
x_57 = lean_st_ref_set(x_44, x_56, x_47);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec(x_57);
x_59 = lean_apply_6(x_2, x_49, x_45, x_44, x_50, x_51, x_58);
return x_59;
}
block_81:
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_71 = lean_st_ref_take(x_67, x_70);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = lean_box(0);
x_75 = lean_ctor_get(x_72, 0);
lean_inc(x_75);
x_76 = lean_unsigned_to_nat(0u);
x_77 = lean_string_utf8_byte_size(x_3);
x_78 = l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(x_3, x_77, x_76);
x_79 = lean_string_utf8_extract(x_3, x_78, x_77);
lean_dec(x_77);
lean_dec(x_78);
x_80 = lean_string_dec_eq(x_79, x_3);
lean_dec(x_79);
if (x_80 == 0)
{
lean_dec(x_3);
x_44 = x_67;
x_45 = x_66;
x_46 = x_72;
x_47 = x_73;
x_48 = x_75;
x_49 = x_74;
x_50 = x_68;
x_51 = x_69;
x_52 = x_65;
goto block_60;
}
else
{
lean_dec(x_65);
x_44 = x_67;
x_45 = x_66;
x_46 = x_72;
x_47 = x_73;
x_48 = x_75;
x_49 = x_74;
x_50 = x_68;
x_51 = x_69;
x_52 = x_3;
goto block_60;
}
}
block_110:
{
uint8_t x_82; 
x_82 = lean_string_dec_eq(x_64, x_65);
lean_dec(x_64);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_83 = lean_mk_string_unchecked(" ", 1, 1);
x_84 = lean_unsigned_to_nat(0u);
x_85 = lean_string_utf8_byte_size(x_3);
x_86 = lean_unsigned_to_nat(1u);
lean_inc(x_85);
lean_inc(x_3);
x_87 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_87, 0, x_3);
lean_ctor_set(x_87, 1, x_84);
lean_ctor_set(x_87, 2, x_85);
lean_inc(x_85);
x_88 = l_Substring_prevn(x_87, x_86, x_85);
lean_dec(x_87);
lean_inc(x_85);
lean_inc(x_3);
x_89 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_89, 0, x_3);
lean_ctor_set(x_89, 1, x_88);
lean_ctor_set(x_89, 2, x_85);
x_90 = lean_string_utf8_byte_size(x_83);
x_91 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_91, 0, x_83);
lean_ctor_set(x_91, 1, x_84);
lean_ctor_set(x_91, 2, x_90);
x_92 = l_Substring_beq(x_89, x_91);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_85);
lean_inc(x_3);
x_93 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_93, 0, x_3);
x_94 = l___private_Lean_PrettyPrinter_Formatter_0__Lean_PrettyPrinter_Formatter_push___redArg(x_93, x_6, x_63);
x_95 = lean_ctor_get(x_94, 1);
lean_inc(x_95);
lean_dec(x_94);
x_66 = x_5;
x_67 = x_6;
x_68 = x_7;
x_69 = x_8;
x_70 = x_95;
goto block_81;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_96 = l_Lean_PrettyPrinter_Formatter_pushLine___redArg(x_6, x_63);
x_97 = lean_ctor_get(x_96, 1);
lean_inc(x_97);
lean_dec(x_96);
lean_inc(x_3);
x_98 = l_Substring_takeRightWhileAux___at___Lean_PrettyPrinter_Formatter_pushToken_spec__0(x_3, x_3, x_84, x_85);
x_99 = lean_string_utf8_extract(x_3, x_84, x_98);
lean_dec(x_98);
x_100 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_100, 0, x_99);
x_101 = l___private_Lean_PrettyPrinter_Formatter_0__Lean_PrettyPrinter_Formatter_push___redArg(x_100, x_6, x_97);
x_102 = lean_ctor_get(x_101, 1);
lean_inc(x_102);
lean_dec(x_101);
x_66 = x_5;
x_67 = x_6;
x_68 = x_7;
x_69 = x_8;
x_70 = x_102;
goto block_81;
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_103 = lean_unsigned_to_nat(0u);
x_104 = lean_string_utf8_byte_size(x_3);
x_105 = l_Substring_takeRightWhileAux___at___Lean_PrettyPrinter_Formatter_pushToken_spec__1(x_82, x_3, x_103, x_104);
x_106 = lean_string_utf8_extract(x_3, x_103, x_105);
lean_dec(x_105);
x_107 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_107, 0, x_106);
x_108 = l___private_Lean_PrettyPrinter_Formatter_0__Lean_PrettyPrinter_Formatter_push___redArg(x_107, x_6, x_63);
x_109 = lean_ctor_get(x_108, 1);
lean_inc(x_109);
lean_dec(x_108);
x_66 = x_5;
x_67 = x_6;
x_68 = x_7;
x_69 = x_8;
x_70 = x_109;
goto block_81;
}
}
block_132:
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; 
x_117 = l_Lean_PrettyPrinter_Formatter_pushLine___redArg(x_113, x_116);
x_118 = lean_ctor_get(x_117, 1);
lean_inc(x_118);
lean_dec(x_117);
lean_inc(x_3);
x_119 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_119, 0, x_3);
x_120 = l___private_Lean_PrettyPrinter_Formatter_0__Lean_PrettyPrinter_Formatter_push___redArg(x_119, x_113, x_118);
x_121 = lean_ctor_get(x_120, 1);
lean_inc(x_121);
lean_dec(x_120);
x_122 = lean_st_ref_take(x_113, x_121);
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
lean_dec(x_122);
x_125 = lean_box(0);
x_126 = lean_ctor_get(x_123, 0);
lean_inc(x_126);
x_127 = lean_unsigned_to_nat(0u);
x_128 = lean_string_utf8_byte_size(x_3);
x_129 = l_Substring_takeWhileAux___at___Lean_PrettyPrinter_Formatter_pushToken_spec__2(x_111, x_3, x_128, x_127);
x_130 = lean_string_utf8_extract(x_3, x_129, x_128);
lean_dec(x_128);
lean_dec(x_129);
x_131 = lean_string_dec_eq(x_130, x_3);
lean_dec(x_130);
if (x_131 == 0)
{
lean_dec(x_3);
x_27 = x_114;
x_28 = x_112;
x_29 = x_113;
x_30 = x_115;
x_31 = x_125;
x_32 = x_124;
x_33 = x_126;
x_34 = x_123;
x_35 = x_65;
goto block_43;
}
else
{
lean_dec(x_65);
x_27 = x_114;
x_28 = x_112;
x_29 = x_113;
x_30 = x_115;
x_31 = x_125;
x_32 = x_124;
x_33 = x_126;
x_34 = x_123;
x_35 = x_3;
goto block_43;
}
}
block_154:
{
if (x_133 == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; 
lean_inc(x_3);
x_139 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_139, 0, x_3);
x_140 = l___private_Lean_PrettyPrinter_Formatter_0__Lean_PrettyPrinter_Formatter_push___redArg(x_139, x_135, x_138);
x_141 = lean_ctor_get(x_140, 1);
lean_inc(x_141);
lean_dec(x_140);
x_142 = lean_st_ref_take(x_135, x_141);
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
lean_dec(x_142);
x_145 = lean_box(0);
x_146 = lean_ctor_get(x_143, 0);
lean_inc(x_146);
x_147 = lean_unsigned_to_nat(0u);
x_148 = lean_string_utf8_byte_size(x_3);
x_149 = l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(x_3, x_148, x_147);
x_150 = lean_string_utf8_extract(x_3, x_149, x_148);
lean_dec(x_148);
lean_dec(x_149);
x_151 = lean_string_dec_eq(x_150, x_3);
lean_dec(x_150);
if (x_151 == 0)
{
lean_dec(x_3);
x_10 = x_137;
x_11 = x_143;
x_12 = x_136;
x_13 = x_144;
x_14 = x_146;
x_15 = x_134;
x_16 = x_145;
x_17 = x_135;
x_18 = x_65;
goto block_26;
}
else
{
lean_object* x_152; lean_object* x_153; 
lean_dec(x_65);
x_152 = lean_ctor_get(x_143, 1);
lean_inc(x_152);
x_153 = lean_string_append(x_3, x_152);
lean_dec(x_152);
x_10 = x_137;
x_11 = x_143;
x_12 = x_136;
x_13 = x_144;
x_14 = x_146;
x_15 = x_134;
x_16 = x_145;
x_17 = x_135;
x_18 = x_153;
goto block_26;
}
}
else
{
x_111 = x_133;
x_112 = x_134;
x_113 = x_135;
x_114 = x_136;
x_115 = x_137;
x_116 = x_138;
goto block_132;
}
}
block_168:
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; uint8_t x_167; 
x_157 = lean_unsigned_to_nat(0u);
x_158 = lean_string_utf8_byte_size(x_3);
x_159 = l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(x_3, x_158, x_157);
x_160 = lean_string_utf8_extract(x_3, x_159, x_158);
lean_dec(x_158);
lean_dec(x_159);
lean_inc(x_160);
x_161 = lean_string_append(x_160, x_64);
lean_dec(x_64);
lean_inc(x_5);
x_162 = l_Lean_PrettyPrinter_Formatter_parseToken___redArg(x_161, x_5, x_7, x_8, x_63);
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_162, 1);
lean_inc(x_164);
lean_dec(x_162);
x_165 = lean_ctor_get(x_163, 2);
lean_inc(x_165);
lean_dec(x_163);
x_166 = lean_string_utf8_byte_size(x_160);
lean_dec(x_160);
x_167 = lean_nat_dec_le(x_165, x_166);
lean_dec(x_166);
lean_dec(x_165);
if (x_167 == 0)
{
x_133 = x_155;
x_134 = x_5;
x_135 = x_6;
x_136 = x_7;
x_137 = x_8;
x_138 = x_164;
goto block_154;
}
else
{
x_133 = x_156;
x_134 = x_5;
x_135 = x_6;
x_136 = x_7;
x_137 = x_8;
x_138 = x_164;
goto block_154;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_pushToken(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_pushToken___lam__0___boxed), 7, 1);
lean_closure_set(x_9, 0, x_1);
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 2);
lean_inc(x_13);
lean_dec(x_10);
x_14 = l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(x_11, x_13, x_12);
lean_inc(x_13);
x_15 = l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(x_11, x_14, x_13);
x_16 = lean_nat_sub(x_15, x_14);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_eq(x_16, x_17);
lean_dec(x_16);
if (x_18 == 0)
{
uint8_t x_38; 
lean_inc(x_15);
x_38 = l_String_anyAux___at___Lean_Parser_checkTailLinebreak_spec__0(x_11, x_13, x_15);
lean_dec(x_13);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_39 = lean_mk_string_unchecked("  ", 2, 2);
x_40 = lean_string_utf8_extract(x_11, x_14, x_15);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
x_41 = lean_string_append(x_39, x_40);
lean_dec(x_40);
x_42 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_42, 0, x_41);
x_43 = l___private_Lean_PrettyPrinter_Formatter_0__Lean_PrettyPrinter_Formatter_push___redArg(x_42, x_5, x_8);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
x_19 = x_4;
x_20 = x_5;
x_21 = x_6;
x_22 = x_7;
x_23 = x_44;
goto block_37;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_45 = lean_mk_string_unchecked("\n", 1, 1);
x_46 = lean_string_utf8_extract(x_11, x_14, x_15);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
x_47 = lean_string_append(x_45, x_46);
lean_dec(x_46);
x_48 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_49 = l___private_Lean_PrettyPrinter_Formatter_0__Lean_PrettyPrinter_Formatter_push___redArg(x_48, x_5, x_8);
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec(x_49);
x_19 = x_4;
x_20 = x_5;
x_21 = x_6;
x_22 = x_7;
x_23 = x_50;
goto block_37;
}
}
else
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
x_51 = lean_box(0);
x_52 = l_Lean_PrettyPrinter_Formatter_pushToken___lam__1(x_3, x_9, x_2, x_51, x_4, x_5, x_6, x_7, x_8);
return x_52;
}
block_37:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_24 = lean_st_ref_take(x_20, x_23);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
x_28 = lean_mk_string_unchecked("", 0, 0);
x_29 = lean_ctor_get_uint8(x_25, sizeof(void*)*3 + 1);
x_30 = lean_ctor_get_uint8(x_25, sizeof(void*)*3 + 2);
x_31 = lean_ctor_get(x_25, 2);
lean_inc(x_31);
lean_dec(x_25);
x_32 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_32, 0, x_27);
lean_ctor_set(x_32, 1, x_28);
lean_ctor_set(x_32, 2, x_31);
lean_ctor_set_uint8(x_32, sizeof(void*)*3, x_18);
lean_ctor_set_uint8(x_32, sizeof(void*)*3 + 1, x_29);
lean_ctor_set_uint8(x_32, sizeof(void*)*3 + 2, x_30);
x_33 = lean_st_ref_set(x_20, x_32, x_26);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_box(0);
x_36 = l_Lean_PrettyPrinter_Formatter_pushToken___lam__1(x_3, x_9, x_2, x_35, x_19, x_20, x_21, x_22, x_34);
return x_36;
}
}
else
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_1);
x_53 = lean_box(0);
x_54 = l_Lean_PrettyPrinter_Formatter_pushToken___lam__1(x_3, x_9, x_2, x_53, x_4, x_5, x_6, x_7, x_8);
return x_54;
}
}
}
LEAN_EXPORT lean_object* l_Substring_takeRightWhileAux___at___Lean_PrettyPrinter_Formatter_pushToken_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Substring_takeRightWhileAux___at___Lean_PrettyPrinter_Formatter_pushToken_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Substring_takeRightWhileAux___at___Lean_PrettyPrinter_Formatter_pushToken_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l_Substring_takeRightWhileAux___at___Lean_PrettyPrinter_Formatter_pushToken_spec__1(x_5, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Substring_takeWhileAux___at___Lean_PrettyPrinter_Formatter_pushToken_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l_Substring_takeWhileAux___at___Lean_PrettyPrinter_Formatter_pushToken_spec__2(x_5, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Substring_takeRightWhileAux___at___Lean_PrettyPrinter_Formatter_pushToken_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l_Substring_takeRightWhileAux___at___Lean_PrettyPrinter_Formatter_pushToken_spec__3(x_5, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_pushToken___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Formatter_pushToken___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_pushToken___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_1);
lean_dec(x_1);
x_11 = l_Lean_PrettyPrinter_Formatter_pushToken___lam__1(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_pushToken___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lean_PrettyPrinter_Formatter_pushToken(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter_spec__0___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_7 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__0___boxed), 5, 0);
x_8 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__1), 7, 0);
x_9 = l_instMonadEIO(lean_box(0));
x_10 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
lean_inc(x_12);
x_13 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_13, 0, x_12);
x_14 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_14, 0, x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_closure((void*)(l_instMonadEIO___lam__1), 5, 0);
x_17 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_17, 0, x_16);
x_18 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_18, 0, x_17);
x_19 = lean_alloc_closure((void*)(l_instMonadEIO___lam__2), 5, 0);
x_20 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_20, 0, x_19);
x_21 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_21, 0, x_20);
x_22 = lean_alloc_closure((void*)(l_EStateM_seqRight), 7, 2);
lean_closure_set(x_22, 0, lean_box(0));
lean_closure_set(x_22, 1, lean_box(0));
x_23 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_23, 0, x_22);
x_24 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_25, 0, x_15);
lean_ctor_set(x_25, 1, x_7);
lean_ctor_set(x_25, 2, x_18);
lean_ctor_set(x_25, 3, x_21);
lean_ctor_set(x_25, 4, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_8);
x_27 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_26);
x_28 = lean_box(0);
x_29 = l_instInhabitedOfMonad___redArg(x_27, x_28);
x_30 = lean_alloc_closure((void*)(l_panic___at___Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter_spec__0___lam__0___boxed), 2, 1);
lean_closure_set(x_30, 0, x_29);
x_31 = lean_panic_fn(x_30, x_1);
x_32 = lean_apply_5(x_31, x_2, x_3, x_4, x_5, x_6);
return x_32;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_Syntax_MonadTraverser_getCur___at___Lean_PrettyPrinter_Formatter_visitArgs_spec__2___redArg(x_3, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = l_Lean_Syntax_isToken(x_1, x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_mk_string_unchecked("PrettyPrinter", 13, 13);
x_13 = lean_mk_string_unchecked("format", 6, 6);
x_14 = lean_mk_string_unchecked("backtrack", 9, 9);
x_15 = l_Lean_Name_mkStr3(x_12, x_13, x_14);
lean_inc(x_15);
x_16 = l_Lean_isTracingEnabledFor___at___Lean_PrettyPrinter_Formatter_categoryFormatterCore_spec__0___redArg(x_15, x_4, x_10);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_unbox(x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_15);
lean_free_object(x_7);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = l_Lean_PrettyPrinter_Formatter_throwBacktrack___redArg(x_19);
return x_20;
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_16);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_22 = lean_ctor_get(x_16, 1);
x_23 = lean_ctor_get(x_16, 0);
lean_dec(x_23);
x_24 = lean_mk_string_unchecked("unexpected syntax '", 19, 19);
x_25 = l_Lean_stringToMessageData(x_24);
lean_dec(x_24);
x_26 = lean_box(0);
x_27 = l_Lean_Syntax_formatStx(x_9, x_26, x_11);
x_28 = l_Lean_MessageData_ofFormat(x_27);
lean_ctor_set_tag(x_16, 7);
lean_ctor_set(x_16, 1, x_28);
lean_ctor_set(x_16, 0, x_25);
x_29 = lean_mk_string_unchecked("', expected symbol '", 20, 20);
x_30 = l_Lean_stringToMessageData(x_29);
lean_dec(x_29);
lean_ctor_set_tag(x_7, 7);
lean_ctor_set(x_7, 1, x_30);
lean_ctor_set(x_7, 0, x_16);
x_31 = l_Lean_stringToMessageData(x_1);
lean_dec(x_1);
x_32 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_32, 0, x_7);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_mk_string_unchecked("'", 1, 1);
x_34 = l_Lean_stringToMessageData(x_33);
lean_dec(x_33);
x_35 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_addTrace___at___Lean_PrettyPrinter_Formatter_categoryFormatterCore_spec__1___redArg(x_15, x_35, x_4, x_5, x_22);
lean_dec(x_5);
lean_dec(x_4);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = l_Lean_PrettyPrinter_Formatter_throwBacktrack___redArg(x_37);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_39 = lean_ctor_get(x_16, 1);
lean_inc(x_39);
lean_dec(x_16);
x_40 = lean_mk_string_unchecked("unexpected syntax '", 19, 19);
x_41 = l_Lean_stringToMessageData(x_40);
lean_dec(x_40);
x_42 = lean_box(0);
x_43 = l_Lean_Syntax_formatStx(x_9, x_42, x_11);
x_44 = l_Lean_MessageData_ofFormat(x_43);
x_45 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_45, 0, x_41);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_mk_string_unchecked("', expected symbol '", 20, 20);
x_47 = l_Lean_stringToMessageData(x_46);
lean_dec(x_46);
lean_ctor_set_tag(x_7, 7);
lean_ctor_set(x_7, 1, x_47);
lean_ctor_set(x_7, 0, x_45);
x_48 = l_Lean_stringToMessageData(x_1);
lean_dec(x_1);
x_49 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_49, 0, x_7);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_mk_string_unchecked("'", 1, 1);
x_51 = l_Lean_stringToMessageData(x_50);
lean_dec(x_50);
x_52 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_52, 0, x_49);
lean_ctor_set(x_52, 1, x_51);
x_53 = l_Lean_addTrace___at___Lean_PrettyPrinter_Formatter_categoryFormatterCore_spec__1___redArg(x_15, x_52, x_4, x_5, x_39);
lean_dec(x_5);
lean_dec(x_4);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec(x_53);
x_55 = l_Lean_PrettyPrinter_Formatter_throwBacktrack___redArg(x_54);
return x_55;
}
}
}
else
{
lean_free_object(x_7);
if (lean_obj_tag(x_9) == 2)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_56 = lean_ctor_get(x_9, 0);
lean_inc(x_56);
x_57 = l___private_Lean_PrettyPrinter_Formatter_0__Lean_PrettyPrinter_Formatter_getExprPos_x3f(x_9);
lean_dec(x_9);
x_58 = lean_box(0);
x_59 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_pushToken___boxed), 8, 3);
lean_closure_set(x_59, 0, x_56);
lean_closure_set(x_59, 1, x_1);
lean_closure_set(x_59, 2, x_58);
lean_inc(x_3);
x_60 = l_Lean_PrettyPrinter_Formatter_withMaybeTag(x_57, x_59, x_2, x_3, x_4, x_5, x_10);
lean_dec(x_57);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
lean_dec(x_60);
x_62 = l_Lean_Syntax_MonadTraverser_goLeft___at___Lean_PrettyPrinter_Formatter_visitArgs_spec__1___redArg(x_3, x_61);
lean_dec(x_3);
return x_62;
}
else
{
lean_dec(x_3);
return x_60;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_9);
lean_dec(x_1);
x_63 = lean_mk_string_unchecked("Lean.PrettyPrinter.Formatter", 28, 28);
x_64 = lean_mk_string_unchecked("Lean.PrettyPrinter.Formatter.symbolNoAntiquot.formatter", 55, 55);
x_65 = lean_unsigned_to_nat(410u);
x_66 = lean_unsigned_to_nat(42u);
x_67 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_68 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_63, x_64, x_65, x_66, x_67);
lean_dec(x_67);
lean_dec(x_64);
lean_dec(x_63);
x_69 = l_panic___at___Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter_spec__0(x_68, x_2, x_3, x_4, x_5, x_10);
return x_69;
}
}
}
else
{
lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_70 = lean_ctor_get(x_7, 0);
x_71 = lean_ctor_get(x_7, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_7);
x_72 = l_Lean_Syntax_isToken(x_1, x_70);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
lean_dec(x_3);
lean_dec(x_2);
x_73 = lean_mk_string_unchecked("PrettyPrinter", 13, 13);
x_74 = lean_mk_string_unchecked("format", 6, 6);
x_75 = lean_mk_string_unchecked("backtrack", 9, 9);
x_76 = l_Lean_Name_mkStr3(x_73, x_74, x_75);
lean_inc(x_76);
x_77 = l_Lean_isTracingEnabledFor___at___Lean_PrettyPrinter_Formatter_categoryFormatterCore_spec__0___redArg(x_76, x_4, x_71);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_unbox(x_78);
lean_dec(x_78);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; 
lean_dec(x_76);
lean_dec(x_70);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_80 = lean_ctor_get(x_77, 1);
lean_inc(x_80);
lean_dec(x_77);
x_81 = l_Lean_PrettyPrinter_Formatter_throwBacktrack___redArg(x_80);
return x_81;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_82 = lean_ctor_get(x_77, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_83 = x_77;
} else {
 lean_dec_ref(x_77);
 x_83 = lean_box(0);
}
x_84 = lean_mk_string_unchecked("unexpected syntax '", 19, 19);
x_85 = l_Lean_stringToMessageData(x_84);
lean_dec(x_84);
x_86 = lean_box(0);
x_87 = l_Lean_Syntax_formatStx(x_70, x_86, x_72);
x_88 = l_Lean_MessageData_ofFormat(x_87);
if (lean_is_scalar(x_83)) {
 x_89 = lean_alloc_ctor(7, 2, 0);
} else {
 x_89 = x_83;
 lean_ctor_set_tag(x_89, 7);
}
lean_ctor_set(x_89, 0, x_85);
lean_ctor_set(x_89, 1, x_88);
x_90 = lean_mk_string_unchecked("', expected symbol '", 20, 20);
x_91 = l_Lean_stringToMessageData(x_90);
lean_dec(x_90);
x_92 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_92, 0, x_89);
lean_ctor_set(x_92, 1, x_91);
x_93 = l_Lean_stringToMessageData(x_1);
lean_dec(x_1);
x_94 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
x_95 = lean_mk_string_unchecked("'", 1, 1);
x_96 = l_Lean_stringToMessageData(x_95);
lean_dec(x_95);
x_97 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_97, 0, x_94);
lean_ctor_set(x_97, 1, x_96);
x_98 = l_Lean_addTrace___at___Lean_PrettyPrinter_Formatter_categoryFormatterCore_spec__1___redArg(x_76, x_97, x_4, x_5, x_82);
lean_dec(x_5);
lean_dec(x_4);
x_99 = lean_ctor_get(x_98, 1);
lean_inc(x_99);
lean_dec(x_98);
x_100 = l_Lean_PrettyPrinter_Formatter_throwBacktrack___redArg(x_99);
return x_100;
}
}
else
{
if (lean_obj_tag(x_70) == 2)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_101 = lean_ctor_get(x_70, 0);
lean_inc(x_101);
x_102 = l___private_Lean_PrettyPrinter_Formatter_0__Lean_PrettyPrinter_Formatter_getExprPos_x3f(x_70);
lean_dec(x_70);
x_103 = lean_box(0);
x_104 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_pushToken___boxed), 8, 3);
lean_closure_set(x_104, 0, x_101);
lean_closure_set(x_104, 1, x_1);
lean_closure_set(x_104, 2, x_103);
lean_inc(x_3);
x_105 = l_Lean_PrettyPrinter_Formatter_withMaybeTag(x_102, x_104, x_2, x_3, x_4, x_5, x_71);
lean_dec(x_102);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_ctor_get(x_105, 1);
lean_inc(x_106);
lean_dec(x_105);
x_107 = l_Lean_Syntax_MonadTraverser_goLeft___at___Lean_PrettyPrinter_Formatter_visitArgs_spec__1___redArg(x_3, x_106);
lean_dec(x_3);
return x_107;
}
else
{
lean_dec(x_3);
return x_105;
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
lean_dec(x_70);
lean_dec(x_1);
x_108 = lean_mk_string_unchecked("Lean.PrettyPrinter.Formatter", 28, 28);
x_109 = lean_mk_string_unchecked("Lean.PrettyPrinter.Formatter.symbolNoAntiquot.formatter", 55, 55);
x_110 = lean_unsigned_to_nat(410u);
x_111 = lean_unsigned_to_nat(42u);
x_112 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_113 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_108, x_109, x_110, x_111, x_112);
lean_dec(x_112);
lean_dec(x_109);
lean_dec(x_108);
x_114 = l_panic___at___Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter_spec__0(x_113, x_2, x_3, x_4, x_5, x_71);
return x_114;
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_panic___at___Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter_spec__0___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_nonReservedSymbolNoAntiquot_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_rawCh_formatter(uint32_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_mk_string_unchecked("", 0, 0);
x_8 = lean_string_push(x_7, x_1);
x_9 = l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter(x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_rawCh_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint32_t x_7; lean_object* x_8; 
x_7 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_8 = l_Lean_PrettyPrinter_Formatter_rawCh_formatter(x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_PrettyPrinter_Formatter_unicodeSymbolNoAntiquot_formatter_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0(x_1, x_2, x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_2, 5);
lean_inc(x_8);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_9);
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_5);
x_12 = lean_ctor_get(x_2, 5);
lean_inc(x_12);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_PrettyPrinter_Formatter_unicodeSymbolNoAntiquot_formatter_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwError___at___Lean_PrettyPrinter_Formatter_unicodeSymbolNoAntiquot_formatter_spec__0___redArg(x_2, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_unicodeSymbolNoAntiquot_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Syntax_MonadTraverser_getCur___at___Lean_PrettyPrinter_Formatter_visitArgs_spec__2___redArg(x_4, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 2)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_string_utf8_byte_size(x_1);
x_15 = l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(x_1, x_14, x_13);
x_16 = l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(x_1, x_15, x_14);
x_17 = lean_string_utf8_extract(x_1, x_15, x_16);
lean_dec(x_16);
lean_dec(x_15);
x_18 = lean_string_dec_eq(x_12, x_17);
lean_dec(x_17);
lean_dec(x_12);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_1);
lean_inc(x_4);
x_19 = l_Lean_PrettyPrinter_Formatter_pushToken(x_11, x_2, x_18, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = l_Lean_Syntax_MonadTraverser_goLeft___at___Lean_PrettyPrinter_Formatter_visitArgs_spec__1___redArg(x_4, x_20);
lean_dec(x_4);
return x_21;
}
else
{
lean_dec(x_4);
return x_19;
}
}
else
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; 
lean_dec(x_2);
x_22 = lean_box(0);
x_23 = lean_unbox(x_22);
lean_inc(x_4);
x_24 = l_Lean_PrettyPrinter_Formatter_pushToken(x_11, x_1, x_23, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = l_Lean_Syntax_MonadTraverser_goLeft___at___Lean_PrettyPrinter_Formatter_visitArgs_spec__1___redArg(x_4, x_25);
lean_dec(x_4);
return x_26;
}
else
{
lean_dec(x_4);
return x_24;
}
}
}
else
{
uint8_t x_27; 
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_8);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_ctor_get(x_8, 1);
x_29 = lean_ctor_get(x_8, 0);
lean_dec(x_29);
x_30 = l_Lean_Syntax_MonadTraverser_getCur___at___Lean_PrettyPrinter_Formatter_visitArgs_spec__2___redArg(x_4, x_28);
lean_dec(x_4);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = lean_ctor_get(x_30, 1);
x_34 = lean_mk_string_unchecked("not an atom: ", 13, 13);
x_35 = l_Lean_stringToMessageData(x_34);
lean_dec(x_34);
x_36 = l_Lean_MessageData_ofSyntax(x_32);
lean_ctor_set_tag(x_30, 7);
lean_ctor_set(x_30, 1, x_36);
lean_ctor_set(x_30, 0, x_35);
x_37 = lean_mk_string_unchecked("", 0, 0);
x_38 = l_Lean_stringToMessageData(x_37);
lean_dec(x_37);
lean_ctor_set_tag(x_8, 7);
lean_ctor_set(x_8, 1, x_38);
lean_ctor_set(x_8, 0, x_30);
x_39 = l_Lean_throwError___at___Lean_PrettyPrinter_Formatter_unicodeSymbolNoAntiquot_formatter_spec__0___redArg(x_8, x_5, x_6, x_33);
lean_dec(x_6);
lean_dec(x_5);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_40 = lean_ctor_get(x_30, 0);
x_41 = lean_ctor_get(x_30, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_30);
x_42 = lean_mk_string_unchecked("not an atom: ", 13, 13);
x_43 = l_Lean_stringToMessageData(x_42);
lean_dec(x_42);
x_44 = l_Lean_MessageData_ofSyntax(x_40);
x_45 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_mk_string_unchecked("", 0, 0);
x_47 = l_Lean_stringToMessageData(x_46);
lean_dec(x_46);
lean_ctor_set_tag(x_8, 7);
lean_ctor_set(x_8, 1, x_47);
lean_ctor_set(x_8, 0, x_45);
x_48 = l_Lean_throwError___at___Lean_PrettyPrinter_Formatter_unicodeSymbolNoAntiquot_formatter_spec__0___redArg(x_8, x_5, x_6, x_41);
lean_dec(x_6);
lean_dec(x_5);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_49 = lean_ctor_get(x_8, 1);
lean_inc(x_49);
lean_dec(x_8);
x_50 = l_Lean_Syntax_MonadTraverser_getCur___at___Lean_PrettyPrinter_Formatter_visitArgs_spec__2___redArg(x_4, x_49);
lean_dec(x_4);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_53 = x_50;
} else {
 lean_dec_ref(x_50);
 x_53 = lean_box(0);
}
x_54 = lean_mk_string_unchecked("not an atom: ", 13, 13);
x_55 = l_Lean_stringToMessageData(x_54);
lean_dec(x_54);
x_56 = l_Lean_MessageData_ofSyntax(x_51);
if (lean_is_scalar(x_53)) {
 x_57 = lean_alloc_ctor(7, 2, 0);
} else {
 x_57 = x_53;
 lean_ctor_set_tag(x_57, 7);
}
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_mk_string_unchecked("", 0, 0);
x_59 = l_Lean_stringToMessageData(x_58);
lean_dec(x_58);
x_60 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_59);
x_61 = l_Lean_throwError___at___Lean_PrettyPrinter_Formatter_unicodeSymbolNoAntiquot_formatter_spec__0___redArg(x_60, x_5, x_6, x_52);
lean_dec(x_6);
lean_dec(x_5);
return x_61;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_PrettyPrinter_Formatter_unicodeSymbolNoAntiquot_formatter_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwError___at___Lean_PrettyPrinter_Formatter_unicodeSymbolNoAntiquot_formatter_spec__0___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_PrettyPrinter_Formatter_unicodeSymbolNoAntiquot_formatter_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwError___at___Lean_PrettyPrinter_Formatter_unicodeSymbolNoAntiquot_formatter_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT uint8_t l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Data_Trie_find_x3f___redArg(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_box(0);
x_5 = lean_unbox(x_4);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
lean_dec(x_3);
x_6 = lean_box(1);
x_7 = lean_unbox(x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_mk_string_unchecked("ident", 5, 5);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = l_Lean_PrettyPrinter_Formatter_checkKind___redArg(x_7, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Lean_Syntax_MonadTraverser_getCur___at___Lean_PrettyPrinter_Formatter_visitArgs_spec__2___redArg(x_2, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 3)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 2);
lean_inc(x_14);
x_15 = lean_simp_macro_scopes(x_14);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
x_17 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___lam__0___boxed), 2, 1);
lean_closure_set(x_17, 0, x_16);
x_18 = l___private_Lean_PrettyPrinter_Formatter_0__Lean_PrettyPrinter_Formatter_getExprPos_x3f(x_11);
lean_dec(x_11);
x_19 = lean_box(1);
x_20 = lean_unbox(x_19);
x_21 = l_Lean_Name_toString(x_15, x_20, x_17);
x_22 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_pushToken___boxed), 8, 3);
lean_closure_set(x_22, 0, x_13);
lean_closure_set(x_22, 1, x_21);
lean_closure_set(x_22, 2, x_19);
lean_inc(x_2);
x_23 = l_Lean_PrettyPrinter_Formatter_withMaybeTag(x_18, x_22, x_1, x_2, x_3, x_4, x_12);
lean_dec(x_18);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = l_Lean_Syntax_MonadTraverser_goLeft___at___Lean_PrettyPrinter_Formatter_visitArgs_spec__1___redArg(x_2, x_24);
lean_dec(x_2);
return x_25;
}
else
{
lean_dec(x_2);
return x_23;
}
}
else
{
uint8_t x_26; 
lean_dec(x_11);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_10);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_10, 1);
x_28 = lean_ctor_get(x_10, 0);
lean_dec(x_28);
x_29 = l_Lean_Syntax_MonadTraverser_getCur___at___Lean_PrettyPrinter_Formatter_visitArgs_spec__2___redArg(x_2, x_27);
lean_dec(x_2);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_ctor_get(x_29, 1);
x_33 = lean_mk_string_unchecked("not an ident: ", 14, 14);
x_34 = l_Lean_stringToMessageData(x_33);
lean_dec(x_33);
x_35 = l_Lean_MessageData_ofSyntax(x_31);
lean_ctor_set_tag(x_29, 7);
lean_ctor_set(x_29, 1, x_35);
lean_ctor_set(x_29, 0, x_34);
x_36 = lean_mk_string_unchecked("", 0, 0);
x_37 = l_Lean_stringToMessageData(x_36);
lean_dec(x_36);
lean_ctor_set_tag(x_10, 7);
lean_ctor_set(x_10, 1, x_37);
lean_ctor_set(x_10, 0, x_29);
x_38 = l_Lean_throwError___at___Lean_PrettyPrinter_Formatter_unicodeSymbolNoAntiquot_formatter_spec__0___redArg(x_10, x_3, x_4, x_32);
lean_dec(x_4);
lean_dec(x_3);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_39 = lean_ctor_get(x_29, 0);
x_40 = lean_ctor_get(x_29, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_29);
x_41 = lean_mk_string_unchecked("not an ident: ", 14, 14);
x_42 = l_Lean_stringToMessageData(x_41);
lean_dec(x_41);
x_43 = l_Lean_MessageData_ofSyntax(x_39);
x_44 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_mk_string_unchecked("", 0, 0);
x_46 = l_Lean_stringToMessageData(x_45);
lean_dec(x_45);
lean_ctor_set_tag(x_10, 7);
lean_ctor_set(x_10, 1, x_46);
lean_ctor_set(x_10, 0, x_44);
x_47 = l_Lean_throwError___at___Lean_PrettyPrinter_Formatter_unicodeSymbolNoAntiquot_formatter_spec__0___redArg(x_10, x_3, x_4, x_40);
lean_dec(x_4);
lean_dec(x_3);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_48 = lean_ctor_get(x_10, 1);
lean_inc(x_48);
lean_dec(x_10);
x_49 = l_Lean_Syntax_MonadTraverser_getCur___at___Lean_PrettyPrinter_Formatter_visitArgs_spec__2___redArg(x_2, x_48);
lean_dec(x_2);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_52 = x_49;
} else {
 lean_dec_ref(x_49);
 x_52 = lean_box(0);
}
x_53 = lean_mk_string_unchecked("not an ident: ", 14, 14);
x_54 = l_Lean_stringToMessageData(x_53);
lean_dec(x_53);
x_55 = l_Lean_MessageData_ofSyntax(x_50);
if (lean_is_scalar(x_52)) {
 x_56 = lean_alloc_ctor(7, 2, 0);
} else {
 x_56 = x_52;
 lean_ctor_set_tag(x_56, 7);
}
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_mk_string_unchecked("", 0, 0);
x_58 = l_Lean_stringToMessageData(x_57);
lean_dec(x_57);
x_59 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_59, 0, x_56);
lean_ctor_set(x_59, 1, x_58);
x_60 = l_Lean_throwError___at___Lean_PrettyPrinter_Formatter_unicodeSymbolNoAntiquot_formatter_spec__0___redArg(x_59, x_3, x_4, x_51);
lean_dec(x_4);
lean_dec(x_3);
return x_60;
}
}
}
else
{
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___lam__0(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_PrettyPrinter_Formatter_rawIdentNoAntiquot_formatter___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_rawIdentNoAntiquot_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_mk_string_unchecked("ident", 5, 5);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = l_Lean_PrettyPrinter_Formatter_checkKind___redArg(x_7, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Lean_Syntax_MonadTraverser_getCur___at___Lean_PrettyPrinter_Formatter_visitArgs_spec__2___redArg(x_2, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 3)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 2);
lean_inc(x_14);
x_15 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_rawIdentNoAntiquot_formatter___lam__0___boxed), 1, 0);
x_16 = l___private_Lean_PrettyPrinter_Formatter_0__Lean_PrettyPrinter_Formatter_getExprPos_x3f(x_11);
lean_dec(x_11);
x_17 = lean_box(1);
x_18 = lean_unbox(x_17);
x_19 = l_Lean_Name_toString(x_14, x_18, x_15);
x_20 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_pushToken___boxed), 8, 3);
lean_closure_set(x_20, 0, x_13);
lean_closure_set(x_20, 1, x_19);
lean_closure_set(x_20, 2, x_17);
lean_inc(x_2);
x_21 = l_Lean_PrettyPrinter_Formatter_withMaybeTag(x_16, x_20, x_1, x_2, x_3, x_4, x_12);
lean_dec(x_16);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Lean_Syntax_MonadTraverser_goLeft___at___Lean_PrettyPrinter_Formatter_visitArgs_spec__1___redArg(x_2, x_22);
lean_dec(x_2);
return x_23;
}
else
{
lean_dec(x_2);
return x_21;
}
}
else
{
uint8_t x_24; 
lean_dec(x_11);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_10);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_10, 1);
x_26 = lean_ctor_get(x_10, 0);
lean_dec(x_26);
x_27 = l_Lean_Syntax_MonadTraverser_getCur___at___Lean_PrettyPrinter_Formatter_visitArgs_spec__2___redArg(x_2, x_25);
lean_dec(x_2);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_27, 1);
x_31 = lean_mk_string_unchecked("not an ident: ", 14, 14);
x_32 = l_Lean_stringToMessageData(x_31);
lean_dec(x_31);
x_33 = l_Lean_MessageData_ofSyntax(x_29);
lean_ctor_set_tag(x_27, 7);
lean_ctor_set(x_27, 1, x_33);
lean_ctor_set(x_27, 0, x_32);
x_34 = lean_mk_string_unchecked("", 0, 0);
x_35 = l_Lean_stringToMessageData(x_34);
lean_dec(x_34);
lean_ctor_set_tag(x_10, 7);
lean_ctor_set(x_10, 1, x_35);
lean_ctor_set(x_10, 0, x_27);
x_36 = l_Lean_throwError___at___Lean_PrettyPrinter_Formatter_unicodeSymbolNoAntiquot_formatter_spec__0___redArg(x_10, x_3, x_4, x_30);
lean_dec(x_4);
lean_dec(x_3);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_37 = lean_ctor_get(x_27, 0);
x_38 = lean_ctor_get(x_27, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_27);
x_39 = lean_mk_string_unchecked("not an ident: ", 14, 14);
x_40 = l_Lean_stringToMessageData(x_39);
lean_dec(x_39);
x_41 = l_Lean_MessageData_ofSyntax(x_37);
x_42 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_mk_string_unchecked("", 0, 0);
x_44 = l_Lean_stringToMessageData(x_43);
lean_dec(x_43);
lean_ctor_set_tag(x_10, 7);
lean_ctor_set(x_10, 1, x_44);
lean_ctor_set(x_10, 0, x_42);
x_45 = l_Lean_throwError___at___Lean_PrettyPrinter_Formatter_unicodeSymbolNoAntiquot_formatter_spec__0___redArg(x_10, x_3, x_4, x_38);
lean_dec(x_4);
lean_dec(x_3);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_46 = lean_ctor_get(x_10, 1);
lean_inc(x_46);
lean_dec(x_10);
x_47 = l_Lean_Syntax_MonadTraverser_getCur___at___Lean_PrettyPrinter_Formatter_visitArgs_spec__2___redArg(x_2, x_46);
lean_dec(x_2);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_50 = x_47;
} else {
 lean_dec_ref(x_47);
 x_50 = lean_box(0);
}
x_51 = lean_mk_string_unchecked("not an ident: ", 14, 14);
x_52 = l_Lean_stringToMessageData(x_51);
lean_dec(x_51);
x_53 = l_Lean_MessageData_ofSyntax(x_48);
if (lean_is_scalar(x_50)) {
 x_54 = lean_alloc_ctor(7, 2, 0);
} else {
 x_54 = x_50;
 lean_ctor_set_tag(x_54, 7);
}
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_mk_string_unchecked("", 0, 0);
x_56 = l_Lean_stringToMessageData(x_55);
lean_dec(x_55);
x_57 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_56);
x_58 = l_Lean_throwError___at___Lean_PrettyPrinter_Formatter_unicodeSymbolNoAntiquot_formatter_spec__0___redArg(x_57, x_3, x_4, x_49);
lean_dec(x_4);
lean_dec(x_3);
return x_58;
}
}
}
else
{
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_rawIdentNoAntiquot_formatter___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_PrettyPrinter_Formatter_rawIdentNoAntiquot_formatter___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_identEq_formatter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Formatter_rawIdentNoAntiquot_formatter(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_identEq_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Formatter_rawIdentNoAntiquot_formatter(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_identEq_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Formatter_identEq_formatter(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_visitAtom(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_43; uint8_t x_44; 
x_7 = l_Lean_Syntax_MonadTraverser_getCur___at___Lean_PrettyPrinter_Formatter_visitArgs_spec__2___redArg(x_3, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_10 = x_7;
} else {
 lean_dec_ref(x_7);
 x_10 = lean_box(0);
}
x_43 = lean_box(0);
x_44 = lean_name_eq(x_1, x_43);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = l_Lean_PrettyPrinter_Formatter_checkKind___redArg(x_1, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_33 = x_2;
x_34 = x_3;
x_35 = x_4;
x_36 = x_5;
x_37 = x_46;
goto block_42;
}
else
{
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_45;
}
}
else
{
lean_dec(x_1);
x_33 = x_2;
x_34 = x_3;
x_35 = x_4;
x_36 = x_5;
x_37 = x_9;
goto block_42;
}
block_32:
{
if (lean_obj_tag(x_16) == 2)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
lean_dec(x_10);
lean_dec(x_8);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_box(0);
x_20 = lean_unbox(x_19);
lean_inc(x_12);
x_21 = l_Lean_PrettyPrinter_Formatter_pushToken(x_17, x_18, x_20, x_15, x_12, x_11, x_14, x_13);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Lean_Syntax_MonadTraverser_goLeft___at___Lean_PrettyPrinter_Formatter_visitArgs_spec__1___redArg(x_12, x_22);
lean_dec(x_12);
return x_23;
}
else
{
lean_dec(x_12);
return x_21;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_12);
x_24 = lean_mk_string_unchecked("not an atom: ", 13, 13);
x_25 = l_Lean_stringToMessageData(x_24);
lean_dec(x_24);
x_26 = l_Lean_MessageData_ofSyntax(x_8);
if (lean_is_scalar(x_10)) {
 x_27 = lean_alloc_ctor(7, 2, 0);
} else {
 x_27 = x_10;
 lean_ctor_set_tag(x_27, 7);
}
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_mk_string_unchecked("", 0, 0);
x_29 = l_Lean_stringToMessageData(x_28);
lean_dec(x_28);
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_throwError___at___Lean_PrettyPrinter_Formatter_unicodeSymbolNoAntiquot_formatter_spec__0___redArg(x_30, x_11, x_14, x_13);
lean_dec(x_14);
lean_dec(x_11);
return x_31;
}
}
block_42:
{
if (lean_obj_tag(x_8) == 1)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_8, 2);
lean_inc(x_38);
x_39 = lean_unsigned_to_nat(0u);
x_40 = l_Lean_instInhabitedSyntax;
x_41 = lean_array_get(x_40, x_38, x_39);
lean_dec(x_38);
x_11 = x_35;
x_12 = x_34;
x_13 = x_37;
x_14 = x_36;
x_15 = x_33;
x_16 = x_41;
goto block_32;
}
else
{
lean_inc(x_8);
x_11 = x_35;
x_12 = x_34;
x_13 = x_37;
x_14 = x_36;
x_15 = x_33;
x_16 = x_8;
goto block_32;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_charLitNoAntiquot_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_mk_string_unchecked("char", 4, 4);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = l_Lean_PrettyPrinter_Formatter_visitAtom(x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_strLitNoAntiquot_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_mk_string_unchecked("str", 3, 3);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = l_Lean_PrettyPrinter_Formatter_visitAtom(x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_nameLitNoAntiquot_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_mk_string_unchecked("name", 4, 4);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = l_Lean_PrettyPrinter_Formatter_visitAtom(x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_numLitNoAntiquot_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_mk_string_unchecked("num", 3, 3);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = l_Lean_PrettyPrinter_Formatter_visitAtom(x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_scientificLitNoAntiquot_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_mk_string_unchecked("scientific", 10, 10);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = l_Lean_PrettyPrinter_Formatter_visitAtom(x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_fieldIdx_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_mk_string_unchecked("fieldIdx", 8, 8);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = l_Lean_PrettyPrinter_Formatter_visitAtom(x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at___Lean_PrettyPrinter_Formatter_manyNoAntiquot_formatter_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_2, x_8);
if (x_9 == 1)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
return x_11;
}
else
{
lean_object* x_12; 
lean_inc(x_1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_12 = lean_apply_5(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_2, x_14);
lean_dec(x_2);
x_2 = x_15;
x_7 = x_13;
goto _start;
}
else
{
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
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at___Lean_PrettyPrinter_Formatter_manyNoAntiquot_formatter_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_forM_loop___at___Lean_PrettyPrinter_Formatter_manyNoAntiquot_formatter_spec__0___redArg(x_1, x_3, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_manyNoAntiquot_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = l_Lean_Syntax_MonadTraverser_getCur___at___Lean_PrettyPrinter_Formatter_visitArgs_spec__2___redArg(x_3, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Syntax_getArgs(x_8);
lean_dec(x_8);
x_11 = lean_array_get_size(x_10);
lean_dec(x_10);
lean_inc(x_11);
x_12 = lean_alloc_closure((void*)(l_Nat_forM_loop___at___Lean_PrettyPrinter_Formatter_manyNoAntiquot_formatter_spec__0___boxed), 9, 4);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_11);
lean_closure_set(x_12, 2, x_11);
lean_closure_set(x_12, 3, lean_box(0));
x_13 = l_Lean_PrettyPrinter_Formatter_visitArgs(x_12, x_2, x_3, x_4, x_5, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at___Lean_PrettyPrinter_Formatter_manyNoAntiquot_formatter_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_forM_loop___at___Lean_PrettyPrinter_Formatter_manyNoAntiquot_formatter_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_many1NoAntiquot_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Formatter_manyNoAntiquot_formatter(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_optionalNoAntiquot_formatter___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (x_1 == 0)
{
lean_object* x_8; 
x_8 = lean_apply_5(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_optionalNoAntiquot_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = l_Lean_Syntax_MonadTraverser_getCur___at___Lean_PrettyPrinter_Formatter_visitArgs_spec__2___redArg(x_3, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Syntax_getArgs(x_8);
lean_dec(x_8);
x_11 = l_Array_isEmpty___redArg(x_10);
lean_dec(x_10);
x_12 = lean_box(x_11);
x_13 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_optionalNoAntiquot_formatter___lam__0___boxed), 7, 2);
lean_closure_set(x_13, 0, x_12);
lean_closure_set(x_13, 1, x_1);
x_14 = l_Lean_PrettyPrinter_Formatter_visitArgs(x_13, x_2, x_3, x_4, x_5, x_9);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_optionalNoAntiquot_formatter___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_1);
lean_dec(x_1);
x_9 = l_Lean_PrettyPrinter_Formatter_optionalNoAntiquot_formatter___lam__0(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_many1Unbox_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_7 = l_Lean_Syntax_MonadTraverser_getCur___at___Lean_PrettyPrinter_Formatter_visitArgs_spec__2___redArg(x_3, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Syntax_getKind(x_8);
x_11 = lean_mk_string_unchecked("null", 4, 4);
x_12 = l_Lean_Name_mkStr1(x_11);
x_13 = lean_name_eq(x_10, x_12);
lean_dec(x_12);
lean_dec(x_10);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_9);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = l_Lean_PrettyPrinter_Formatter_manyNoAntiquot_formatter(x_1, x_2, x_3, x_4, x_5, x_9);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Nat_forRevM_loop___at___Lean_PrettyPrinter_Formatter_sepByNoAntiquot_formatter_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_3, x_9);
if (x_10 == 1)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_8);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_3, x_13);
lean_dec(x_3);
x_19 = lean_unsigned_to_nat(2u);
x_20 = lean_nat_mod(x_14, x_19);
x_21 = lean_nat_dec_eq(x_20, x_9);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
lean_inc(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_22 = lean_apply_5(x_1, x_4, x_5, x_6, x_7, x_8);
x_15 = x_22;
goto block_18;
}
else
{
lean_object* x_23; 
lean_inc(x_2);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_23 = lean_apply_5(x_2, x_4, x_5, x_6, x_7, x_8);
x_15 = x_23;
goto block_18;
}
block_18:
{
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_3 = x_14;
x_8 = x_16;
goto _start;
}
else
{
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_forRevM_loop___at___Lean_PrettyPrinter_Formatter_sepByNoAntiquot_formatter_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Nat_forRevM_loop___at___Lean_PrettyPrinter_Formatter_sepByNoAntiquot_formatter_spec__0___redArg(x_1, x_2, x_4, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_sepByNoAntiquot_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = l_Lean_Syntax_MonadTraverser_getCur___at___Lean_PrettyPrinter_Formatter_visitArgs_spec__2___redArg(x_4, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Syntax_getArgs(x_9);
lean_dec(x_9);
x_12 = lean_array_get_size(x_11);
lean_dec(x_11);
lean_inc(x_12);
x_13 = lean_alloc_closure((void*)(l_Nat_forRevM_loop___at___Lean_PrettyPrinter_Formatter_sepByNoAntiquot_formatter_spec__0___boxed), 10, 5);
lean_closure_set(x_13, 0, x_2);
lean_closure_set(x_13, 1, x_1);
lean_closure_set(x_13, 2, x_12);
lean_closure_set(x_13, 3, x_12);
lean_closure_set(x_13, 4, lean_box(0));
x_14 = l_Lean_PrettyPrinter_Formatter_visitArgs(x_13, x_3, x_4, x_5, x_6, x_10);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Nat_forRevM_loop___at___Lean_PrettyPrinter_Formatter_sepByNoAntiquot_formatter_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Nat_forRevM_loop___at___Lean_PrettyPrinter_Formatter_sepByNoAntiquot_formatter_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_sepBy1NoAntiquot_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Formatter_sepByNoAntiquot_formatter(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_withoutInfo_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkWsBefore_formatter___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_st_ref_get(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_mk_string_unchecked("", 0, 0);
x_9 = lean_string_dec_eq(x_7, x_8);
lean_dec(x_8);
lean_dec(x_7);
if (x_9 == 0)
{
lean_object* x_10; 
lean_free_object(x_3);
x_10 = l_Lean_PrettyPrinter_Formatter_pushLine___redArg(x_1, x_6);
return x_10;
}
else
{
lean_object* x_11; 
x_11 = lean_box(0);
lean_ctor_set(x_3, 0, x_11);
return x_3;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_3);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_mk_string_unchecked("", 0, 0);
x_16 = lean_string_dec_eq(x_14, x_15);
lean_dec(x_15);
lean_dec(x_14);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = l_Lean_PrettyPrinter_Formatter_pushLine___redArg(x_1, x_13);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_13);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkWsBefore_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Formatter_checkWsBefore_formatter___redArg(x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkWsBefore_formatter___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PrettyPrinter_Formatter_checkWsBefore_formatter___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkWsBefore_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Formatter_checkWsBefore_formatter(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkPrec_formatter___redArg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkPrec_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Formatter_checkPrec_formatter___redArg(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkPrec_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Formatter_checkPrec_formatter(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkLhsPrec_formatter___redArg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkLhsPrec_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Formatter_checkLhsPrec_formatter___redArg(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkLhsPrec_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Formatter_checkLhsPrec_formatter(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_setLhsPrec_formatter___redArg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_setLhsPrec_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Formatter_setLhsPrec_formatter___redArg(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_setLhsPrec_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Formatter_setLhsPrec_formatter(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkStackTop_formatter___redArg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkStackTop_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Formatter_checkStackTop_formatter___redArg(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkStackTop_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Formatter_checkStackTop_formatter(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkNoWsBefore_formatter___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; uint8_t x_15; 
x_3 = lean_st_ref_take(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_mk_string_unchecked("", 0, 0);
x_8 = lean_box(0);
x_9 = lean_ctor_get_uint8(x_4, sizeof(void*)*3 + 1);
x_10 = lean_ctor_get_uint8(x_4, sizeof(void*)*3 + 2);
x_11 = lean_ctor_get(x_4, 2);
lean_inc(x_11);
lean_dec(x_4);
x_12 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_12, 0, x_6);
lean_ctor_set(x_12, 1, x_7);
lean_ctor_set(x_12, 2, x_11);
x_13 = lean_unbox(x_8);
lean_ctor_set_uint8(x_12, sizeof(void*)*3, x_13);
lean_ctor_set_uint8(x_12, sizeof(void*)*3 + 1, x_9);
lean_ctor_set_uint8(x_12, sizeof(void*)*3 + 2, x_10);
x_14 = lean_st_ref_set(x_1, x_12, x_5);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
x_17 = lean_box(0);
lean_ctor_set(x_14, 0, x_17);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkNoWsBefore_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Formatter_checkNoWsBefore_formatter___redArg(x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkNoWsBefore_formatter___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PrettyPrinter_Formatter_checkNoWsBefore_formatter___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkNoWsBefore_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Formatter_checkNoWsBefore_formatter(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkLinebreakBefore_formatter___redArg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkLinebreakBefore_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Formatter_checkLinebreakBefore_formatter___redArg(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkLinebreakBefore_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Formatter_checkLinebreakBefore_formatter(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkTailWs_formatter___redArg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkTailWs_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Formatter_checkTailWs_formatter___redArg(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkTailWs_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Formatter_checkTailWs_formatter(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkColEq_formatter___redArg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkColEq_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Formatter_checkColEq_formatter___redArg(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkColEq_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Formatter_checkColEq_formatter(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkColGe_formatter___redArg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkColGe_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Formatter_checkColGe_formatter___redArg(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkColGe_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Formatter_checkColGe_formatter(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkColGt_formatter___redArg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkColGt_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Formatter_checkColGt_formatter___redArg(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkColGt_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Formatter_checkColGt_formatter(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkLineEq_formatter___redArg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkLineEq_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Formatter_checkLineEq_formatter___redArg(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkLineEq_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Formatter_checkLineEq_formatter(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_eoi_formatter___redArg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_eoi_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Formatter_eoi_formatter___redArg(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_eoi_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Formatter_eoi_formatter(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkNoImmediateColon_formatter___redArg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkNoImmediateColon_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Formatter_checkNoImmediateColon_formatter___redArg(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkNoImmediateColon_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Formatter_checkNoImmediateColon_formatter(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_skip_formatter___redArg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_skip_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Formatter_skip_formatter___redArg(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_skip_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Formatter_skip_formatter(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_pushNone_formatter___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_MonadTraverser_goLeft___at___Lean_PrettyPrinter_Formatter_visitArgs_spec__1___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_pushNone_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Syntax_MonadTraverser_goLeft___at___Lean_PrettyPrinter_Formatter_visitArgs_spec__1___redArg(x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_pushNone_formatter___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PrettyPrinter_Formatter_pushNone_formatter___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_pushNone_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Formatter_pushNone_formatter(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_hygieneInfoNoAntiquot_formatter___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_MonadTraverser_goLeft___at___Lean_PrettyPrinter_Formatter_visitArgs_spec__1___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_hygieneInfoNoAntiquot_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Syntax_MonadTraverser_goLeft___at___Lean_PrettyPrinter_Formatter_visitArgs_spec__1___redArg(x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_hygieneInfoNoAntiquot_formatter___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PrettyPrinter_Formatter_hygieneInfoNoAntiquot_formatter___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_hygieneInfoNoAntiquot_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Formatter_hygieneInfoNoAntiquot_formatter(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_PrettyPrinter_Formatter_interpolatedStr_formatter_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_19; 
x_19 = lean_usize_dec_eq(x_3, x_4);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_5);
x_20 = lean_array_uget(x_2, x_3);
x_21 = lean_mk_string_unchecked("interpolatedStrLitKind", 22, 22);
x_22 = l_Lean_Name_mkStr1(x_21);
x_23 = l_Lean_Syntax_isLit_x3f(x_22, x_20);
lean_dec(x_20);
lean_dec(x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
lean_inc(x_1);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_24 = lean_apply_5(x_1, x_6, x_7, x_8, x_9, x_10);
x_11 = x_24;
goto block_18;
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_ctor_set_tag(x_23, 3);
x_26 = l___private_Lean_PrettyPrinter_Formatter_0__Lean_PrettyPrinter_Formatter_push___redArg(x_23, x_7, x_10);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = l_Lean_Syntax_MonadTraverser_goLeft___at___Lean_PrettyPrinter_Formatter_visitArgs_spec__1___redArg(x_7, x_27);
x_11 = x_28;
goto block_18;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_23, 0);
lean_inc(x_29);
lean_dec(x_23);
x_30 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = l___private_Lean_PrettyPrinter_Formatter_0__Lean_PrettyPrinter_Formatter_push___redArg(x_30, x_7, x_10);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = l_Lean_Syntax_MonadTraverser_goLeft___at___Lean_PrettyPrinter_Formatter_visitArgs_spec__1___redArg(x_7, x_32);
x_11 = x_33;
goto block_18;
}
}
}
else
{
lean_object* x_34; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_5);
lean_ctor_set(x_34, 1, x_10);
return x_34;
}
block_18:
{
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_usize_of_nat(x_14);
x_16 = lean_usize_add(x_3, x_15);
x_3 = x_16;
x_5 = x_12;
x_10 = x_13;
goto _start;
}
else
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_box(0);
x_11 = lean_nat_dec_lt(x_1, x_2);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = lean_nat_dec_le(x_2, x_2);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_9);
return x_14;
}
else
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_usize_of_nat(x_1);
x_16 = lean_usize_of_nat(x_2);
x_17 = l_Array_foldlMUnsafe_fold___at___Lean_PrettyPrinter_Formatter_interpolatedStr_formatter_spec__0(x_3, x_4, x_15, x_16, x_10, x_5, x_6, x_7, x_8, x_9);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = l_Lean_Syntax_MonadTraverser_getCur___at___Lean_PrettyPrinter_Formatter_visitArgs_spec__2___redArg(x_3, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Syntax_getArgs(x_8);
lean_dec(x_8);
x_11 = l_Array_reverse(lean_box(0), x_10);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_get_size(x_11);
x_14 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter___lam__0___boxed), 9, 4);
lean_closure_set(x_14, 0, x_12);
lean_closure_set(x_14, 1, x_13);
lean_closure_set(x_14, 2, x_1);
lean_closure_set(x_14, 3, x_11);
x_15 = l_Lean_PrettyPrinter_Formatter_visitArgs(x_14, x_2, x_3, x_4, x_5, x_9);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_PrettyPrinter_Formatter_interpolatedStr_formatter_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_foldlMUnsafe_fold___at___Lean_PrettyPrinter_Formatter_interpolatedStr_formatter_spec__0(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5055_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_box(0);
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_registerAlias(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_PrettyPrinter_Formatter_formatterAliasesRef;
x_5 = l_Lean_Parser_registerAliasCore(lean_box(0), x_4, x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_instCoeFormatterAliasValue___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_instCoeFormatterAliasValue() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_instCoeFormatterAliasValue___lam__0), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_instCoeForallFormatterAliasValue___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_instCoeForallFormatterAliasValue() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_instCoeForallFormatterAliasValue___lam__0), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_instCoeForallForallFormatterAliasValue___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_instCoeForallForallFormatterAliasValue() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_instCoeForallForallFormatterAliasValue___lam__0), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5154_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = lean_mk_string_unchecked("pp", 2, 2);
x_3 = lean_mk_string_unchecked("oneline", 7, 7);
lean_inc(x_3);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(0);
x_6 = lean_mk_string_unchecked("(pretty printer) elide all but first line of pretty printer output", 66, 66);
lean_inc(x_2);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 2, x_6);
x_8 = lean_mk_string_unchecked("Lean", 4, 4);
x_9 = lean_mk_string_unchecked("PrettyPrinter", 13, 13);
x_10 = l_Lean_Name_mkStr4(x_8, x_9, x_2, x_3);
x_11 = l_Lean_Option_register___at___Lean_initFn____x40_Lean_Util_Profile___hyg_5__spec__0(x_4, x_7, x_10, x_1);
lean_dec(x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Substring_takeWhileAux___at___Lean_PrettyPrinter_format_spec__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_9; 
x_9 = lean_nat_dec_lt(x_4, x_3);
if (x_9 == 0)
{
return x_4;
}
else
{
uint32_t x_10; uint8_t x_11; uint8_t x_16; lean_object* x_21; uint32_t x_22; uint8_t x_23; 
x_10 = lean_string_utf8_get(x_2, x_4);
x_21 = lean_unsigned_to_nat(32u);
x_22 = l_Char_ofNat(x_21);
x_23 = l_instDecidableEqChar(x_10, x_22);
if (x_23 == 0)
{
lean_object* x_24; uint32_t x_25; uint8_t x_26; 
x_24 = lean_unsigned_to_nat(9u);
x_25 = l_Char_ofNat(x_24);
x_26 = l_instDecidableEqChar(x_10, x_25);
x_16 = x_26;
goto block_20;
}
else
{
x_16 = x_1;
goto block_20;
}
block_15:
{
if (x_11 == 0)
{
lean_object* x_12; uint32_t x_13; uint8_t x_14; 
x_12 = lean_unsigned_to_nat(10u);
x_13 = l_Char_ofNat(x_12);
x_14 = l_instDecidableEqChar(x_10, x_13);
x_5 = x_14;
goto block_8;
}
else
{
x_5 = x_1;
goto block_8;
}
}
block_20:
{
if (x_16 == 0)
{
lean_object* x_17; uint32_t x_18; uint8_t x_19; 
x_17 = lean_unsigned_to_nat(13u);
x_18 = l_Char_ofNat(x_17);
x_19 = l_instDecidableEqChar(x_10, x_18);
x_11 = x_19;
goto block_15;
}
else
{
x_11 = x_1;
goto block_15;
}
}
}
block_8:
{
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; 
x_6 = lean_string_utf8_next(x_2, x_4);
lean_dec(x_4);
x_4 = x_6;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_PrettyPrinter_format_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0(x_2, x_3, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_st_ref_take(x_4, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint64_t x_18; lean_object* x_19; lean_object* x_20; double x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_ctor_get(x_3, 5);
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_11, 2);
lean_inc(x_16);
x_17 = lean_ctor_get(x_11, 3);
lean_inc(x_17);
x_18 = lean_ctor_get_uint64(x_17, sizeof(void*)*1);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_float_of_nat(x_20);
x_22 = lean_box(0);
x_23 = lean_mk_string_unchecked("", 0, 0);
x_24 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set_float(x_24, sizeof(void*)*2, x_21);
lean_ctor_set_float(x_24, sizeof(void*)*2 + 8, x_21);
x_25 = lean_unbox(x_22);
lean_ctor_set_uint8(x_24, sizeof(void*)*2 + 16, x_25);
x_26 = lean_mk_empty_array_with_capacity(x_20);
x_27 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_7);
lean_ctor_set(x_27, 2, x_26);
lean_inc(x_13);
lean_ctor_set(x_9, 1, x_27);
lean_ctor_set(x_9, 0, x_13);
x_28 = l_Lean_PersistentArray_push___redArg(x_19, x_9);
x_29 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set_uint64(x_29, sizeof(void*)*1, x_18);
x_30 = lean_ctor_get(x_11, 4);
lean_inc(x_30);
x_31 = lean_ctor_get(x_11, 5);
lean_inc(x_31);
x_32 = lean_ctor_get(x_11, 6);
lean_inc(x_32);
x_33 = lean_ctor_get(x_11, 7);
lean_inc(x_33);
lean_dec(x_11);
x_34 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_34, 0, x_14);
lean_ctor_set(x_34, 1, x_15);
lean_ctor_set(x_34, 2, x_16);
lean_ctor_set(x_34, 3, x_29);
lean_ctor_set(x_34, 4, x_30);
lean_ctor_set(x_34, 5, x_31);
lean_ctor_set(x_34, 6, x_32);
lean_ctor_set(x_34, 7, x_33);
x_35 = lean_st_ref_set(x_4, x_34, x_12);
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
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint64_t x_49; lean_object* x_50; lean_object* x_51; double x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_42 = lean_ctor_get(x_9, 0);
x_43 = lean_ctor_get(x_9, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_9);
x_44 = lean_ctor_get(x_3, 5);
x_45 = lean_ctor_get(x_42, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_42, 1);
lean_inc(x_46);
x_47 = lean_ctor_get(x_42, 2);
lean_inc(x_47);
x_48 = lean_ctor_get(x_42, 3);
lean_inc(x_48);
x_49 = lean_ctor_get_uint64(x_48, sizeof(void*)*1);
x_50 = lean_ctor_get(x_48, 0);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_unsigned_to_nat(0u);
x_52 = lean_float_of_nat(x_51);
x_53 = lean_box(0);
x_54 = lean_mk_string_unchecked("", 0, 0);
x_55 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_55, 0, x_1);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set_float(x_55, sizeof(void*)*2, x_52);
lean_ctor_set_float(x_55, sizeof(void*)*2 + 8, x_52);
x_56 = lean_unbox(x_53);
lean_ctor_set_uint8(x_55, sizeof(void*)*2 + 16, x_56);
x_57 = lean_mk_empty_array_with_capacity(x_51);
x_58 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_7);
lean_ctor_set(x_58, 2, x_57);
lean_inc(x_44);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_44);
lean_ctor_set(x_59, 1, x_58);
x_60 = l_Lean_PersistentArray_push___redArg(x_50, x_59);
x_61 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set_uint64(x_61, sizeof(void*)*1, x_49);
x_62 = lean_ctor_get(x_42, 4);
lean_inc(x_62);
x_63 = lean_ctor_get(x_42, 5);
lean_inc(x_63);
x_64 = lean_ctor_get(x_42, 6);
lean_inc(x_64);
x_65 = lean_ctor_get(x_42, 7);
lean_inc(x_65);
lean_dec(x_42);
x_66 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_66, 0, x_45);
lean_ctor_set(x_66, 1, x_46);
lean_ctor_set(x_66, 2, x_47);
lean_ctor_set(x_66, 3, x_61);
lean_ctor_set(x_66, 4, x_62);
lean_ctor_set(x_66, 5, x_63);
lean_ctor_set(x_66, 6, x_64);
lean_ctor_set(x_66, 7, x_65);
x_67 = lean_st_ref_set(x_4, x_66, x_43);
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_69 = x_67;
} else {
 lean_dec_ref(x_67);
 x_69 = lean_box(0);
}
x_70 = lean_box(0);
if (lean_is_scalar(x_69)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_69;
}
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_68);
return x_71;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_format___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Std_Format_fill(x_1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_format___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_3);
x_9 = lean_box(0);
x_10 = lean_apply_5(x_1, x_8, x_9, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT uint8_t l_Lean_PrettyPrinter_format___lam__2(uint32_t x_1) {
_start:
{
lean_object* x_2; uint32_t x_3; uint8_t x_4; 
x_2 = lean_unsigned_to_nat(10u);
x_3 = l_Char_ofNat(x_2);
x_4 = l_instDecidableEqChar(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_format(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_35 = lean_mk_string_unchecked("PrettyPrinter", 13, 13);
x_36 = lean_mk_string_unchecked("format", 6, 6);
x_37 = lean_mk_string_unchecked("input", 5, 5);
x_38 = l_Lean_Name_mkStr3(x_35, x_36, x_37);
lean_inc(x_38);
x_39 = l_Lean_isTracingEnabledFor___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20_spec__20___redArg(x_38, x_3, x_5);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_140; 
x_41 = lean_ctor_get(x_39, 0);
x_42 = lean_ctor_get(x_39, 1);
x_43 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_format___lam__0___boxed), 5, 0);
x_44 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_format___lam__2___boxed), 1, 0);
x_45 = l_Std_instInhabitedFormat;
x_140 = lean_unbox(x_41);
lean_dec(x_41);
if (x_140 == 0)
{
lean_free_object(x_39);
lean_dec(x_38);
x_46 = x_3;
x_47 = x_4;
x_48 = x_42;
goto block_139;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_141 = lean_mk_string_unchecked("", 0, 0);
x_142 = l_Lean_stringToMessageData(x_141);
lean_dec(x_141);
x_143 = lean_box(0);
x_144 = lean_box(0);
x_145 = lean_unbox(x_144);
lean_inc(x_2);
x_146 = l_Lean_Syntax_formatStx(x_2, x_143, x_145);
x_147 = l_Lean_MessageData_ofFormat(x_146);
lean_inc(x_142);
lean_ctor_set_tag(x_39, 7);
lean_ctor_set(x_39, 1, x_147);
lean_ctor_set(x_39, 0, x_142);
x_148 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_148, 0, x_39);
lean_ctor_set(x_148, 1, x_142);
x_149 = l_Lean_addTrace___at___Lean_PrettyPrinter_format_spec__1(x_38, x_148, x_3, x_4, x_42);
x_150 = lean_ctor_get(x_149, 1);
lean_inc(x_150);
lean_dec(x_149);
x_46 = x_3;
x_47 = x_4;
x_48 = x_150;
goto block_139;
}
block_139:
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; lean_object* x_62; uint8_t x_63; 
x_49 = lean_st_ref_get(x_47, x_48);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = l_Lean_Syntax_Traverser_fromSyntax(x_2);
x_53 = lean_mk_string_unchecked("", 0, 0);
x_54 = lean_box(0);
x_55 = lean_box(1);
x_56 = lean_unsigned_to_nat(0u);
x_57 = lean_mk_empty_array_with_capacity(x_56);
x_58 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_58, 0, x_52);
lean_ctor_set(x_58, 1, x_53);
lean_ctor_set(x_58, 2, x_57);
x_59 = lean_unbox(x_54);
lean_ctor_set_uint8(x_58, sizeof(void*)*3, x_59);
x_60 = lean_unbox(x_54);
lean_ctor_set_uint8(x_58, sizeof(void*)*3 + 1, x_60);
x_61 = lean_unbox(x_55);
lean_ctor_set_uint8(x_58, sizeof(void*)*3 + 2, x_61);
x_62 = lean_st_mk_ref(x_58, x_51);
x_63 = !lean_is_exclusive(x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_64 = lean_ctor_get(x_62, 0);
x_65 = lean_ctor_get(x_62, 1);
x_66 = lean_ctor_get(x_50, 0);
lean_inc(x_66);
lean_dec(x_50);
x_67 = l_Lean_Parser_getTokenTable(x_66);
x_68 = l_Lean_PrettyPrinter_backtrackExceptionId;
x_69 = lean_ctor_get(x_46, 2);
lean_inc(x_69);
lean_inc(x_69);
lean_ctor_set(x_62, 1, x_67);
lean_ctor_set(x_62, 0, x_69);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_64);
x_70 = l_Lean_PrettyPrinter_Formatter_concat(x_1, x_62, x_64, x_46, x_47, x_65);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
lean_dec(x_70);
x_72 = lean_st_ref_get(x_64, x_71);
lean_dec(x_64);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_ctor_get(x_73, 2);
lean_inc(x_75);
lean_dec(x_73);
x_76 = lean_array_get(x_45, x_75, x_56);
lean_dec(x_75);
x_77 = l_Lean_PrettyPrinter_pp_oneline;
x_78 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_69, x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; 
lean_dec(x_69);
lean_dec(x_44);
lean_dec(x_43);
x_79 = lean_box(0);
x_80 = l_Lean_PrettyPrinter_format___lam__0(x_76, x_79, x_46, x_47, x_74);
x_28 = x_47;
x_29 = x_46;
x_30 = x_68;
x_31 = x_80;
goto block_34;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
lean_inc(x_76);
x_81 = l_Std_Format_pretty_x27(x_76, x_69);
lean_dec(x_69);
x_82 = lean_string_utf8_byte_size(x_81);
x_83 = l_Substring_takeWhileAux___at___Lean_PrettyPrinter_format_spec__0(x_78, x_81, x_82, x_56);
x_84 = l_Substring_takeRightWhileAux___at___Lean_PrettyPrinter_Formatter_pushToken_spec__1(x_78, x_81, x_83, x_82);
x_85 = lean_string_utf8_extract(x_81, x_83, x_84);
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_81);
x_86 = lean_string_utf8_byte_size(x_85);
x_87 = l_String_findAux(x_85, x_44, x_86, x_56);
x_88 = lean_nat_dec_lt(x_87, x_86);
lean_dec(x_86);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; 
lean_dec(x_87);
x_89 = lean_box(0);
lean_inc(x_47);
lean_inc(x_46);
x_90 = l_Lean_PrettyPrinter_format___lam__1(x_43, x_76, x_85, x_89, x_46, x_47, x_74);
lean_dec(x_76);
x_28 = x_47;
x_29 = x_46;
x_30 = x_68;
x_31 = x_90;
goto block_34;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_91 = lean_string_utf8_extract(x_85, x_56, x_87);
lean_dec(x_87);
lean_dec(x_85);
x_92 = lean_mk_string_unchecked(" [...]", 6, 6);
x_93 = lean_string_append(x_91, x_92);
lean_dec(x_92);
x_94 = lean_box(0);
lean_inc(x_47);
lean_inc(x_46);
x_95 = l_Lean_PrettyPrinter_format___lam__1(x_43, x_76, x_93, x_94, x_46, x_47, x_74);
lean_dec(x_76);
x_28 = x_47;
x_29 = x_46;
x_30 = x_68;
x_31 = x_95;
goto block_34;
}
}
}
else
{
uint8_t x_96; 
lean_dec(x_69);
lean_dec(x_64);
lean_dec(x_44);
lean_dec(x_43);
x_96 = !lean_is_exclusive(x_70);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_70, 0);
x_98 = lean_ctor_get(x_70, 1);
lean_inc(x_98);
lean_inc(x_97);
x_19 = x_47;
x_20 = x_68;
x_21 = x_46;
x_22 = x_70;
x_23 = x_97;
x_24 = x_98;
goto block_27;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_70, 0);
x_100 = lean_ctor_get(x_70, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_70);
lean_inc(x_100);
lean_inc(x_99);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
x_19 = x_47;
x_20 = x_68;
x_21 = x_46;
x_22 = x_101;
x_23 = x_99;
x_24 = x_100;
goto block_27;
}
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_102 = lean_ctor_get(x_62, 0);
x_103 = lean_ctor_get(x_62, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_62);
x_104 = lean_ctor_get(x_50, 0);
lean_inc(x_104);
lean_dec(x_50);
x_105 = l_Lean_Parser_getTokenTable(x_104);
x_106 = l_Lean_PrettyPrinter_backtrackExceptionId;
x_107 = lean_ctor_get(x_46, 2);
lean_inc(x_107);
lean_inc(x_107);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_105);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_102);
x_109 = l_Lean_PrettyPrinter_Formatter_concat(x_1, x_108, x_102, x_46, x_47, x_103);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; 
x_110 = lean_ctor_get(x_109, 1);
lean_inc(x_110);
lean_dec(x_109);
x_111 = lean_st_ref_get(x_102, x_110);
lean_dec(x_102);
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec(x_111);
x_114 = lean_ctor_get(x_112, 2);
lean_inc(x_114);
lean_dec(x_112);
x_115 = lean_array_get(x_45, x_114, x_56);
lean_dec(x_114);
x_116 = l_Lean_PrettyPrinter_pp_oneline;
x_117 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_107, x_116);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; 
lean_dec(x_107);
lean_dec(x_44);
lean_dec(x_43);
x_118 = lean_box(0);
x_119 = l_Lean_PrettyPrinter_format___lam__0(x_115, x_118, x_46, x_47, x_113);
x_28 = x_47;
x_29 = x_46;
x_30 = x_106;
x_31 = x_119;
goto block_34;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; 
lean_inc(x_115);
x_120 = l_Std_Format_pretty_x27(x_115, x_107);
lean_dec(x_107);
x_121 = lean_string_utf8_byte_size(x_120);
x_122 = l_Substring_takeWhileAux___at___Lean_PrettyPrinter_format_spec__0(x_117, x_120, x_121, x_56);
x_123 = l_Substring_takeRightWhileAux___at___Lean_PrettyPrinter_Formatter_pushToken_spec__1(x_117, x_120, x_122, x_121);
x_124 = lean_string_utf8_extract(x_120, x_122, x_123);
lean_dec(x_123);
lean_dec(x_122);
lean_dec(x_120);
x_125 = lean_string_utf8_byte_size(x_124);
x_126 = l_String_findAux(x_124, x_44, x_125, x_56);
x_127 = lean_nat_dec_lt(x_126, x_125);
lean_dec(x_125);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; 
lean_dec(x_126);
x_128 = lean_box(0);
lean_inc(x_47);
lean_inc(x_46);
x_129 = l_Lean_PrettyPrinter_format___lam__1(x_43, x_115, x_124, x_128, x_46, x_47, x_113);
lean_dec(x_115);
x_28 = x_47;
x_29 = x_46;
x_30 = x_106;
x_31 = x_129;
goto block_34;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_130 = lean_string_utf8_extract(x_124, x_56, x_126);
lean_dec(x_126);
lean_dec(x_124);
x_131 = lean_mk_string_unchecked(" [...]", 6, 6);
x_132 = lean_string_append(x_130, x_131);
lean_dec(x_131);
x_133 = lean_box(0);
lean_inc(x_47);
lean_inc(x_46);
x_134 = l_Lean_PrettyPrinter_format___lam__1(x_43, x_115, x_132, x_133, x_46, x_47, x_113);
lean_dec(x_115);
x_28 = x_47;
x_29 = x_46;
x_30 = x_106;
x_31 = x_134;
goto block_34;
}
}
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_dec(x_107);
lean_dec(x_102);
lean_dec(x_44);
lean_dec(x_43);
x_135 = lean_ctor_get(x_109, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_109, 1);
lean_inc(x_136);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_137 = x_109;
} else {
 lean_dec_ref(x_109);
 x_137 = lean_box(0);
}
lean_inc(x_136);
lean_inc(x_135);
if (lean_is_scalar(x_137)) {
 x_138 = lean_alloc_ctor(1, 2, 0);
} else {
 x_138 = x_137;
}
lean_ctor_set(x_138, 0, x_135);
lean_ctor_set(x_138, 1, x_136);
x_19 = x_47;
x_20 = x_106;
x_21 = x_46;
x_22 = x_138;
x_23 = x_135;
x_24 = x_136;
goto block_27;
}
}
}
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_212; 
x_151 = lean_ctor_get(x_39, 0);
x_152 = lean_ctor_get(x_39, 1);
lean_inc(x_152);
lean_inc(x_151);
lean_dec(x_39);
x_153 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_format___lam__0___boxed), 5, 0);
x_154 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_format___lam__2___boxed), 1, 0);
x_155 = l_Std_instInhabitedFormat;
x_212 = lean_unbox(x_151);
lean_dec(x_151);
if (x_212 == 0)
{
lean_dec(x_38);
x_156 = x_3;
x_157 = x_4;
x_158 = x_152;
goto block_211;
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; uint8_t x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_213 = lean_mk_string_unchecked("", 0, 0);
x_214 = l_Lean_stringToMessageData(x_213);
lean_dec(x_213);
x_215 = lean_box(0);
x_216 = lean_box(0);
x_217 = lean_unbox(x_216);
lean_inc(x_2);
x_218 = l_Lean_Syntax_formatStx(x_2, x_215, x_217);
x_219 = l_Lean_MessageData_ofFormat(x_218);
lean_inc(x_214);
x_220 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_220, 0, x_214);
lean_ctor_set(x_220, 1, x_219);
x_221 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_221, 0, x_220);
lean_ctor_set(x_221, 1, x_214);
x_222 = l_Lean_addTrace___at___Lean_PrettyPrinter_format_spec__1(x_38, x_221, x_3, x_4, x_152);
x_223 = lean_ctor_get(x_222, 1);
lean_inc(x_223);
lean_dec(x_222);
x_156 = x_3;
x_157 = x_4;
x_158 = x_223;
goto block_211;
}
block_211:
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; uint8_t x_169; uint8_t x_170; uint8_t x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_159 = lean_st_ref_get(x_157, x_158);
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
lean_dec(x_159);
x_162 = l_Lean_Syntax_Traverser_fromSyntax(x_2);
x_163 = lean_mk_string_unchecked("", 0, 0);
x_164 = lean_box(0);
x_165 = lean_box(1);
x_166 = lean_unsigned_to_nat(0u);
x_167 = lean_mk_empty_array_with_capacity(x_166);
x_168 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_168, 0, x_162);
lean_ctor_set(x_168, 1, x_163);
lean_ctor_set(x_168, 2, x_167);
x_169 = lean_unbox(x_164);
lean_ctor_set_uint8(x_168, sizeof(void*)*3, x_169);
x_170 = lean_unbox(x_164);
lean_ctor_set_uint8(x_168, sizeof(void*)*3 + 1, x_170);
x_171 = lean_unbox(x_165);
lean_ctor_set_uint8(x_168, sizeof(void*)*3 + 2, x_171);
x_172 = lean_st_mk_ref(x_168, x_161);
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
x_176 = lean_ctor_get(x_160, 0);
lean_inc(x_176);
lean_dec(x_160);
x_177 = l_Lean_Parser_getTokenTable(x_176);
x_178 = l_Lean_PrettyPrinter_backtrackExceptionId;
x_179 = lean_ctor_get(x_156, 2);
lean_inc(x_179);
lean_inc(x_179);
if (lean_is_scalar(x_175)) {
 x_180 = lean_alloc_ctor(0, 2, 0);
} else {
 x_180 = x_175;
}
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_177);
lean_inc(x_157);
lean_inc(x_156);
lean_inc(x_173);
x_181 = l_Lean_PrettyPrinter_Formatter_concat(x_1, x_180, x_173, x_156, x_157, x_174);
if (lean_obj_tag(x_181) == 0)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; uint8_t x_189; 
x_182 = lean_ctor_get(x_181, 1);
lean_inc(x_182);
lean_dec(x_181);
x_183 = lean_st_ref_get(x_173, x_182);
lean_dec(x_173);
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_183, 1);
lean_inc(x_185);
lean_dec(x_183);
x_186 = lean_ctor_get(x_184, 2);
lean_inc(x_186);
lean_dec(x_184);
x_187 = lean_array_get(x_155, x_186, x_166);
lean_dec(x_186);
x_188 = l_Lean_PrettyPrinter_pp_oneline;
x_189 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_179, x_188);
if (x_189 == 0)
{
lean_object* x_190; lean_object* x_191; 
lean_dec(x_179);
lean_dec(x_154);
lean_dec(x_153);
x_190 = lean_box(0);
x_191 = l_Lean_PrettyPrinter_format___lam__0(x_187, x_190, x_156, x_157, x_185);
x_28 = x_157;
x_29 = x_156;
x_30 = x_178;
x_31 = x_191;
goto block_34;
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; uint8_t x_199; 
lean_inc(x_187);
x_192 = l_Std_Format_pretty_x27(x_187, x_179);
lean_dec(x_179);
x_193 = lean_string_utf8_byte_size(x_192);
x_194 = l_Substring_takeWhileAux___at___Lean_PrettyPrinter_format_spec__0(x_189, x_192, x_193, x_166);
x_195 = l_Substring_takeRightWhileAux___at___Lean_PrettyPrinter_Formatter_pushToken_spec__1(x_189, x_192, x_194, x_193);
x_196 = lean_string_utf8_extract(x_192, x_194, x_195);
lean_dec(x_195);
lean_dec(x_194);
lean_dec(x_192);
x_197 = lean_string_utf8_byte_size(x_196);
x_198 = l_String_findAux(x_196, x_154, x_197, x_166);
x_199 = lean_nat_dec_lt(x_198, x_197);
lean_dec(x_197);
if (x_199 == 0)
{
lean_object* x_200; lean_object* x_201; 
lean_dec(x_198);
x_200 = lean_box(0);
lean_inc(x_157);
lean_inc(x_156);
x_201 = l_Lean_PrettyPrinter_format___lam__1(x_153, x_187, x_196, x_200, x_156, x_157, x_185);
lean_dec(x_187);
x_28 = x_157;
x_29 = x_156;
x_30 = x_178;
x_31 = x_201;
goto block_34;
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_202 = lean_string_utf8_extract(x_196, x_166, x_198);
lean_dec(x_198);
lean_dec(x_196);
x_203 = lean_mk_string_unchecked(" [...]", 6, 6);
x_204 = lean_string_append(x_202, x_203);
lean_dec(x_203);
x_205 = lean_box(0);
lean_inc(x_157);
lean_inc(x_156);
x_206 = l_Lean_PrettyPrinter_format___lam__1(x_153, x_187, x_204, x_205, x_156, x_157, x_185);
lean_dec(x_187);
x_28 = x_157;
x_29 = x_156;
x_30 = x_178;
x_31 = x_206;
goto block_34;
}
}
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
lean_dec(x_179);
lean_dec(x_173);
lean_dec(x_154);
lean_dec(x_153);
x_207 = lean_ctor_get(x_181, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_181, 1);
lean_inc(x_208);
if (lean_is_exclusive(x_181)) {
 lean_ctor_release(x_181, 0);
 lean_ctor_release(x_181, 1);
 x_209 = x_181;
} else {
 lean_dec_ref(x_181);
 x_209 = lean_box(0);
}
lean_inc(x_208);
lean_inc(x_207);
if (lean_is_scalar(x_209)) {
 x_210 = lean_alloc_ctor(1, 2, 0);
} else {
 x_210 = x_209;
}
lean_ctor_set(x_210, 0, x_207);
lean_ctor_set(x_210, 1, x_208);
x_19 = x_157;
x_20 = x_178;
x_21 = x_156;
x_22 = x_210;
x_23 = x_207;
x_24 = x_208;
goto block_27;
}
}
}
block_18:
{
if (x_12 == 0)
{
if (lean_obj_tag(x_8) == 0)
{
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
return x_7;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_8, 0);
lean_inc(x_13);
lean_dec(x_8);
x_14 = l___private_Lean_InternalExceptionId_0__Lean_beqInternalExceptionId____x40_Lean_InternalExceptionId___hyg_26_(x_11, x_13);
lean_dec(x_13);
lean_dec(x_11);
if (x_14 == 0)
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
return x_7;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_7);
x_15 = lean_mk_string_unchecked("format: uncaught backtrack exception", 36, 36);
x_16 = l_Lean_stringToMessageData(x_15);
lean_dec(x_15);
x_17 = l_Lean_throwError___at___Lean_throwUnknownIdentifier___at___Lean_throwUnknownConstant___at___Lean_filterFieldList___at___Lean_realizeGlobalConstCore_spec__0_spec__2_spec__2_spec__2___redArg(x_16, x_10, x_6, x_9);
lean_dec(x_6);
lean_dec(x_10);
return x_17;
}
}
}
else
{
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
return x_7;
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
x_6 = x_19;
x_7 = x_22;
x_8 = x_23;
x_9 = x_24;
x_10 = x_21;
x_11 = x_20;
x_12 = x_26;
goto block_18;
}
else
{
x_6 = x_19;
x_7 = x_22;
x_8 = x_23;
x_9 = x_24;
x_10 = x_21;
x_11 = x_20;
x_12 = x_25;
goto block_18;
}
}
block_34:
{
if (lean_obj_tag(x_31) == 0)
{
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
x_19 = x_28;
x_20 = x_30;
x_21 = x_29;
x_22 = x_31;
x_23 = x_32;
x_24 = x_33;
goto block_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_takeWhileAux___at___Lean_PrettyPrinter_format_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l_Substring_takeWhileAux___at___Lean_PrettyPrinter_format_spec__0(x_5, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_PrettyPrinter_format_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_addTrace___at___Lean_PrettyPrinter_format_spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_format___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_format___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_format___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_format___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_format___lam__2___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Lean_PrettyPrinter_format___lam__2(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_formatCategory(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_categoryFormatter), 6, 1);
lean_closure_set(x_6, 0, x_1);
x_7 = l_Lean_PrettyPrinter_format(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_formatTerm(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_mk_string_unchecked("term", 4, 4);
x_6 = l_Lean_Name_mkStr1(x_5);
x_7 = l_Lean_PrettyPrinter_formatCategory(x_6, x_1, x_2, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_formatTactic(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_mk_string_unchecked("tactic", 6, 6);
x_6 = l_Lean_Name_mkStr1(x_5);
x_7 = l_Lean_PrettyPrinter_formatCategory(x_6, x_1, x_2, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_formatCommand(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_mk_string_unchecked("command", 7, 7);
x_6 = l_Lean_Name_mkStr1(x_5);
x_7 = l_Lean_PrettyPrinter_formatCategory(x_6, x_1, x_2, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5637_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_2 = lean_mk_string_unchecked("PrettyPrinter", 13, 13);
x_3 = lean_mk_string_unchecked("format", 6, 6);
lean_inc(x_3);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(0);
x_6 = lean_box(0);
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
lean_inc(x_7);
x_8 = l_Lean_Name_str___override(x_6, x_7);
lean_inc(x_2);
x_9 = l_Lean_Name_str___override(x_8, x_2);
x_10 = lean_mk_string_unchecked("initFn", 6, 6);
x_11 = l_Lean_Name_str___override(x_9, x_10);
x_12 = lean_mk_string_unchecked("_@", 2, 2);
x_13 = l_Lean_Name_str___override(x_11, x_12);
x_14 = l_Lean_Name_str___override(x_13, x_7);
lean_inc(x_2);
x_15 = l_Lean_Name_str___override(x_14, x_2);
x_16 = lean_mk_string_unchecked("Formatter", 9, 9);
x_17 = l_Lean_Name_str___override(x_15, x_16);
x_18 = lean_mk_string_unchecked("_hyg", 4, 4);
x_19 = l_Lean_Name_str___override(x_17, x_18);
x_20 = lean_unsigned_to_nat(5637u);
x_21 = l_Lean_Name_num___override(x_19, x_20);
x_22 = lean_unbox(x_5);
lean_inc(x_21);
x_23 = l_Lean_registerTraceClass(x_4, x_22, x_21, x_1);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_mk_string_unchecked("backtrack", 9, 9);
lean_inc(x_3);
lean_inc(x_2);
x_26 = l_Lean_Name_mkStr3(x_2, x_3, x_25);
x_27 = lean_box(1);
x_28 = lean_unbox(x_27);
lean_inc(x_21);
x_29 = l_Lean_registerTraceClass(x_26, x_28, x_21, x_24);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_mk_string_unchecked("input", 5, 5);
x_32 = l_Lean_Name_mkStr3(x_2, x_3, x_31);
x_33 = lean_unbox(x_27);
x_34 = l_Lean_registerTraceClass(x_32, x_33, x_21, x_30);
return x_34;
}
else
{
lean_dec(x_21);
lean_dec(x_3);
lean_dec(x_2);
return x_29;
}
}
else
{
lean_dec(x_21);
lean_dec(x_3);
lean_dec(x_2);
return x_23;
}
}
}
lean_object* initialize_Lean_CoreM(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Parser_Extension(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Parser_StrInterpolation(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_KeyedDeclsAttribute(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_ParserCompiler_Attribute(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_PrettyPrinter_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_PrettyPrinter_Formatter(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_CoreM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Extension(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_StrInterpolation(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_KeyedDeclsAttribute(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ParserCompiler_Attribute(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_PrettyPrinter_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
if (builtin) {res = l_Lean_PrettyPrinter_mkFormatterAttribute(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_PrettyPrinter_formatterAttribute = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_PrettyPrinter_formatterAttribute);
lean_dec_ref(res);
}if (builtin) {res = l_Lean_PrettyPrinter_mkCombinatorFormatterAttribute(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_PrettyPrinter_combinatorFormatterAttribute = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_PrettyPrinter_combinatorFormatterAttribute);
lean_dec_ref(res);
}l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM = _init_l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM);
if (builtin) {res = l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5055_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_PrettyPrinter_Formatter_formatterAliasesRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_formatterAliasesRef);
lean_dec_ref(res);
}l_Lean_PrettyPrinter_Formatter_instCoeFormatterAliasValue = _init_l_Lean_PrettyPrinter_Formatter_instCoeFormatterAliasValue();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_instCoeFormatterAliasValue);
l_Lean_PrettyPrinter_Formatter_instCoeForallFormatterAliasValue = _init_l_Lean_PrettyPrinter_Formatter_instCoeForallFormatterAliasValue();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_instCoeForallFormatterAliasValue);
l_Lean_PrettyPrinter_Formatter_instCoeForallForallFormatterAliasValue = _init_l_Lean_PrettyPrinter_Formatter_instCoeForallForallFormatterAliasValue();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_instCoeForallForallFormatterAliasValue);
if (builtin) {res = l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5154_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_PrettyPrinter_pp_oneline = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_PrettyPrinter_pp_oneline);
lean_dec_ref(res);
}if (builtin) {res = l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5637_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
