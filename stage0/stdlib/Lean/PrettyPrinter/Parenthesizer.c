// Lean compiler output
// Module: Lean.PrettyPrinter.Parenthesizer
// Imports: Lean.Parser.Extension Lean.Parser.StrInterpolation Lean.ParserCompiler.Attribute Lean.PrettyPrinter.Basic Lean.PrettyPrinter.Delaborator.Options
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_recover_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_nameLitNoAntiquot_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_Traverser_down(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_withFn_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_paren(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_eoi_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_rawStx_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkKind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_strLitNoAntiquot_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_categoryParenthesizerAttribute;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_throwBacktrack___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_charLitNoAntiquot_parenthesizer___redArg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_formatStx(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_scientificLitNoAntiquot_parenthesizer___redArg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Syntax_setHeadInfo(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_sepBy1NoAntiquot_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_mkAntiquot_parenthesizer_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_registerAliasCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkStackTop_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_pushNone_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_parenthesizeTerm(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_nonReservedSymbolNoAntiquot_parenthesizer___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goRight___at___Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkLineEq_parenthesizer___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_strLitNoAntiquot_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_skip_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getHeadInfo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_addPrecCheck___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentD(lean_object*);
uint8_t l_Array_isEmpty___redArg(lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_unicodeSymbolNoAntiquot_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_rawStx_parenthesizer__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___Lean_PrettyPrinter_Parenthesizer_visitArgs_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___lam__0(lean_object*);
lean_object* l_Lean_Syntax_Traverser_fromSyntax(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkNoWsBefore_parenthesizer___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_withAntiquotSuffixSplice_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isAntiquotSuffixSplice(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_setCur___at___Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isTracingEnabledFor___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20_spec__20___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Array_reverse(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___Lean_PrettyPrinter_Parenthesizer_visitArgs_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_rawCh_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goUp___at___Lean_PrettyPrinter_Parenthesizer_visitArgs_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_unicodeSymbolNoAntiquot_parenthesizer___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_throwBacktrack___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_many1Unbox_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___Lean_PrettyPrinter_Parenthesizer_visitArgs_spec__2___redArg___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_ParserExtension_instInhabitedState;
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* lean_pretty_printer_parenthesizer_interpret_parser_descr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_fieldIdx_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goRight___at___Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_forM_loop___at___Lean_PrettyPrinter_Parenthesizer_manyNoAntiquot_parenthesizer_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_getPPParens(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkColGt_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkColEq_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_rawCh_parenthesizer(uint32_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___Lean_PrettyPrinter_Parenthesizer_visitArgs_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_parserOfStack_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_withAntiquotSuffixSplice_parenthesizer___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_unicodeSymbolNoAntiquot_parenthesizer___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_addPrecCheck(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkColEq_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getIdx___at___Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_lookahead_parenthesizer___redArg(lean_object*);
lean_object* l_Lean_Syntax_Traverser_left(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_withFn_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_symbolNoAntiquot_parenthesizer___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_identNoAntiquot_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_forM_loop___at___Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getIdx___at___Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_identNoAntiquot_parenthesizer___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkWsBefore_parenthesizer___redArg(lean_object*);
extern lean_object* l_instInhabitedNat;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_mkCombinatorParenthesizerAttribute(lean_object*);
uint8_t l___private_Lean_InternalExceptionId_0__Lean_beqInternalExceptionId____x40_Lean_InternalExceptionId___hyg_26_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_skip_parenthesizer___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_nameLitNoAntiquot_parenthesizer___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_pushNone_parenthesizer___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_skip_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_withPositionAfterLinebreak_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkColEq_parenthesizer___redArg(lean_object*);
lean_object* l_ReaderT_instMonad(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_pure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isAntiquot(lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkNoWsBefore_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_instOrElseParenthesizerM(lean_object*);
lean_object* l_Lean_Elab_addConstInfo___at___Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_4746_(lean_object*);
LEAN_EXPORT lean_object* l_Nat_forM_loop___at___Lean_PrettyPrinter_Parenthesizer_manyNoAntiquot_parenthesizer_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_interpolatedStr_parenthesizer___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_rawStx_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_forM_loop___at___Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_errorAtSavedPos_parenthesizer(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_getValues___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_PrettyPrinter_Parenthesizer_interpolatedStr_parenthesizer_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_visitToken___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkKind___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_visitArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___lam__0(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkColGe_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_range(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_sepByNoAntiquot_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_atomic_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_parenthesizerAttribute;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer_wrapParens(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM;
lean_object* l_Lean_Syntax_getKind(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_optionalNoAntiquot_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_fieldIdx_parenthesizer___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_rawCh_parenthesizer___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_error_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_error_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_rawStx_parenthesizer__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_identEq_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_scientificLitNoAntiquot_parenthesizer___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_rawStx_parenthesizer___redArg___boxed(lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_lookahead_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Attribute_Builtin_getIdent(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_parserExtension;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_back_x21(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_parserOfStack_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___Lean_PrettyPrinter_Parenthesizer_visitArgs_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_recover_x27_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_liftCoreM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkStackTop_parenthesizer___redArg(lean_object*);
lean_object* l_Lean_Syntax_Traverser_right(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_fieldIdx_parenthesizer___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkLinebreakBefore_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___Lean_PrettyPrinter_Parenthesizer_sepByNoAntiquot_parenthesizer_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_setTailInfo(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_symbolNoAntiquot_parenthesizer___redArg(lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___lam__3(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_symbolNoAntiquot_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_visitToken(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_error_parenthesizer___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_instCoeForallParenthesizerAliasValue___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_withPosition_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkColGt_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkTailWs_parenthesizer___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_addPrecCheck___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_errorAtSavedPos_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkNoImmediateColon_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_nonReservedSymbolNoAntiquot_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_notFollowedBy_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_numLitNoAntiquot_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ParenthesizerM_orElse___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailInfo(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkPrec_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_instCoeForallParenthesizerAliasValue;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkLinebreakBefore_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_interpolatedStr_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isTokenAntiquot(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_symbolNoAntiquot_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_back_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_lookahead_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_setCur___at___Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_eoi_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_manyNoAntiquot_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM;
lean_object* l_instMonadEIO___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getIdx___at___Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_forM_loop___at___Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkKind___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Core_instMonadQuotationCoreM;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_identEq_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_rawStx_parenthesizer___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_pushNone_parenthesizer___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goDown___at___Lean_PrettyPrinter_Parenthesizer_visitArgs_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goUp___at___Lean_PrettyPrinter_Parenthesizer_visitArgs_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_unicodeSymbolNoAntiquot_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goUp___at___Lean_PrettyPrinter_Parenthesizer_visitArgs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_eoi_parenthesizer___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goRight___at___Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goUp___at___Lean_PrettyPrinter_Parenthesizer_visitArgs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_identEq_parenthesizer___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_charLitNoAntiquot_parenthesizer___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lam__0(lean_object*);
lean_object* l_Lean_ParserCompiler_registerCombinatorAttribute(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_withFn_parenthesizer___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_nameLitNoAntiquot_parenthesizer___redArg(lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___Lean_throwUnknownIdentifier___at___Lean_throwUnknownConstant___at___Lean_filterFieldList___at___Lean_realizeGlobalConstCore_spec__0_spec__2_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_withoutInfo_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_PrettyPrinter_parenthesize_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_combinatorParenthesizerAttribute;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_addPrecCheck___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_numLitNoAntiquot_parenthesizer___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_parserOfStack_parenthesizer___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_scientificLitNoAntiquot_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_init___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkPrec_parenthesizer___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkColGe_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_forM_loop___at___Lean_PrettyPrinter_Parenthesizer_manyNoAntiquot_parenthesizer_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___Lean_PrettyPrinter_Parenthesizer_sepByNoAntiquot_parenthesizer_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadFunctor___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goDown___at___Lean_PrettyPrinter_Parenthesizer_visitArgs_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getIdx___at___Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_parenthesizerAliasesRef;
LEAN_EXPORT lean_object* l_Nat_forM_loop___at___Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_rawIdentNoAntiquot_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_errorAtSavedPos_parenthesizer___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkWsBefore_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goDown___at___Lean_PrettyPrinter_Parenthesizer_visitArgs_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_runForNodeKind___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___Lean_PrettyPrinter_Parenthesizer_visitArgs_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_strLitNoAntiquot_parenthesizer___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_rawIdentNoAntiquot_parenthesizer___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_identNoAntiquot_parenthesizer___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_parenthesizeCategory(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ParenthesizerM_orElse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkColGt_parenthesizer___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkNoImmediateColon_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goRight___at___Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_parenthesizeCommand(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_setCur___at___Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_instCoeParenthesizerAliasValue___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_rawStx_parenthesizer__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Syntax_setInfo(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonadLift(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_PrettyPrinter_parenthesize_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_Traverser_setCur(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_forM_loop___at___Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkTailWs_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_PrettyPrinter_backtrackExceptionId;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkTailWs_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkStackTop_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___Lean_PrettyPrinter_Parenthesizer_visitArgs_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkLinebreakBefore_parenthesizer___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_charLitNoAntiquot_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_withAntiquotSuffixSplice_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_instCoeForallForallParenthesizerAliasValue;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_4416_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_numLitNoAntiquot_parenthesizer___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkColGe_parenthesizer___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkPrec_parenthesizer___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_parenthesize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_seqRight(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_strLitNoAntiquot_parenthesizer___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer__1(lean_object*);
lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_tokenWithAntiquot_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goDown___at___Lean_PrettyPrinter_Parenthesizer_visitArgs_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_nonReservedSymbolNoAntiquot_parenthesizer___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_rawIdentNoAntiquot_parenthesizer___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_fieldIdx_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_withAntiquotSuffixSplice_parenthesizer___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_liftCoreM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_notFollowedBy_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_parserOfStack_parenthesizer___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_Traverser_up(lean_object*);
lean_object* lean_mk_antiquot_parenthesizer(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_identNoAntiquot_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_rawCh_parenthesizer___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_interpretParserDescr_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_forM_loop___at___Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedSyntax;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_identEq_parenthesizer___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_interpolatedStr_parenthesizer___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_rawIdentNoAntiquot_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___Lean_PrettyPrinter_Parenthesizer_visitArgs_spec__1___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_parenthesizeTactic(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_instCoeForallForallParenthesizerAliasValue___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkPrec_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_notFollowedBy_parenthesizer___redArg(lean_object*);
uint8_t l_Lean_Parser_isValidSyntaxNodeKind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkNoWsBefore_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkNoImmediateColon_parenthesizer___redArg(lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_setCur___at___Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_charLitNoAntiquot_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkKind___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_scientificLitNoAntiquot_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_nonReservedSymbolNoAntiquot_parenthesizer(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_hygieneInfoNoAntiquot_parenthesizer___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_numLitNoAntiquot_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkLineEq_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkWsBefore_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_hygieneInfoNoAntiquot_parenthesizer___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_hygieneInfoNoAntiquot_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadLift___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_hygieneInfoNoAntiquot_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_many1NoAntiquot_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_liftCoreM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_throwBacktrack(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKindUnsafe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isAntiquotSplice(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkLineEq_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_PrettyPrinter_Parenthesizer_interpolatedStr_parenthesizer_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___lam__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_forM_loop___at___Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_nameLitNoAntiquot_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_instCoeParenthesizerAliasValue;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_pushNone_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_registerAlias(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ParenthesizerM_orElse___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ParenthesizerM_orElse(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_instOrElseParenthesizerM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_ParenthesizerM_orElse), 8, 1);
lean_closure_set(x_2, 0, lean_box(0));
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___lam__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_25 = l_Lean_Elab_addConstInfo___at___Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(x_15, x_18, x_24, x_20, x_21, x_19);
lean_dec(x_21);
lean_dec(x_20);
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
x_20 = x_35;
x_21 = x_36;
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
x_20 = x_35;
x_21 = x_36;
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
x_58 = lean_mk_string_unchecked("invalid [parenthesizer] argument, unknown syntax kind '", 55, 55);
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_mkParenthesizerAttribute___lam__0___boxed), 5, 0);
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_mkParenthesizerAttribute___lam__1___boxed), 4, 0);
x_4 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_mkParenthesizerAttribute___lam__2___boxed), 6, 1);
lean_closure_set(x_4, 0, x_3);
x_5 = lean_mk_string_unchecked("builtin_parenthesizer", 21, 21);
x_6 = l_Lean_Name_mkStr1(x_5);
x_7 = lean_mk_string_unchecked("parenthesizer", 13, 13);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("Register a parenthesizer for a parser.\n\n  [parenthesizer k] registers a declaration of type `Lean.PrettyPrinter.Parenthesizer` for the `SyntaxNodeKind` `k`.", 156, 156);
x_10 = lean_mk_string_unchecked("Lean", 4, 4);
x_11 = lean_mk_string_unchecked("PrettyPrinter", 13, 13);
x_12 = lean_mk_string_unchecked("Parenthesizer", 13, 13);
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
x_15 = lean_mk_string_unchecked("parenthesizerAttribute", 22, 22);
x_16 = l_Lean_Name_mkStr3(x_10, x_11, x_15);
x_17 = l_Lean_KeyedDeclsAttribute_init___redArg(x_14, x_16, x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___lam__0(x_6, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___lam__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_2);
lean_dec(x_2);
x_8 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___lam__2(x_1, x_7, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT uint8_t l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_1);
lean_inc(x_7);
lean_inc(x_6);
x_13 = lean_apply_4(x_1, x_11, x_6, x_7, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Attribute_Builtin_getIdent(x_5, x_6, x_7, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Syntax_getId(x_17);
x_20 = l_Lean_Parser_parserExtension;
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_ctor_get_uint8(x_22, sizeof(void*)*3);
lean_dec(x_22);
x_24 = l_Lean_ScopedEnvExtension_getState___redArg(x_2, x_20, x_14, x_23);
x_25 = lean_ctor_get(x_24, 2);
lean_inc(x_25);
lean_dec(x_24);
x_26 = l_Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__1(lean_box(0), x_25, x_19);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_17);
lean_dec(x_1);
x_27 = lean_mk_string_unchecked("invalid [category_parenthesizer] argument, unknown parser category '", 68, 68);
x_28 = l_Lean_stringToMessageData(x_27);
lean_dec(x_27);
x_29 = lean_box(1);
x_30 = lean_unbox(x_29);
x_31 = l_Lean_Name_toString(x_19, x_30, x_3);
x_32 = l_Lean_stringToMessageData(x_31);
lean_dec(x_31);
lean_ctor_set_tag(x_9, 7);
lean_ctor_set(x_9, 1, x_32);
lean_ctor_set(x_9, 0, x_28);
x_33 = lean_mk_string_unchecked("'", 1, 1);
x_34 = l_Lean_stringToMessageData(x_33);
lean_dec(x_33);
x_35 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_35, 0, x_9);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_throwError___at___Lean_throwUnknownIdentifier___at___Lean_throwUnknownConstant___at___Lean_filterFieldList___at___Lean_realizeGlobalConstCore_spec__0_spec__2_spec__2_spec__2___redArg(x_35, x_6, x_7, x_18);
lean_dec(x_7);
lean_dec(x_6);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_free_object(x_9);
lean_dec(x_3);
x_37 = lean_ctor_get(x_26, 0);
lean_inc(x_37);
lean_dec(x_26);
x_38 = lean_st_ref_get(x_7, x_18);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_st_ref_get(x_7, x_40);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
lean_inc(x_7);
lean_inc(x_6);
x_44 = lean_apply_4(x_1, x_42, x_6, x_7, x_43);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_62; uint8_t x_63; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_47 = x_44;
} else {
 lean_dec_ref(x_44);
 x_47 = lean_box(0);
}
x_62 = lean_ctor_get(x_39, 6);
lean_inc(x_62);
lean_dec(x_39);
x_63 = lean_ctor_get_uint8(x_62, sizeof(void*)*3);
lean_dec(x_62);
if (x_63 == 0)
{
lean_dec(x_45);
x_48 = x_63;
goto block_61;
}
else
{
lean_object* x_64; uint8_t x_65; 
x_64 = lean_ctor_get(x_37, 0);
lean_inc(x_64);
x_65 = l_Lean_Environment_contains(x_45, x_64, x_63);
x_48 = x_65;
goto block_61;
}
block_61:
{
if (x_48 == 0)
{
lean_object* x_49; 
lean_dec(x_37);
lean_dec(x_17);
lean_dec(x_7);
lean_dec(x_6);
if (lean_is_scalar(x_47)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_47;
}
lean_ctor_set(x_49, 0, x_19);
lean_ctor_set(x_49, 1, x_46);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_47);
x_50 = lean_ctor_get(x_37, 0);
lean_inc(x_50);
lean_dec(x_37);
x_51 = lean_box(0);
x_52 = l_Lean_Elab_addConstInfo___at___Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(x_17, x_50, x_51, x_6, x_7, x_46);
lean_dec(x_7);
lean_dec(x_6);
if (lean_obj_tag(x_52) == 0)
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_52, 0);
lean_dec(x_54);
lean_ctor_set(x_52, 0, x_19);
return x_52;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_dec(x_52);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_19);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
else
{
uint8_t x_57; 
lean_dec(x_19);
x_57 = !lean_is_exclusive(x_52);
if (x_57 == 0)
{
return x_52;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_52, 0);
x_59 = lean_ctor_get(x_52, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_52);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
}
}
else
{
uint8_t x_66; 
lean_dec(x_39);
lean_dec(x_37);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_7);
lean_dec(x_6);
x_66 = !lean_is_exclusive(x_44);
if (x_66 == 0)
{
return x_44;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_44, 0);
x_68 = lean_ctor_get(x_44, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_44);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
}
else
{
uint8_t x_70; 
lean_dec(x_14);
lean_free_object(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_70 = !lean_is_exclusive(x_16);
if (x_70 == 0)
{
return x_16;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_16, 0);
x_72 = lean_ctor_get(x_16, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_16);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
else
{
uint8_t x_74; 
lean_free_object(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_9, 0);
x_79 = lean_ctor_get(x_9, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_9);
lean_inc(x_1);
lean_inc(x_7);
lean_inc(x_6);
x_80 = lean_apply_4(x_1, x_78, x_6, x_7, x_79);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_83 = l_Lean_Attribute_Builtin_getIdent(x_5, x_6, x_7, x_82);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_86 = l_Lean_Syntax_getId(x_84);
x_87 = l_Lean_Parser_parserExtension;
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
lean_dec(x_88);
x_90 = lean_ctor_get_uint8(x_89, sizeof(void*)*3);
lean_dec(x_89);
x_91 = l_Lean_ScopedEnvExtension_getState___redArg(x_2, x_87, x_81, x_90);
x_92 = lean_ctor_get(x_91, 2);
lean_inc(x_92);
lean_dec(x_91);
x_93 = l_Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__1(lean_box(0), x_92, x_86);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec(x_84);
lean_dec(x_1);
x_94 = lean_mk_string_unchecked("invalid [category_parenthesizer] argument, unknown parser category '", 68, 68);
x_95 = l_Lean_stringToMessageData(x_94);
lean_dec(x_94);
x_96 = lean_box(1);
x_97 = lean_unbox(x_96);
x_98 = l_Lean_Name_toString(x_86, x_97, x_3);
x_99 = l_Lean_stringToMessageData(x_98);
lean_dec(x_98);
x_100 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_100, 0, x_95);
lean_ctor_set(x_100, 1, x_99);
x_101 = lean_mk_string_unchecked("'", 1, 1);
x_102 = l_Lean_stringToMessageData(x_101);
lean_dec(x_101);
x_103 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_103, 0, x_100);
lean_ctor_set(x_103, 1, x_102);
x_104 = l_Lean_throwError___at___Lean_throwUnknownIdentifier___at___Lean_throwUnknownConstant___at___Lean_filterFieldList___at___Lean_realizeGlobalConstCore_spec__0_spec__2_spec__2_spec__2___redArg(x_103, x_6, x_7, x_85);
lean_dec(x_7);
lean_dec(x_6);
return x_104;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_3);
x_105 = lean_ctor_get(x_93, 0);
lean_inc(x_105);
lean_dec(x_93);
x_106 = lean_st_ref_get(x_7, x_85);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec(x_106);
x_109 = lean_st_ref_get(x_7, x_108);
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
lean_dec(x_109);
lean_inc(x_7);
lean_inc(x_6);
x_112 = lean_apply_4(x_1, x_110, x_6, x_7, x_111);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; lean_object* x_129; uint8_t x_130; 
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
x_129 = lean_ctor_get(x_107, 6);
lean_inc(x_129);
lean_dec(x_107);
x_130 = lean_ctor_get_uint8(x_129, sizeof(void*)*3);
lean_dec(x_129);
if (x_130 == 0)
{
lean_dec(x_113);
x_116 = x_130;
goto block_128;
}
else
{
lean_object* x_131; uint8_t x_132; 
x_131 = lean_ctor_get(x_105, 0);
lean_inc(x_131);
x_132 = l_Lean_Environment_contains(x_113, x_131, x_130);
x_116 = x_132;
goto block_128;
}
block_128:
{
if (x_116 == 0)
{
lean_object* x_117; 
lean_dec(x_105);
lean_dec(x_84);
lean_dec(x_7);
lean_dec(x_6);
if (lean_is_scalar(x_115)) {
 x_117 = lean_alloc_ctor(0, 2, 0);
} else {
 x_117 = x_115;
}
lean_ctor_set(x_117, 0, x_86);
lean_ctor_set(x_117, 1, x_114);
return x_117;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec(x_115);
x_118 = lean_ctor_get(x_105, 0);
lean_inc(x_118);
lean_dec(x_105);
x_119 = lean_box(0);
x_120 = l_Lean_Elab_addConstInfo___at___Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0(x_84, x_118, x_119, x_6, x_7, x_114);
lean_dec(x_7);
lean_dec(x_6);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_120, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_122 = x_120;
} else {
 lean_dec_ref(x_120);
 x_122 = lean_box(0);
}
if (lean_is_scalar(x_122)) {
 x_123 = lean_alloc_ctor(0, 2, 0);
} else {
 x_123 = x_122;
}
lean_ctor_set(x_123, 0, x_86);
lean_ctor_set(x_123, 1, x_121);
return x_123;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_86);
x_124 = lean_ctor_get(x_120, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_120, 1);
lean_inc(x_125);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_126 = x_120;
} else {
 lean_dec_ref(x_120);
 x_126 = lean_box(0);
}
if (lean_is_scalar(x_126)) {
 x_127 = lean_alloc_ctor(1, 2, 0);
} else {
 x_127 = x_126;
}
lean_ctor_set(x_127, 0, x_124);
lean_ctor_set(x_127, 1, x_125);
return x_127;
}
}
}
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec(x_107);
lean_dec(x_105);
lean_dec(x_86);
lean_dec(x_84);
lean_dec(x_7);
lean_dec(x_6);
x_133 = lean_ctor_get(x_112, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_112, 1);
lean_inc(x_134);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 x_135 = x_112;
} else {
 lean_dec_ref(x_112);
 x_135 = lean_box(0);
}
if (lean_is_scalar(x_135)) {
 x_136 = lean_alloc_ctor(1, 2, 0);
} else {
 x_136 = x_135;
}
lean_ctor_set(x_136, 0, x_133);
lean_ctor_set(x_136, 1, x_134);
return x_136;
}
}
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_dec(x_81);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_137 = lean_ctor_get(x_83, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_83, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_139 = x_83;
} else {
 lean_dec_ref(x_83);
 x_139 = lean_box(0);
}
if (lean_is_scalar(x_139)) {
 x_140 = lean_alloc_ctor(1, 2, 0);
} else {
 x_140 = x_139;
}
lean_ctor_set(x_140, 0, x_137);
lean_ctor_set(x_140, 1, x_138);
return x_140;
}
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_141 = lean_ctor_get(x_80, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_80, 1);
lean_inc(x_142);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_143 = x_80;
} else {
 lean_dec_ref(x_80);
 x_143 = lean_box(0);
}
if (lean_is_scalar(x_143)) {
 x_144 = lean_alloc_ctor(1, 2, 0);
} else {
 x_144 = x_143;
}
lean_ctor_set(x_144, 0, x_141);
lean_ctor_set(x_144, 1, x_142);
return x_144;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___lam__0___boxed), 1, 0);
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_mkParenthesizerAttribute___lam__1___boxed), 4, 0);
x_4 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_mkParenthesizerAttribute___lam__0___boxed), 5, 0);
x_5 = l_Lean_Parser_ParserExtension_instInhabitedState;
x_6 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___lam__3___boxed), 8, 3);
lean_closure_set(x_6, 0, x_3);
lean_closure_set(x_6, 1, x_5);
lean_closure_set(x_6, 2, x_2);
x_7 = lean_mk_string_unchecked("builtin_category_parenthesizer", 30, 30);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("category_parenthesizer", 22, 22);
x_10 = l_Lean_Name_mkStr1(x_9);
x_11 = lean_mk_string_unchecked("Register a parenthesizer for a syntax category.\n\n  [category_parenthesizer cat] registers a declaration of type `Lean.PrettyPrinter.CategoryParenthesizer` for the category `cat`,\n  which is used when parenthesizing calls of `categoryParser cat prec`. Implementations should call `maybeParenthesize`\n  with the precedence and `cat`. If no category parenthesizer is registered, the category will never be parenthesized,\n  but still be traversed for parenthesizing nested categories.", 480, 480);
x_12 = lean_mk_string_unchecked("Lean", 4, 4);
x_13 = lean_mk_string_unchecked("PrettyPrinter", 13, 13);
x_14 = lean_mk_string_unchecked("CategoryParenthesizer", 21, 21);
lean_inc(x_13);
lean_inc(x_12);
x_15 = l_Lean_Name_mkStr3(x_12, x_13, x_14);
x_16 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_16, 0, x_8);
lean_ctor_set(x_16, 1, x_10);
lean_ctor_set(x_16, 2, x_11);
lean_ctor_set(x_16, 3, x_15);
lean_ctor_set(x_16, 4, x_6);
lean_ctor_set(x_16, 5, x_4);
x_17 = lean_mk_string_unchecked("categoryParenthesizerAttribute", 30, 30);
x_18 = l_Lean_Name_mkStr3(x_12, x_13, x_17);
x_19 = l_Lean_KeyedDeclsAttribute_init___redArg(x_16, x_18, x_1);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_4);
lean_dec(x_4);
x_10 = l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___lam__3(x_1, x_2, x_3, x_9, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_mkCombinatorParenthesizerAttribute(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("combinator_parenthesizer", 24, 24);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_mk_string_unchecked("Register a parenthesizer for a parser combinator.\n\n  [combinator_parenthesizer c] registers a declaration of type `Lean.PrettyPrinter.Parenthesizer` for the `Parser` declaration `c`.\n  Note that, unlike with [parenthesizer], this is not a node kind since combinators usually do not introduce their own node kinds.\n  The tagged declaration may optionally accept parameters corresponding to (a prefix of) those of `c`, where `Parser` is replaced\n  with `Parenthesizer` in the parameter types.", 490, 490);
x_5 = lean_mk_string_unchecked("Lean", 4, 4);
x_6 = lean_mk_string_unchecked("PrettyPrinter", 13, 13);
x_7 = lean_mk_string_unchecked("mkCombinatorParenthesizerAttribute", 34, 34);
x_8 = l_Lean_Name_mkStr3(x_5, x_6, x_7);
x_9 = l_Lean_ParserCompiler_registerCombinatorAttribute(x_3, x_4, x_8, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_throwBacktrack___redArg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_throwBacktrack(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Parenthesizer_throwBacktrack___redArg(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_throwBacktrack___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Parenthesizer_throwBacktrack(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_7 = lean_st_ref_take(x_3, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_8, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_8, 3);
lean_inc(x_12);
x_13 = lean_ctor_get(x_8, 4);
lean_inc(x_13);
x_14 = lean_ctor_get(x_8, 5);
lean_inc(x_14);
x_15 = lean_ctor_get_uint8(x_8, sizeof(void*)*6);
lean_dec(x_8);
x_16 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_10);
lean_ctor_set(x_16, 2, x_11);
lean_ctor_set(x_16, 3, x_12);
lean_ctor_set(x_16, 4, x_13);
lean_ctor_set(x_16, 5, x_14);
lean_ctor_set_uint8(x_16, sizeof(void*)*6, x_15);
x_17 = lean_st_ref_set(x_3, x_16, x_9);
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
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
x_16 = lean_ctor_get(x_9, 2);
lean_inc(x_16);
x_17 = lean_ctor_get(x_9, 3);
lean_inc(x_17);
x_18 = lean_ctor_get(x_9, 4);
lean_inc(x_18);
x_19 = lean_ctor_get(x_9, 5);
lean_inc(x_19);
x_20 = lean_ctor_get_uint8(x_9, sizeof(void*)*6);
lean_dec(x_9);
x_21 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_21, 0, x_14);
lean_ctor_set(x_21, 1, x_15);
lean_ctor_set(x_21, 2, x_16);
lean_ctor_set(x_21, 3, x_17);
lean_ctor_set(x_21, 4, x_18);
lean_ctor_set(x_21, 5, x_19);
lean_ctor_set_uint8(x_21, sizeof(void*)*6, x_20);
x_22 = lean_st_ref_set(x_4, x_21, x_10);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
lean_ctor_set(x_22, 0, x_13);
return x_22;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_13);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___lam__0___boxed), 5, 0);
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___lam__1___boxed), 6, 0);
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___lam__2___boxed), 7, 0);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___lam__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_addPrecCheck___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_28; lean_object* x_35; lean_object* x_38; 
x_4 = lean_st_ref_take(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_box(0);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
x_38 = lean_ctor_get(x_5, 1);
lean_inc(x_38);
if (lean_obj_tag(x_38) == 0)
{
lean_inc(x_1);
x_35 = x_1;
goto block_37;
}
else
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
lean_dec(x_38);
x_35 = x_39;
goto block_37;
}
block_22:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_ctor_get(x_5, 4);
lean_inc(x_13);
x_14 = lean_ctor_get(x_5, 5);
lean_inc(x_14);
x_15 = lean_ctor_get_uint8(x_5, sizeof(void*)*6);
lean_dec(x_5);
x_16 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_16, 0, x_8);
lean_ctor_set(x_16, 1, x_10);
lean_ctor_set(x_16, 2, x_9);
lean_ctor_set(x_16, 3, x_12);
lean_ctor_set(x_16, 4, x_13);
lean_ctor_set(x_16, 5, x_14);
lean_ctor_set_uint8(x_16, sizeof(void*)*6, x_15);
x_17 = lean_st_ref_set(x_2, x_16, x_6);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
lean_ctor_set(x_17, 0, x_7);
return x_17;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_7);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
block_27:
{
uint8_t x_26; 
x_26 = lean_nat_dec_le(x_25, x_1);
if (x_26 == 0)
{
lean_dec(x_25);
x_9 = x_23;
x_10 = x_24;
x_11 = x_1;
goto block_22;
}
else
{
lean_dec(x_1);
x_9 = x_23;
x_10 = x_24;
x_11 = x_25;
goto block_22;
}
}
block_34:
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_ctor_get(x_5, 3);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_5, 2);
lean_inc(x_31);
lean_inc(x_1);
x_23 = x_31;
x_24 = x_29;
x_25 = x_1;
goto block_27;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_5, 2);
lean_inc(x_32);
x_33 = lean_ctor_get(x_30, 0);
lean_inc(x_33);
lean_dec(x_30);
x_23 = x_32;
x_24 = x_29;
x_25 = x_33;
goto block_27;
}
}
block_37:
{
uint8_t x_36; 
x_36 = lean_nat_dec_le(x_35, x_1);
if (x_36 == 0)
{
lean_dec(x_35);
lean_inc(x_1);
x_28 = x_1;
goto block_34;
}
else
{
x_28 = x_35;
goto block_34;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_addPrecCheck(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Parenthesizer_addPrecCheck___redArg(x_1, x_3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_addPrecCheck___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PrettyPrinter_Parenthesizer_addPrecCheck___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_addPrecCheck___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Parenthesizer_addPrecCheck(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goUp___at___Lean_PrettyPrinter_Parenthesizer_visitArgs_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
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
x_9 = lean_ctor_get(x_4, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 3);
lean_inc(x_10);
x_11 = lean_ctor_get(x_4, 4);
lean_inc(x_11);
x_12 = lean_ctor_get(x_4, 5);
lean_inc(x_12);
x_13 = lean_ctor_get_uint8(x_4, sizeof(void*)*6);
lean_dec(x_4);
x_14 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_8);
lean_ctor_set(x_14, 2, x_9);
lean_ctor_set(x_14, 3, x_10);
lean_ctor_set(x_14, 4, x_11);
lean_ctor_set(x_14, 5, x_12);
lean_ctor_set_uint8(x_14, sizeof(void*)*6, x_13);
x_15 = lean_st_ref_set(x_1, x_14, x_5);
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
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goUp___at___Lean_PrettyPrinter_Parenthesizer_visitArgs_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Syntax_MonadTraverser_goUp___at___Lean_PrettyPrinter_Parenthesizer_visitArgs_spec__0___redArg(x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___Lean_PrettyPrinter_Parenthesizer_visitArgs_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
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
x_9 = lean_ctor_get(x_4, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 3);
lean_inc(x_10);
x_11 = lean_ctor_get(x_4, 4);
lean_inc(x_11);
x_12 = lean_ctor_get(x_4, 5);
lean_inc(x_12);
x_13 = lean_ctor_get_uint8(x_4, sizeof(void*)*6);
lean_dec(x_4);
x_14 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_8);
lean_ctor_set(x_14, 2, x_9);
lean_ctor_set(x_14, 3, x_10);
lean_ctor_set(x_14, 4, x_11);
lean_ctor_set(x_14, 5, x_12);
lean_ctor_set_uint8(x_14, sizeof(void*)*6, x_13);
x_15 = lean_st_ref_set(x_1, x_14, x_5);
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
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___Lean_PrettyPrinter_Parenthesizer_visitArgs_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Syntax_MonadTraverser_goLeft___at___Lean_PrettyPrinter_Parenthesizer_visitArgs_spec__1___redArg(x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___Lean_PrettyPrinter_Parenthesizer_visitArgs_spec__2___redArg(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___Lean_PrettyPrinter_Parenthesizer_visitArgs_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Syntax_MonadTraverser_getCur___at___Lean_PrettyPrinter_Parenthesizer_visitArgs_spec__2___redArg(x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goDown___at___Lean_PrettyPrinter_Parenthesizer_visitArgs_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
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
x_10 = lean_ctor_get(x_5, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_5, 3);
lean_inc(x_11);
x_12 = lean_ctor_get(x_5, 4);
lean_inc(x_12);
x_13 = lean_ctor_get(x_5, 5);
lean_inc(x_13);
x_14 = lean_ctor_get_uint8(x_5, sizeof(void*)*6);
lean_dec(x_5);
x_15 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_9);
lean_ctor_set(x_15, 2, x_10);
lean_ctor_set(x_15, 3, x_11);
lean_ctor_set(x_15, 4, x_12);
lean_ctor_set(x_15, 5, x_13);
lean_ctor_set_uint8(x_15, sizeof(void*)*6, x_14);
x_16 = lean_st_ref_set(x_2, x_15, x_6);
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
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goDown___at___Lean_PrettyPrinter_Parenthesizer_visitArgs_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Syntax_MonadTraverser_goDown___at___Lean_PrettyPrinter_Parenthesizer_visitArgs_spec__3___redArg(x_1, x_3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_visitArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_7 = l_Lean_Syntax_MonadTraverser_getCur___at___Lean_PrettyPrinter_Parenthesizer_visitArgs_spec__2___redArg(x_3, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Lean_Syntax_getArgs(x_8);
lean_dec(x_8);
x_12 = lean_array_get_size(x_11);
lean_dec(x_11);
x_13 = lean_nat_dec_lt(x_10, x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_14 = l_Lean_Syntax_MonadTraverser_goLeft___at___Lean_PrettyPrinter_Parenthesizer_visitArgs_spec__1___redArg(x_3, x_9);
lean_dec(x_3);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_12, x_15);
lean_dec(x_12);
x_17 = l_Lean_Syntax_MonadTraverser_goDown___at___Lean_PrettyPrinter_Parenthesizer_visitArgs_spec__3___redArg(x_16, x_3, x_9);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
lean_inc(x_3);
x_19 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = l_Lean_Syntax_MonadTraverser_goUp___at___Lean_PrettyPrinter_Parenthesizer_visitArgs_spec__0___redArg(x_3, x_20);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Lean_Syntax_MonadTraverser_goLeft___at___Lean_PrettyPrinter_Parenthesizer_visitArgs_spec__1___redArg(x_3, x_22);
lean_dec(x_3);
return x_23;
}
else
{
lean_dec(x_3);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goUp___at___Lean_PrettyPrinter_Parenthesizer_visitArgs_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_MonadTraverser_goUp___at___Lean_PrettyPrinter_Parenthesizer_visitArgs_spec__0___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goUp___at___Lean_PrettyPrinter_Parenthesizer_visitArgs_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Syntax_MonadTraverser_goUp___at___Lean_PrettyPrinter_Parenthesizer_visitArgs_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___Lean_PrettyPrinter_Parenthesizer_visitArgs_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_MonadTraverser_goLeft___at___Lean_PrettyPrinter_Parenthesizer_visitArgs_spec__1___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___Lean_PrettyPrinter_Parenthesizer_visitArgs_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Syntax_MonadTraverser_goLeft___at___Lean_PrettyPrinter_Parenthesizer_visitArgs_spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___Lean_PrettyPrinter_Parenthesizer_visitArgs_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_MonadTraverser_getCur___at___Lean_PrettyPrinter_Parenthesizer_visitArgs_spec__2___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___Lean_PrettyPrinter_Parenthesizer_visitArgs_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Syntax_MonadTraverser_getCur___at___Lean_PrettyPrinter_Parenthesizer_visitArgs_spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goDown___at___Lean_PrettyPrinter_Parenthesizer_visitArgs_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Syntax_MonadTraverser_goDown___at___Lean_PrettyPrinter_Parenthesizer_visitArgs_spec__3___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goDown___at___Lean_PrettyPrinter_Parenthesizer_visitArgs_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Syntax_MonadTraverser_goDown___at___Lean_PrettyPrinter_Parenthesizer_visitArgs_spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_apply_5(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___lam__0), 7, 0);
x_2 = lean_alloc_closure((void*)(l_ReaderT_instMonadFunctor___lam__0), 4, 0);
x_3 = lean_alloc_closure((void*)(l_ReaderT_instMonadLift___lam__0___boxed), 3, 0);
x_4 = l_StateRefT_x27_instMonadLift(lean_box(0), lean_box(0), lean_box(0));
x_5 = l_Lean_Core_instMonadQuotationCoreM;
lean_inc(x_2);
x_6 = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(x_2, x_4, x_5);
x_7 = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(x_2, x_3, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
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
x_30 = lean_box(0);
lean_inc(x_29);
x_31 = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 5);
lean_closure_set(x_31, 0, lean_box(0));
lean_closure_set(x_31, 1, lean_box(0));
lean_closure_set(x_31, 2, x_29);
lean_closure_set(x_31, 3, lean_box(0));
lean_closure_set(x_31, 4, x_30);
x_32 = lean_box(0);
x_33 = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 5);
lean_closure_set(x_33, 0, lean_box(0));
lean_closure_set(x_33, 1, lean_box(0));
lean_closure_set(x_33, 2, x_29);
lean_closure_set(x_33, 3, lean_box(0));
lean_closure_set(x_33, 4, x_32);
x_34 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_34, 0, x_8);
lean_ctor_set(x_34, 1, x_31);
lean_ctor_set(x_34, 2, x_33);
lean_ctor_set(x_34, 3, x_1);
return x_34;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getIdx___at___Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_st_ref_get(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_6, 2);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Array_back_x3f(lean_box(0), x_7);
lean_dec(x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = lean_unsigned_to_nat(0u);
lean_ctor_set(x_3, 0, x_9);
return x_3;
}
else
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
lean_ctor_set(x_3, 0, x_10);
return x_3;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_13, 2);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Array_back_x3f(lean_box(0), x_14);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_12);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_12);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getIdx___at___Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Syntax_MonadTraverser_getIdx___at___Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_spec__0___redArg(x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_setCur___at___Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_4 = lean_st_ref_take(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = l_Lean_Syntax_Traverser_setCur(x_7, x_1);
lean_dec(x_7);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_5, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_5, 3);
lean_inc(x_11);
x_12 = lean_ctor_get(x_5, 4);
lean_inc(x_12);
x_13 = lean_ctor_get(x_5, 5);
lean_inc(x_13);
x_14 = lean_ctor_get_uint8(x_5, sizeof(void*)*6);
lean_dec(x_5);
x_15 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_9);
lean_ctor_set(x_15, 2, x_10);
lean_ctor_set(x_15, 3, x_11);
lean_ctor_set(x_15, 4, x_12);
lean_ctor_set(x_15, 5, x_13);
lean_ctor_set_uint8(x_15, sizeof(void*)*6, x_14);
x_16 = lean_st_ref_set(x_2, x_15, x_6);
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
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_setCur___at___Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Syntax_MonadTraverser_setCur___at___Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_spec__1___redArg(x_1, x_3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_isTracingEnabledFor___at___Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_spec__2___redArg(x_1, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_addTrace___at___Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_spec__3___redArg(x_1, x_2, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goRight___at___Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_spec__4___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_3 = lean_st_ref_take(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = l_Lean_Syntax_Traverser_right(x_6);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_4, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 3);
lean_inc(x_10);
x_11 = lean_ctor_get(x_4, 4);
lean_inc(x_11);
x_12 = lean_ctor_get(x_4, 5);
lean_inc(x_12);
x_13 = lean_ctor_get_uint8(x_4, sizeof(void*)*6);
lean_dec(x_4);
x_14 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_8);
lean_ctor_set(x_14, 2, x_9);
lean_ctor_set(x_14, 3, x_10);
lean_ctor_set(x_14, 4, x_11);
lean_ctor_set(x_14, 5, x_12);
lean_ctor_set_uint8(x_14, sizeof(void*)*6, x_13);
x_15 = lean_st_ref_set(x_1, x_14, x_5);
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
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goRight___at___Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Syntax_MonadTraverser_goRight___at___Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_spec__4___redArg(x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_47; 
x_31 = lean_st_ref_get(x_6, x_9);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_47 = lean_ctor_get_uint8(x_1, sizeof(void*)*6);
if (x_47 == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_32, 4);
lean_inc(x_48);
lean_dec(x_32);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; 
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_3);
x_34 = x_49;
goto block_46;
}
else
{
lean_object* x_50; uint8_t x_51; 
x_50 = lean_ctor_get(x_48, 0);
lean_inc(x_50);
x_51 = lean_nat_dec_le(x_50, x_3);
lean_dec(x_50);
if (x_51 == 0)
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_48);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_48, 0);
lean_dec(x_53);
lean_ctor_set(x_48, 0, x_3);
x_34 = x_48;
goto block_46;
}
else
{
lean_object* x_54; 
lean_dec(x_48);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_3);
x_34 = x_54;
goto block_46;
}
}
else
{
lean_dec(x_3);
x_34 = x_48;
goto block_46;
}
}
}
else
{
uint8_t x_55; 
lean_dec(x_3);
lean_dec(x_2);
x_55 = !lean_is_exclusive(x_32);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; lean_object* x_72; lean_object* x_73; 
x_56 = lean_ctor_get(x_32, 5);
lean_dec(x_56);
x_57 = lean_ctor_get(x_32, 4);
lean_dec(x_57);
x_58 = lean_ctor_get(x_32, 3);
lean_dec(x_58);
x_59 = lean_ctor_get(x_32, 2);
lean_dec(x_59);
x_60 = lean_ctor_get(x_32, 1);
lean_dec(x_60);
x_61 = lean_ctor_get(x_32, 0);
lean_dec(x_61);
x_62 = lean_st_ref_take(x_6, x_33);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = lean_ctor_get(x_63, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_63, 1);
lean_inc(x_66);
x_67 = lean_ctor_get(x_63, 2);
lean_inc(x_67);
x_68 = lean_ctor_get(x_63, 3);
lean_inc(x_68);
x_69 = lean_ctor_get(x_1, 4);
x_70 = lean_ctor_get(x_1, 5);
x_71 = lean_ctor_get_uint8(x_63, sizeof(void*)*6);
lean_dec(x_63);
lean_inc(x_70);
lean_inc(x_69);
lean_ctor_set(x_32, 5, x_70);
lean_ctor_set(x_32, 4, x_69);
lean_ctor_set(x_32, 3, x_68);
lean_ctor_set(x_32, 2, x_67);
lean_ctor_set(x_32, 1, x_66);
lean_ctor_set(x_32, 0, x_65);
lean_ctor_set_uint8(x_32, sizeof(void*)*6, x_71);
x_72 = lean_st_ref_set(x_6, x_32, x_64);
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec(x_72);
x_10 = x_6;
x_11 = x_73;
goto block_30;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_32);
x_74 = lean_st_ref_take(x_6, x_33);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = lean_ctor_get(x_75, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_75, 1);
lean_inc(x_78);
x_79 = lean_ctor_get(x_75, 2);
lean_inc(x_79);
x_80 = lean_ctor_get(x_75, 3);
lean_inc(x_80);
x_81 = lean_ctor_get(x_1, 4);
x_82 = lean_ctor_get(x_1, 5);
x_83 = lean_ctor_get_uint8(x_75, sizeof(void*)*6);
lean_dec(x_75);
lean_inc(x_82);
lean_inc(x_81);
x_84 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_84, 0, x_77);
lean_ctor_set(x_84, 1, x_78);
lean_ctor_set(x_84, 2, x_79);
lean_ctor_set(x_84, 3, x_80);
lean_ctor_set(x_84, 4, x_81);
lean_ctor_set(x_84, 5, x_82);
lean_ctor_set_uint8(x_84, sizeof(void*)*6, x_83);
x_85 = lean_st_ref_set(x_6, x_84, x_76);
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
lean_dec(x_85);
x_10 = x_6;
x_11 = x_86;
goto block_30;
}
}
block_30:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_12 = lean_st_ref_take(x_10, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_13, 2);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 3);
x_19 = lean_ctor_get(x_13, 4);
lean_inc(x_19);
x_20 = lean_ctor_get(x_13, 5);
lean_inc(x_20);
x_21 = lean_ctor_get_uint8(x_13, sizeof(void*)*6);
lean_dec(x_13);
lean_inc(x_18);
x_22 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_22, 0, x_15);
lean_ctor_set(x_22, 1, x_16);
lean_ctor_set(x_22, 2, x_17);
lean_ctor_set(x_22, 3, x_18);
lean_ctor_set(x_22, 4, x_19);
lean_ctor_set(x_22, 5, x_20);
lean_ctor_set_uint8(x_22, sizeof(void*)*6, x_21);
x_23 = lean_st_ref_set(x_10, x_22, x_14);
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
block_46:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_35 = lean_st_ref_take(x_6, x_33);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_ctor_get(x_36, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_36, 2);
lean_inc(x_40);
x_41 = lean_ctor_get(x_36, 3);
lean_inc(x_41);
x_42 = lean_ctor_get_uint8(x_36, sizeof(void*)*6);
lean_dec(x_36);
x_43 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_43, 0, x_38);
lean_ctor_set(x_43, 1, x_39);
lean_ctor_set(x_43, 2, x_40);
lean_ctor_set(x_43, 3, x_41);
lean_ctor_set(x_43, 4, x_34);
lean_ctor_set(x_43, 5, x_2);
lean_ctor_set_uint8(x_43, sizeof(void*)*6, x_42);
x_44 = lean_st_ref_set(x_6, x_43, x_37);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_10 = x_6;
x_11 = x_45;
goto block_30;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_630; lean_object* x_631; uint8_t x_632; 
x_11 = l_Lean_Syntax_MonadTraverser_getCur___at___Lean_PrettyPrinter_Parenthesizer_visitArgs_spec__2___redArg(x_7, x_10);
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
x_15 = l_Lean_Syntax_MonadTraverser_getIdx___at___Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_spec__0___redArg(x_7, x_13);
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
x_19 = lean_st_ref_get(x_7, x_17);
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
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
x_24 = lean_box(0);
x_25 = lean_box(0);
x_26 = lean_box(0);
lean_inc(x_23);
x_27 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_27, 0, x_23);
lean_ctor_set(x_27, 1, x_24);
lean_ctor_set(x_27, 2, x_25);
lean_ctor_set(x_27, 3, x_24);
lean_ctor_set(x_27, 4, x_24);
lean_ctor_set(x_27, 5, x_25);
x_28 = lean_unbox(x_26);
lean_ctor_set_uint8(x_27, sizeof(void*)*6, x_28);
x_29 = lean_st_ref_set(x_7, x_27, x_21);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_31 = x_29;
} else {
 lean_dec_ref(x_29);
 x_31 = lean_box(0);
}
x_65 = lean_mk_string_unchecked("PrettyPrinter", 13, 13);
x_66 = lean_mk_string_unchecked("parenthesize", 12, 12);
x_67 = l_Lean_Name_mkStr2(x_65, x_66);
lean_inc(x_67);
x_630 = l_Lean_isTracingEnabledFor___at___Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_spec__2___redArg(x_67, x_8, x_30);
x_631 = lean_ctor_get(x_630, 0);
lean_inc(x_631);
x_632 = lean_unbox(x_631);
lean_dec(x_631);
if (x_632 == 0)
{
lean_object* x_633; 
x_633 = lean_ctor_get(x_630, 1);
lean_inc(x_633);
lean_dec(x_630);
x_338 = x_6;
x_339 = x_7;
x_340 = x_8;
x_341 = x_9;
x_342 = x_633;
goto block_629;
}
else
{
lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; 
x_634 = lean_ctor_get(x_630, 1);
lean_inc(x_634);
if (lean_is_exclusive(x_630)) {
 lean_ctor_release(x_630, 0);
 lean_ctor_release(x_630, 1);
 x_635 = x_630;
} else {
 lean_dec_ref(x_630);
 x_635 = lean_box(0);
}
x_636 = lean_mk_string_unchecked("parenthesizing (cont := ", 24, 24);
x_637 = l_Lean_stringToMessageData(x_636);
lean_dec(x_636);
x_638 = lean_ctor_get(x_20, 1);
lean_inc(x_638);
x_639 = lean_ctor_get(x_20, 2);
lean_inc(x_639);
if (lean_obj_tag(x_638) == 0)
{
lean_object* x_666; lean_object* x_667; lean_object* x_668; 
x_666 = lean_mk_string_unchecked("none", 4, 4);
x_667 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_667, 0, x_666);
x_668 = l_Lean_MessageData_ofFormat(x_667);
x_640 = x_668;
goto block_665;
}
else
{
uint8_t x_669; 
x_669 = !lean_is_exclusive(x_638);
if (x_669 == 0)
{
lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; 
x_670 = lean_ctor_get(x_638, 0);
x_671 = lean_mk_string_unchecked("some (", 6, 6);
lean_ctor_set_tag(x_638, 3);
lean_ctor_set(x_638, 0, x_671);
x_672 = l_Lean_MessageData_ofFormat(x_638);
x_673 = l___private_Init_Data_Repr_0__Nat_reprFast(x_670);
x_674 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_674, 0, x_673);
x_675 = l_Lean_MessageData_ofFormat(x_674);
x_676 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_676, 0, x_672);
lean_ctor_set(x_676, 1, x_675);
x_677 = lean_mk_string_unchecked(")", 1, 1);
x_678 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_678, 0, x_677);
x_679 = l_Lean_MessageData_ofFormat(x_678);
x_680 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_680, 0, x_676);
lean_ctor_set(x_680, 1, x_679);
x_640 = x_680;
goto block_665;
}
else
{
lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; 
x_681 = lean_ctor_get(x_638, 0);
lean_inc(x_681);
lean_dec(x_638);
x_682 = lean_mk_string_unchecked("some (", 6, 6);
x_683 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_683, 0, x_682);
x_684 = l_Lean_MessageData_ofFormat(x_683);
x_685 = l___private_Init_Data_Repr_0__Nat_reprFast(x_681);
x_686 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_686, 0, x_685);
x_687 = l_Lean_MessageData_ofFormat(x_686);
x_688 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_688, 0, x_684);
lean_ctor_set(x_688, 1, x_687);
x_689 = lean_mk_string_unchecked(")", 1, 1);
x_690 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_690, 0, x_689);
x_691 = l_Lean_MessageData_ofFormat(x_690);
x_692 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_692, 0, x_688);
lean_ctor_set(x_692, 1, x_691);
x_640 = x_692;
goto block_665;
}
}
block_665:
{
lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; uint8_t x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; 
x_641 = lean_mk_string_unchecked(",", 1, 1);
x_642 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_642, 0, x_641);
x_643 = l_Lean_MessageData_ofFormat(x_642);
if (lean_is_scalar(x_635)) {
 x_644 = lean_alloc_ctor(7, 2, 0);
} else {
 x_644 = x_635;
 lean_ctor_set_tag(x_644, 7);
}
lean_ctor_set(x_644, 0, x_640);
lean_ctor_set(x_644, 1, x_643);
x_645 = lean_box(1);
x_646 = l_Lean_MessageData_ofFormat(x_645);
x_647 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_647, 0, x_644);
lean_ctor_set(x_647, 1, x_646);
x_648 = l_Lean_MessageData_ofName(x_639);
x_649 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_649, 0, x_647);
lean_ctor_set(x_649, 1, x_648);
x_650 = l_Lean_MessageData_paren(x_649);
x_651 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_651, 0, x_637);
lean_ctor_set(x_651, 1, x_650);
x_652 = lean_mk_string_unchecked(")", 1, 1);
x_653 = l_Lean_stringToMessageData(x_652);
lean_dec(x_652);
x_654 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_654, 0, x_651);
lean_ctor_set(x_654, 1, x_653);
x_655 = lean_unbox(x_26);
lean_inc(x_12);
x_656 = l_Lean_Syntax_formatStx(x_12, x_24, x_655);
x_657 = l_Lean_MessageData_ofFormat(x_656);
x_658 = l_Lean_indentD(x_657);
x_659 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_659, 0, x_654);
lean_ctor_set(x_659, 1, x_658);
x_660 = lean_mk_string_unchecked("", 0, 0);
x_661 = l_Lean_stringToMessageData(x_660);
lean_dec(x_660);
x_662 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_662, 0, x_659);
lean_ctor_set(x_662, 1, x_661);
lean_inc(x_67);
x_663 = l_Lean_addTrace___at___Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_spec__3___redArg(x_67, x_662, x_8, x_9, x_634);
x_664 = lean_ctor_get(x_663, 1);
lean_inc(x_664);
lean_dec(x_663);
x_338 = x_6;
x_339 = x_7;
x_340 = x_8;
x_341 = x_9;
x_342 = x_664;
goto block_629;
}
}
block_56:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_38 = l_Lean_Syntax_MonadTraverser_setCur___at___Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_spec__1___redArg(x_32, x_34, x_37);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
x_40 = l_Lean_Syntax_MonadTraverser_goLeft___at___Lean_PrettyPrinter_Parenthesizer_visitArgs_spec__1___redArg(x_34, x_39);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_42 = lean_st_ref_take(x_34, x_41);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_ctor_get(x_43, 0);
lean_inc(x_45);
x_46 = lean_unsigned_to_nat(1024u);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_48 = lean_ctor_get(x_43, 3);
lean_inc(x_48);
x_49 = lean_ctor_get(x_43, 5);
lean_inc(x_49);
x_50 = lean_ctor_get_uint8(x_43, sizeof(void*)*6);
lean_dec(x_43);
lean_inc(x_1);
x_51 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_51, 0, x_45);
lean_ctor_set(x_51, 1, x_47);
lean_ctor_set(x_51, 2, x_1);
lean_ctor_set(x_51, 3, x_48);
lean_ctor_set(x_51, 4, x_24);
lean_ctor_set(x_51, 5, x_49);
lean_ctor_set_uint8(x_51, sizeof(void*)*6, x_50);
x_52 = lean_st_ref_set(x_34, x_51, x_44);
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_dec(x_52);
x_54 = lean_box(0);
x_55 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lam__0(x_20, x_1, x_4, x_54, x_33, x_34, x_35, x_36, x_53);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_20);
return x_55;
}
block_64:
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_box(0);
x_63 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lam__0(x_20, x_1, x_4, x_62, x_58, x_59, x_60, x_61, x_57);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_20);
return x_63;
}
block_103:
{
lean_object* x_74; lean_object* x_75; uint8_t x_76; 
lean_inc(x_67);
x_74 = l_Lean_isTracingEnabledFor___at___Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_spec__2___redArg(x_67, x_71, x_73);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_unbox(x_75);
lean_dec(x_75);
if (x_76 == 0)
{
lean_object* x_77; 
lean_dec(x_67);
lean_dec(x_31);
x_77 = lean_ctor_get(x_74, 1);
lean_inc(x_77);
lean_dec(x_74);
x_32 = x_68;
x_33 = x_69;
x_34 = x_70;
x_35 = x_71;
x_36 = x_72;
x_37 = x_77;
goto block_56;
}
else
{
uint8_t x_78; 
x_78 = !lean_is_exclusive(x_74);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_79 = lean_ctor_get(x_74, 1);
x_80 = lean_ctor_get(x_74, 0);
lean_dec(x_80);
x_81 = lean_mk_string_unchecked("parenthesized: ", 15, 15);
x_82 = l_Lean_stringToMessageData(x_81);
lean_dec(x_81);
x_83 = lean_unbox(x_26);
lean_inc(x_68);
x_84 = l_Lean_Syntax_formatStx(x_68, x_24, x_83);
x_85 = l_Lean_MessageData_ofFormat(x_84);
lean_ctor_set_tag(x_74, 7);
lean_ctor_set(x_74, 1, x_85);
lean_ctor_set(x_74, 0, x_82);
x_86 = lean_mk_string_unchecked("", 0, 0);
x_87 = l_Lean_stringToMessageData(x_86);
lean_dec(x_86);
if (lean_is_scalar(x_31)) {
 x_88 = lean_alloc_ctor(7, 2, 0);
} else {
 x_88 = x_31;
 lean_ctor_set_tag(x_88, 7);
}
lean_ctor_set(x_88, 0, x_74);
lean_ctor_set(x_88, 1, x_87);
x_89 = l_Lean_addTrace___at___Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_spec__3___redArg(x_67, x_88, x_71, x_72, x_79);
x_90 = lean_ctor_get(x_89, 1);
lean_inc(x_90);
lean_dec(x_89);
x_32 = x_68;
x_33 = x_69;
x_34 = x_70;
x_35 = x_71;
x_36 = x_72;
x_37 = x_90;
goto block_56;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_91 = lean_ctor_get(x_74, 1);
lean_inc(x_91);
lean_dec(x_74);
x_92 = lean_mk_string_unchecked("parenthesized: ", 15, 15);
x_93 = l_Lean_stringToMessageData(x_92);
lean_dec(x_92);
x_94 = lean_unbox(x_26);
lean_inc(x_68);
x_95 = l_Lean_Syntax_formatStx(x_68, x_24, x_94);
x_96 = l_Lean_MessageData_ofFormat(x_95);
x_97 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_97, 0, x_93);
lean_ctor_set(x_97, 1, x_96);
x_98 = lean_mk_string_unchecked("", 0, 0);
x_99 = l_Lean_stringToMessageData(x_98);
lean_dec(x_98);
if (lean_is_scalar(x_31)) {
 x_100 = lean_alloc_ctor(7, 2, 0);
} else {
 x_100 = x_31;
 lean_ctor_set_tag(x_100, 7);
}
lean_ctor_set(x_100, 0, x_97);
lean_ctor_set(x_100, 1, x_99);
x_101 = l_Lean_addTrace___at___Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_spec__3___redArg(x_67, x_100, x_71, x_72, x_91);
x_102 = lean_ctor_get(x_101, 1);
lean_inc(x_102);
lean_dec(x_101);
x_32 = x_68;
x_33 = x_69;
x_34 = x_70;
x_35 = x_71;
x_36 = x_72;
x_37 = x_102;
goto block_56;
}
}
}
block_128:
{
lean_object* x_111; 
x_111 = l_Lean_Syntax_getTailInfo(x_104);
lean_dec(x_104);
if (lean_obj_tag(x_111) == 0)
{
uint8_t x_112; 
x_112 = !lean_is_exclusive(x_111);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_113 = lean_ctor_get(x_111, 0);
lean_dec(x_113);
x_114 = lean_mk_string_unchecked("", 0, 0);
x_115 = lean_unsigned_to_nat(0u);
x_116 = lean_string_utf8_byte_size(x_114);
x_117 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_117, 0, x_114);
lean_ctor_set(x_117, 1, x_115);
lean_ctor_set(x_117, 2, x_116);
lean_ctor_set(x_111, 0, x_117);
x_118 = l_Lean_Syntax_setTailInfo(x_105, x_111);
x_68 = x_118;
x_69 = x_106;
x_70 = x_107;
x_71 = x_108;
x_72 = x_109;
x_73 = x_110;
goto block_103;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_119 = lean_ctor_get(x_111, 1);
x_120 = lean_ctor_get(x_111, 2);
x_121 = lean_ctor_get(x_111, 3);
lean_inc(x_121);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_111);
x_122 = lean_mk_string_unchecked("", 0, 0);
x_123 = lean_unsigned_to_nat(0u);
x_124 = lean_string_utf8_byte_size(x_122);
x_125 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_125, 0, x_122);
lean_ctor_set(x_125, 1, x_123);
lean_ctor_set(x_125, 2, x_124);
x_126 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_119);
lean_ctor_set(x_126, 2, x_120);
lean_ctor_set(x_126, 3, x_121);
x_127 = l_Lean_Syntax_setTailInfo(x_105, x_126);
x_68 = x_127;
x_69 = x_106;
x_70 = x_107;
x_71 = x_108;
x_72 = x_109;
x_73 = x_110;
goto block_103;
}
}
else
{
lean_dec(x_111);
x_68 = x_105;
x_69 = x_106;
x_70 = x_107;
x_71 = x_108;
x_72 = x_109;
x_73 = x_110;
goto block_103;
}
}
block_153:
{
lean_object* x_135; lean_object* x_136; 
lean_inc(x_129);
x_135 = lean_apply_1(x_3, x_129);
x_136 = l_Lean_Syntax_getHeadInfo(x_129);
if (lean_obj_tag(x_136) == 0)
{
uint8_t x_137; 
x_137 = !lean_is_exclusive(x_136);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_138 = lean_ctor_get(x_136, 2);
lean_dec(x_138);
x_139 = lean_mk_string_unchecked("", 0, 0);
x_140 = lean_unsigned_to_nat(0u);
x_141 = lean_string_utf8_byte_size(x_139);
x_142 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_142, 0, x_139);
lean_ctor_set(x_142, 1, x_140);
lean_ctor_set(x_142, 2, x_141);
lean_ctor_set(x_136, 2, x_142);
x_143 = l_Lean_Syntax_setHeadInfo(x_135, x_136);
x_104 = x_129;
x_105 = x_143;
x_106 = x_130;
x_107 = x_131;
x_108 = x_132;
x_109 = x_133;
x_110 = x_134;
goto block_128;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_144 = lean_ctor_get(x_136, 0);
x_145 = lean_ctor_get(x_136, 1);
x_146 = lean_ctor_get(x_136, 3);
lean_inc(x_146);
lean_inc(x_145);
lean_inc(x_144);
lean_dec(x_136);
x_147 = lean_mk_string_unchecked("", 0, 0);
x_148 = lean_unsigned_to_nat(0u);
x_149 = lean_string_utf8_byte_size(x_147);
x_150 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_150, 0, x_147);
lean_ctor_set(x_150, 1, x_148);
lean_ctor_set(x_150, 2, x_149);
x_151 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_151, 0, x_144);
lean_ctor_set(x_151, 1, x_145);
lean_ctor_set(x_151, 2, x_150);
lean_ctor_set(x_151, 3, x_146);
x_152 = l_Lean_Syntax_setHeadInfo(x_135, x_151);
x_104 = x_129;
x_105 = x_152;
x_106 = x_130;
x_107 = x_131;
x_108 = x_132;
x_109 = x_133;
x_110 = x_134;
goto block_128;
}
}
else
{
lean_dec(x_136);
x_104 = x_129;
x_105 = x_135;
x_106 = x_130;
x_107 = x_131;
x_108 = x_132;
x_109 = x_133;
x_110 = x_134;
goto block_128;
}
}
block_177:
{
lean_object* x_160; 
x_160 = l_Lean_Syntax_getTailInfo(x_154);
if (lean_obj_tag(x_160) == 0)
{
uint8_t x_161; 
x_161 = !lean_is_exclusive(x_160);
if (x_161 == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_162 = lean_ctor_get(x_160, 2);
lean_dec(x_162);
x_163 = lean_mk_string_unchecked("", 0, 0);
x_164 = lean_unsigned_to_nat(0u);
x_165 = lean_string_utf8_byte_size(x_163);
x_166 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_166, 0, x_163);
lean_ctor_set(x_166, 1, x_164);
lean_ctor_set(x_166, 2, x_165);
lean_ctor_set(x_160, 2, x_166);
x_167 = l_Lean_Syntax_setTailInfo(x_154, x_160);
x_129 = x_167;
x_130 = x_155;
x_131 = x_156;
x_132 = x_157;
x_133 = x_158;
x_134 = x_159;
goto block_153;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_168 = lean_ctor_get(x_160, 0);
x_169 = lean_ctor_get(x_160, 1);
x_170 = lean_ctor_get(x_160, 3);
lean_inc(x_170);
lean_inc(x_169);
lean_inc(x_168);
lean_dec(x_160);
x_171 = lean_mk_string_unchecked("", 0, 0);
x_172 = lean_unsigned_to_nat(0u);
x_173 = lean_string_utf8_byte_size(x_171);
x_174 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_174, 0, x_171);
lean_ctor_set(x_174, 1, x_172);
lean_ctor_set(x_174, 2, x_173);
x_175 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_175, 0, x_168);
lean_ctor_set(x_175, 1, x_169);
lean_ctor_set(x_175, 2, x_174);
lean_ctor_set(x_175, 3, x_170);
x_176 = l_Lean_Syntax_setTailInfo(x_154, x_175);
x_129 = x_176;
x_130 = x_155;
x_131 = x_156;
x_132 = x_157;
x_133 = x_158;
x_134 = x_159;
goto block_153;
}
}
else
{
lean_dec(x_160);
x_129 = x_154;
x_130 = x_155;
x_131 = x_156;
x_132 = x_157;
x_133 = x_158;
x_134 = x_159;
goto block_153;
}
}
block_203:
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_183 = l_Lean_Syntax_MonadTraverser_getCur___at___Lean_PrettyPrinter_Parenthesizer_visitArgs_spec__2___redArg(x_179, x_182);
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_183, 1);
lean_inc(x_185);
lean_dec(x_183);
x_186 = l_Lean_Syntax_getHeadInfo(x_184);
if (lean_obj_tag(x_186) == 0)
{
uint8_t x_187; 
x_187 = !lean_is_exclusive(x_186);
if (x_187 == 0)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_188 = lean_ctor_get(x_186, 0);
lean_dec(x_188);
x_189 = lean_mk_string_unchecked("", 0, 0);
x_190 = lean_unsigned_to_nat(0u);
x_191 = lean_string_utf8_byte_size(x_189);
x_192 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_192, 0, x_189);
lean_ctor_set(x_192, 1, x_190);
lean_ctor_set(x_192, 2, x_191);
lean_ctor_set(x_186, 0, x_192);
x_193 = l_Lean_Syntax_setHeadInfo(x_184, x_186);
x_154 = x_193;
x_155 = x_178;
x_156 = x_179;
x_157 = x_180;
x_158 = x_181;
x_159 = x_185;
goto block_177;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_194 = lean_ctor_get(x_186, 1);
x_195 = lean_ctor_get(x_186, 2);
x_196 = lean_ctor_get(x_186, 3);
lean_inc(x_196);
lean_inc(x_195);
lean_inc(x_194);
lean_dec(x_186);
x_197 = lean_mk_string_unchecked("", 0, 0);
x_198 = lean_unsigned_to_nat(0u);
x_199 = lean_string_utf8_byte_size(x_197);
x_200 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_200, 0, x_197);
lean_ctor_set(x_200, 1, x_198);
lean_ctor_set(x_200, 2, x_199);
x_201 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_194);
lean_ctor_set(x_201, 2, x_195);
lean_ctor_set(x_201, 3, x_196);
x_202 = l_Lean_Syntax_setHeadInfo(x_184, x_201);
x_154 = x_202;
x_155 = x_178;
x_156 = x_179;
x_157 = x_180;
x_158 = x_181;
x_159 = x_185;
goto block_177;
}
}
else
{
lean_dec(x_186);
x_154 = x_184;
x_155 = x_178;
x_156 = x_179;
x_157 = x_180;
x_158 = x_181;
x_159 = x_185;
goto block_177;
}
}
block_213:
{
lean_object* x_209; uint8_t x_210; 
x_209 = lean_unsigned_to_nat(0u);
x_210 = lean_nat_dec_lt(x_209, x_16);
lean_dec(x_16);
if (x_210 == 0)
{
x_178 = x_205;
x_179 = x_206;
x_180 = x_207;
x_181 = x_208;
x_182 = x_204;
goto block_203;
}
else
{
lean_object* x_211; lean_object* x_212; 
x_211 = l_Lean_Syntax_MonadTraverser_goRight___at___Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_spec__4___redArg(x_206, x_204);
x_212 = lean_ctor_get(x_211, 1);
lean_inc(x_212);
lean_dec(x_211);
x_178 = x_205;
x_179 = x_206;
x_180 = x_207;
x_181 = x_208;
x_182 = x_212;
goto block_203;
}
}
block_229:
{
uint8_t x_222; 
x_222 = lean_nat_dec_lt(x_221, x_4);
lean_dec(x_221);
if (x_222 == 0)
{
if (x_2 == 0)
{
lean_dec(x_217);
lean_dec(x_216);
lean_dec(x_67);
lean_dec(x_31);
lean_dec(x_16);
lean_dec(x_3);
x_57 = x_215;
x_58 = x_214;
x_59 = x_218;
x_60 = x_219;
x_61 = x_220;
goto block_64;
}
else
{
if (lean_obj_tag(x_217) == 0)
{
lean_dec(x_216);
lean_dec(x_67);
lean_dec(x_31);
lean_dec(x_16);
lean_dec(x_3);
x_57 = x_215;
x_58 = x_214;
x_59 = x_218;
x_60 = x_219;
x_61 = x_220;
goto block_64;
}
else
{
lean_object* x_223; 
x_223 = lean_ctor_get(x_20, 1);
lean_inc(x_223);
if (lean_obj_tag(x_223) == 0)
{
lean_dec(x_217);
lean_dec(x_216);
lean_dec(x_67);
lean_dec(x_31);
lean_dec(x_16);
lean_dec(x_3);
x_57 = x_215;
x_58 = x_214;
x_59 = x_218;
x_60 = x_219;
x_61 = x_220;
goto block_64;
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; uint8_t x_227; 
x_224 = lean_ctor_get(x_217, 0);
lean_inc(x_224);
lean_dec(x_217);
x_225 = lean_ctor_get(x_223, 0);
lean_inc(x_225);
lean_dec(x_223);
x_226 = lean_ctor_get(x_20, 2);
lean_inc(x_226);
x_227 = lean_name_eq(x_216, x_226);
lean_dec(x_226);
lean_dec(x_216);
if (x_227 == 0)
{
lean_dec(x_225);
lean_dec(x_224);
lean_dec(x_67);
lean_dec(x_31);
lean_dec(x_16);
lean_dec(x_3);
x_57 = x_215;
x_58 = x_214;
x_59 = x_218;
x_60 = x_219;
x_61 = x_220;
goto block_64;
}
else
{
uint8_t x_228; 
x_228 = lean_nat_dec_le(x_224, x_225);
lean_dec(x_225);
lean_dec(x_224);
if (x_228 == 0)
{
lean_dec(x_67);
lean_dec(x_31);
lean_dec(x_16);
lean_dec(x_3);
x_57 = x_215;
x_58 = x_214;
x_59 = x_218;
x_60 = x_219;
x_61 = x_220;
goto block_64;
}
else
{
x_204 = x_215;
x_205 = x_214;
x_206 = x_218;
x_207 = x_219;
x_208 = x_220;
goto block_213;
}
}
}
}
}
}
else
{
lean_dec(x_217);
lean_dec(x_216);
x_204 = x_215;
x_205 = x_214;
x_206 = x_218;
x_207 = x_219;
x_208 = x_220;
goto block_213;
}
}
block_243:
{
uint8_t x_238; 
x_238 = lean_ctor_get_uint8(x_233, sizeof(void*)*1);
if (x_238 == 0)
{
lean_dec(x_23);
x_214 = x_233;
x_215 = x_237;
x_216 = x_231;
x_217 = x_230;
x_218 = x_234;
x_219 = x_235;
x_220 = x_236;
x_221 = x_232;
goto block_229;
}
else
{
lean_object* x_239; uint8_t x_240; 
x_239 = lean_ctor_get(x_23, 1);
lean_inc(x_239);
lean_dec(x_23);
x_240 = l_Array_isEmpty___redArg(x_239);
lean_dec(x_239);
if (x_240 == 0)
{
if (x_238 == 0)
{
x_214 = x_233;
x_215 = x_237;
x_216 = x_231;
x_217 = x_230;
x_218 = x_234;
x_219 = x_235;
x_220 = x_236;
x_221 = x_232;
goto block_229;
}
else
{
lean_object* x_241; uint8_t x_242; 
x_241 = lean_unsigned_to_nat(1024u);
x_242 = lean_nat_dec_lt(x_232, x_241);
if (x_242 == 0)
{
x_214 = x_233;
x_215 = x_237;
x_216 = x_231;
x_217 = x_230;
x_218 = x_234;
x_219 = x_235;
x_220 = x_236;
x_221 = x_232;
goto block_229;
}
else
{
lean_dec(x_232);
lean_dec(x_231);
lean_dec(x_230);
x_204 = x_237;
x_205 = x_233;
x_206 = x_234;
x_207 = x_235;
x_208 = x_236;
goto block_213;
}
}
}
else
{
x_214 = x_233;
x_215 = x_237;
x_216 = x_231;
x_217 = x_230;
x_218 = x_234;
x_219 = x_235;
x_220 = x_236;
x_221 = x_232;
goto block_229;
}
}
}
block_257:
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; 
if (lean_is_scalar(x_22)) {
 x_254 = lean_alloc_ctor(7, 2, 0);
} else {
 x_254 = x_22;
 lean_ctor_set_tag(x_254, 7);
}
lean_ctor_set(x_254, 0, x_252);
lean_ctor_set(x_254, 1, x_253);
lean_inc(x_67);
x_255 = l_Lean_addTrace___at___Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_spec__3___redArg(x_67, x_254, x_245, x_244, x_251);
x_256 = lean_ctor_get(x_255, 1);
lean_inc(x_256);
lean_dec(x_255);
x_230 = x_247;
x_231 = x_246;
x_232 = x_250;
x_233 = x_249;
x_234 = x_248;
x_235 = x_245;
x_236 = x_244;
x_237 = x_256;
goto block_243;
}
block_280:
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; 
if (lean_is_scalar(x_18)) {
 x_273 = lean_alloc_ctor(7, 2, 0);
} else {
 x_273 = x_18;
 lean_ctor_set_tag(x_273, 7);
}
lean_ctor_set(x_273, 0, x_272);
lean_ctor_set(x_273, 1, x_268);
if (lean_is_scalar(x_14)) {
 x_274 = lean_alloc_ctor(7, 2, 0);
} else {
 x_274 = x_14;
 lean_ctor_set_tag(x_274, 7);
}
lean_ctor_set(x_274, 0, x_273);
lean_ctor_set(x_274, 1, x_260);
x_275 = l_Lean_MessageData_ofName(x_271);
x_276 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_276, 0, x_274);
lean_ctor_set(x_276, 1, x_275);
x_277 = l_Lean_MessageData_paren(x_276);
x_278 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_278, 0, x_266);
lean_ctor_set(x_278, 1, x_277);
x_279 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_279, 0, x_278);
lean_ctor_set(x_279, 1, x_269);
x_244 = x_258;
x_245 = x_259;
x_246 = x_261;
x_247 = x_267;
x_248 = x_262;
x_249 = x_263;
x_250 = x_270;
x_251 = x_264;
x_252 = x_265;
x_253 = x_279;
goto block_257;
}
block_337:
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; 
x_293 = lean_mk_string_unchecked(",", 1, 1);
x_294 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_294, 0, x_293);
x_295 = l_Lean_MessageData_ofFormat(x_294);
lean_inc(x_295);
x_296 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_296, 0, x_292);
lean_ctor_set(x_296, 1, x_295);
x_297 = lean_box(1);
x_298 = l_Lean_MessageData_ofFormat(x_297);
lean_inc(x_298);
x_299 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_299, 0, x_296);
lean_ctor_set(x_299, 1, x_298);
lean_inc(x_284);
x_300 = l_Lean_MessageData_ofName(x_284);
x_301 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_301, 0, x_299);
lean_ctor_set(x_301, 1, x_300);
x_302 = l_Lean_MessageData_paren(x_301);
x_303 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_303, 0, x_288);
lean_ctor_set(x_303, 1, x_302);
x_304 = lean_mk_string_unchecked(" <=\? ", 5, 5);
x_305 = l_Lean_stringToMessageData(x_304);
lean_dec(x_304);
x_306 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_306, 0, x_303);
lean_ctor_set(x_306, 1, x_305);
x_307 = lean_ctor_get(x_20, 1);
lean_inc(x_307);
if (lean_obj_tag(x_307) == 0)
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; 
x_308 = lean_ctor_get(x_20, 2);
lean_inc(x_308);
x_309 = lean_mk_string_unchecked("none", 4, 4);
x_310 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_310, 0, x_309);
x_311 = l_Lean_MessageData_ofFormat(x_310);
x_258 = x_281;
x_259 = x_282;
x_260 = x_298;
x_261 = x_284;
x_262 = x_287;
x_263 = x_286;
x_264 = x_290;
x_265 = x_291;
x_266 = x_306;
x_267 = x_283;
x_268 = x_295;
x_269 = x_285;
x_270 = x_289;
x_271 = x_308;
x_272 = x_311;
goto block_280;
}
else
{
lean_object* x_312; uint8_t x_313; 
x_312 = lean_ctor_get(x_20, 2);
lean_inc(x_312);
x_313 = !lean_is_exclusive(x_307);
if (x_313 == 0)
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; 
x_314 = lean_ctor_get(x_307, 0);
x_315 = lean_mk_string_unchecked("some (", 6, 6);
lean_ctor_set_tag(x_307, 3);
lean_ctor_set(x_307, 0, x_315);
x_316 = l_Lean_MessageData_ofFormat(x_307);
x_317 = l___private_Init_Data_Repr_0__Nat_reprFast(x_314);
x_318 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_318, 0, x_317);
x_319 = l_Lean_MessageData_ofFormat(x_318);
x_320 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_320, 0, x_316);
lean_ctor_set(x_320, 1, x_319);
x_321 = lean_mk_string_unchecked(")", 1, 1);
x_322 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_322, 0, x_321);
x_323 = l_Lean_MessageData_ofFormat(x_322);
x_324 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_324, 0, x_320);
lean_ctor_set(x_324, 1, x_323);
x_258 = x_281;
x_259 = x_282;
x_260 = x_298;
x_261 = x_284;
x_262 = x_287;
x_263 = x_286;
x_264 = x_290;
x_265 = x_291;
x_266 = x_306;
x_267 = x_283;
x_268 = x_295;
x_269 = x_285;
x_270 = x_289;
x_271 = x_312;
x_272 = x_324;
goto block_280;
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; 
x_325 = lean_ctor_get(x_307, 0);
lean_inc(x_325);
lean_dec(x_307);
x_326 = lean_mk_string_unchecked("some (", 6, 6);
x_327 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_327, 0, x_326);
x_328 = l_Lean_MessageData_ofFormat(x_327);
x_329 = l___private_Init_Data_Repr_0__Nat_reprFast(x_325);
x_330 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_330, 0, x_329);
x_331 = l_Lean_MessageData_ofFormat(x_330);
x_332 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_332, 0, x_328);
lean_ctor_set(x_332, 1, x_331);
x_333 = lean_mk_string_unchecked(")", 1, 1);
x_334 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_334, 0, x_333);
x_335 = l_Lean_MessageData_ofFormat(x_334);
x_336 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_336, 0, x_332);
lean_ctor_set(x_336, 1, x_335);
x_258 = x_281;
x_259 = x_282;
x_260 = x_298;
x_261 = x_284;
x_262 = x_287;
x_263 = x_286;
x_264 = x_290;
x_265 = x_291;
x_266 = x_306;
x_267 = x_283;
x_268 = x_295;
x_269 = x_285;
x_270 = x_289;
x_271 = x_312;
x_272 = x_336;
goto block_280;
}
}
}
block_629:
{
lean_object* x_343; 
lean_inc(x_341);
lean_inc(x_340);
lean_inc(x_339);
lean_inc(x_338);
x_343 = lean_apply_5(x_5, x_338, x_339, x_340, x_341, x_342);
if (lean_obj_tag(x_343) == 0)
{
uint8_t x_344; 
x_344 = !lean_is_exclusive(x_343);
if (x_344 == 0)
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; 
x_345 = lean_ctor_get(x_343, 1);
x_346 = lean_ctor_get(x_343, 0);
lean_dec(x_346);
x_347 = lean_st_ref_get(x_339, x_345);
x_348 = lean_ctor_get(x_347, 0);
lean_inc(x_348);
x_349 = lean_ctor_get(x_348, 3);
lean_inc(x_349);
if (lean_obj_tag(x_349) == 0)
{
uint8_t x_350; 
lean_dec(x_348);
lean_dec(x_339);
lean_dec(x_338);
lean_dec(x_31);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_350 = !lean_is_exclusive(x_347);
if (x_350 == 0)
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; uint8_t x_355; 
x_351 = lean_ctor_get(x_347, 1);
x_352 = lean_ctor_get(x_347, 0);
lean_dec(x_352);
lean_inc(x_67);
x_353 = l_Lean_isTracingEnabledFor___at___Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_spec__2___redArg(x_67, x_340, x_351);
x_354 = lean_ctor_get(x_353, 0);
lean_inc(x_354);
x_355 = lean_unbox(x_354);
lean_dec(x_354);
if (x_355 == 0)
{
uint8_t x_356; 
lean_free_object(x_347);
lean_free_object(x_343);
lean_dec(x_341);
lean_dec(x_340);
lean_dec(x_67);
lean_dec(x_12);
x_356 = !lean_is_exclusive(x_353);
if (x_356 == 0)
{
lean_object* x_357; lean_object* x_358; 
x_357 = lean_ctor_get(x_353, 0);
lean_dec(x_357);
x_358 = lean_box(0);
lean_ctor_set(x_353, 0, x_358);
return x_353;
}
else
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; 
x_359 = lean_ctor_get(x_353, 1);
lean_inc(x_359);
lean_dec(x_353);
x_360 = lean_box(0);
x_361 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_361, 0, x_360);
lean_ctor_set(x_361, 1, x_359);
return x_361;
}
}
else
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; uint8_t x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; 
x_362 = lean_ctor_get(x_353, 1);
lean_inc(x_362);
lean_dec(x_353);
x_363 = lean_mk_string_unchecked("visited a syntax tree without precedences\?!", 43, 43);
x_364 = l_Lean_stringToMessageData(x_363);
lean_dec(x_363);
x_365 = lean_box(1);
x_366 = lean_unbox(x_26);
x_367 = l_Lean_Syntax_formatStx(x_12, x_349, x_366);
lean_ctor_set_tag(x_347, 5);
lean_ctor_set(x_347, 1, x_367);
lean_ctor_set(x_347, 0, x_365);
x_368 = l_Lean_MessageData_ofFormat(x_347);
lean_ctor_set_tag(x_343, 7);
lean_ctor_set(x_343, 1, x_368);
lean_ctor_set(x_343, 0, x_364);
x_369 = lean_mk_string_unchecked("", 0, 0);
x_370 = l_Lean_stringToMessageData(x_369);
lean_dec(x_369);
x_371 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_371, 0, x_343);
lean_ctor_set(x_371, 1, x_370);
x_372 = l_Lean_addTrace___at___Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_spec__3___redArg(x_67, x_371, x_340, x_341, x_362);
lean_dec(x_341);
lean_dec(x_340);
return x_372;
}
}
else
{
lean_object* x_373; lean_object* x_374; lean_object* x_375; uint8_t x_376; 
x_373 = lean_ctor_get(x_347, 1);
lean_inc(x_373);
lean_dec(x_347);
lean_inc(x_67);
x_374 = l_Lean_isTracingEnabledFor___at___Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_spec__2___redArg(x_67, x_340, x_373);
x_375 = lean_ctor_get(x_374, 0);
lean_inc(x_375);
x_376 = lean_unbox(x_375);
lean_dec(x_375);
if (x_376 == 0)
{
lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; 
lean_free_object(x_343);
lean_dec(x_341);
lean_dec(x_340);
lean_dec(x_67);
lean_dec(x_12);
x_377 = lean_ctor_get(x_374, 1);
lean_inc(x_377);
if (lean_is_exclusive(x_374)) {
 lean_ctor_release(x_374, 0);
 lean_ctor_release(x_374, 1);
 x_378 = x_374;
} else {
 lean_dec_ref(x_374);
 x_378 = lean_box(0);
}
x_379 = lean_box(0);
if (lean_is_scalar(x_378)) {
 x_380 = lean_alloc_ctor(0, 2, 0);
} else {
 x_380 = x_378;
}
lean_ctor_set(x_380, 0, x_379);
lean_ctor_set(x_380, 1, x_377);
return x_380;
}
else
{
lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; uint8_t x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; 
x_381 = lean_ctor_get(x_374, 1);
lean_inc(x_381);
lean_dec(x_374);
x_382 = lean_mk_string_unchecked("visited a syntax tree without precedences\?!", 43, 43);
x_383 = l_Lean_stringToMessageData(x_382);
lean_dec(x_382);
x_384 = lean_box(1);
x_385 = lean_unbox(x_26);
x_386 = l_Lean_Syntax_formatStx(x_12, x_349, x_385);
x_387 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_387, 0, x_384);
lean_ctor_set(x_387, 1, x_386);
x_388 = l_Lean_MessageData_ofFormat(x_387);
lean_ctor_set_tag(x_343, 7);
lean_ctor_set(x_343, 1, x_388);
lean_ctor_set(x_343, 0, x_383);
x_389 = lean_mk_string_unchecked("", 0, 0);
x_390 = l_Lean_stringToMessageData(x_389);
lean_dec(x_389);
x_391 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_391, 0, x_343);
lean_ctor_set(x_391, 1, x_390);
x_392 = l_Lean_addTrace___at___Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_spec__3___redArg(x_67, x_391, x_340, x_341, x_381);
lean_dec(x_341);
lean_dec(x_340);
return x_392;
}
}
}
else
{
uint8_t x_393; 
lean_dec(x_12);
x_393 = !lean_is_exclusive(x_347);
if (x_393 == 0)
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; uint8_t x_398; 
x_394 = lean_ctor_get(x_347, 1);
x_395 = lean_ctor_get(x_347, 0);
lean_dec(x_395);
x_396 = lean_ctor_get(x_348, 4);
lean_inc(x_396);
x_397 = lean_ctor_get(x_348, 5);
lean_inc(x_397);
lean_dec(x_348);
x_398 = !lean_is_exclusive(x_349);
if (x_398 == 0)
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; uint8_t x_402; 
x_399 = lean_ctor_get(x_349, 0);
lean_inc(x_67);
x_400 = l_Lean_isTracingEnabledFor___at___Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_spec__2___redArg(x_67, x_340, x_394);
x_401 = lean_ctor_get(x_400, 0);
lean_inc(x_401);
x_402 = lean_unbox(x_401);
lean_dec(x_401);
if (x_402 == 0)
{
lean_object* x_403; 
lean_free_object(x_349);
lean_free_object(x_347);
lean_free_object(x_343);
lean_dec(x_22);
lean_dec(x_18);
lean_dec(x_14);
x_403 = lean_ctor_get(x_400, 1);
lean_inc(x_403);
lean_dec(x_400);
x_230 = x_396;
x_231 = x_397;
x_232 = x_399;
x_233 = x_338;
x_234 = x_339;
x_235 = x_340;
x_236 = x_341;
x_237 = x_403;
goto block_243;
}
else
{
uint8_t x_404; 
x_404 = !lean_is_exclusive(x_400);
if (x_404 == 0)
{
lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; 
x_405 = lean_ctor_get(x_400, 1);
x_406 = lean_ctor_get(x_400, 0);
lean_dec(x_406);
x_407 = lean_mk_string_unchecked("...precedences are ", 19, 19);
x_408 = l_Lean_stringToMessageData(x_407);
lean_dec(x_407);
lean_inc(x_4);
x_409 = l___private_Init_Data_Repr_0__Nat_reprFast(x_4);
lean_ctor_set_tag(x_349, 3);
lean_ctor_set(x_349, 0, x_409);
x_410 = l_Lean_MessageData_ofFormat(x_349);
lean_ctor_set_tag(x_400, 7);
lean_ctor_set(x_400, 1, x_410);
lean_ctor_set(x_400, 0, x_408);
x_411 = lean_mk_string_unchecked(" >\? ", 4, 4);
x_412 = l_Lean_stringToMessageData(x_411);
lean_dec(x_411);
lean_ctor_set_tag(x_347, 7);
lean_ctor_set(x_347, 1, x_412);
lean_ctor_set(x_347, 0, x_400);
lean_inc(x_399);
x_413 = l___private_Init_Data_Repr_0__Nat_reprFast(x_399);
x_414 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_414, 0, x_413);
x_415 = l_Lean_MessageData_ofFormat(x_414);
lean_ctor_set_tag(x_343, 7);
lean_ctor_set(x_343, 1, x_415);
lean_ctor_set(x_343, 0, x_347);
x_416 = lean_mk_string_unchecked("", 0, 0);
x_417 = l_Lean_stringToMessageData(x_416);
lean_inc(x_417);
x_418 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_418, 0, x_343);
lean_ctor_set(x_418, 1, x_417);
if (x_2 == 0)
{
lean_object* x_419; lean_object* x_420; 
lean_dec(x_417);
lean_dec(x_18);
lean_dec(x_14);
x_419 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_419, 0, x_416);
x_420 = l_Lean_MessageData_ofFormat(x_419);
x_244 = x_341;
x_245 = x_340;
x_246 = x_397;
x_247 = x_396;
x_248 = x_339;
x_249 = x_338;
x_250 = x_399;
x_251 = x_405;
x_252 = x_418;
x_253 = x_420;
goto block_257;
}
else
{
lean_object* x_421; lean_object* x_422; 
lean_dec(x_416);
x_421 = lean_mk_string_unchecked(", ", 2, 2);
x_422 = l_Lean_stringToMessageData(x_421);
lean_dec(x_421);
if (lean_obj_tag(x_396) == 0)
{
lean_object* x_423; lean_object* x_424; lean_object* x_425; 
x_423 = lean_mk_string_unchecked("none", 4, 4);
x_424 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_424, 0, x_423);
x_425 = l_Lean_MessageData_ofFormat(x_424);
x_281 = x_341;
x_282 = x_340;
x_283 = x_396;
x_284 = x_397;
x_285 = x_417;
x_286 = x_338;
x_287 = x_339;
x_288 = x_422;
x_289 = x_399;
x_290 = x_405;
x_291 = x_418;
x_292 = x_425;
goto block_337;
}
else
{
lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; 
x_426 = lean_ctor_get(x_396, 0);
lean_inc(x_426);
x_427 = lean_mk_string_unchecked("some (", 6, 6);
x_428 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_428, 0, x_427);
x_429 = l_Lean_MessageData_ofFormat(x_428);
x_430 = l___private_Init_Data_Repr_0__Nat_reprFast(x_426);
x_431 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_431, 0, x_430);
x_432 = l_Lean_MessageData_ofFormat(x_431);
x_433 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_433, 0, x_429);
lean_ctor_set(x_433, 1, x_432);
x_434 = lean_mk_string_unchecked(")", 1, 1);
x_435 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_435, 0, x_434);
x_436 = l_Lean_MessageData_ofFormat(x_435);
x_437 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_437, 0, x_433);
lean_ctor_set(x_437, 1, x_436);
x_281 = x_341;
x_282 = x_340;
x_283 = x_396;
x_284 = x_397;
x_285 = x_417;
x_286 = x_338;
x_287 = x_339;
x_288 = x_422;
x_289 = x_399;
x_290 = x_405;
x_291 = x_418;
x_292 = x_437;
goto block_337;
}
}
}
else
{
lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; 
x_438 = lean_ctor_get(x_400, 1);
lean_inc(x_438);
lean_dec(x_400);
x_439 = lean_mk_string_unchecked("...precedences are ", 19, 19);
x_440 = l_Lean_stringToMessageData(x_439);
lean_dec(x_439);
lean_inc(x_4);
x_441 = l___private_Init_Data_Repr_0__Nat_reprFast(x_4);
lean_ctor_set_tag(x_349, 3);
lean_ctor_set(x_349, 0, x_441);
x_442 = l_Lean_MessageData_ofFormat(x_349);
x_443 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_443, 0, x_440);
lean_ctor_set(x_443, 1, x_442);
x_444 = lean_mk_string_unchecked(" >\? ", 4, 4);
x_445 = l_Lean_stringToMessageData(x_444);
lean_dec(x_444);
lean_ctor_set_tag(x_347, 7);
lean_ctor_set(x_347, 1, x_445);
lean_ctor_set(x_347, 0, x_443);
lean_inc(x_399);
x_446 = l___private_Init_Data_Repr_0__Nat_reprFast(x_399);
x_447 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_447, 0, x_446);
x_448 = l_Lean_MessageData_ofFormat(x_447);
lean_ctor_set_tag(x_343, 7);
lean_ctor_set(x_343, 1, x_448);
lean_ctor_set(x_343, 0, x_347);
x_449 = lean_mk_string_unchecked("", 0, 0);
x_450 = l_Lean_stringToMessageData(x_449);
lean_inc(x_450);
x_451 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_451, 0, x_343);
lean_ctor_set(x_451, 1, x_450);
if (x_2 == 0)
{
lean_object* x_452; lean_object* x_453; 
lean_dec(x_450);
lean_dec(x_18);
lean_dec(x_14);
x_452 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_452, 0, x_449);
x_453 = l_Lean_MessageData_ofFormat(x_452);
x_244 = x_341;
x_245 = x_340;
x_246 = x_397;
x_247 = x_396;
x_248 = x_339;
x_249 = x_338;
x_250 = x_399;
x_251 = x_438;
x_252 = x_451;
x_253 = x_453;
goto block_257;
}
else
{
lean_object* x_454; lean_object* x_455; 
lean_dec(x_449);
x_454 = lean_mk_string_unchecked(", ", 2, 2);
x_455 = l_Lean_stringToMessageData(x_454);
lean_dec(x_454);
if (lean_obj_tag(x_396) == 0)
{
lean_object* x_456; lean_object* x_457; lean_object* x_458; 
x_456 = lean_mk_string_unchecked("none", 4, 4);
x_457 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_457, 0, x_456);
x_458 = l_Lean_MessageData_ofFormat(x_457);
x_281 = x_341;
x_282 = x_340;
x_283 = x_396;
x_284 = x_397;
x_285 = x_450;
x_286 = x_338;
x_287 = x_339;
x_288 = x_455;
x_289 = x_399;
x_290 = x_438;
x_291 = x_451;
x_292 = x_458;
goto block_337;
}
else
{
lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; 
x_459 = lean_ctor_get(x_396, 0);
lean_inc(x_459);
x_460 = lean_mk_string_unchecked("some (", 6, 6);
x_461 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_461, 0, x_460);
x_462 = l_Lean_MessageData_ofFormat(x_461);
x_463 = l___private_Init_Data_Repr_0__Nat_reprFast(x_459);
x_464 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_464, 0, x_463);
x_465 = l_Lean_MessageData_ofFormat(x_464);
x_466 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_466, 0, x_462);
lean_ctor_set(x_466, 1, x_465);
x_467 = lean_mk_string_unchecked(")", 1, 1);
x_468 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_468, 0, x_467);
x_469 = l_Lean_MessageData_ofFormat(x_468);
x_470 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_470, 0, x_466);
lean_ctor_set(x_470, 1, x_469);
x_281 = x_341;
x_282 = x_340;
x_283 = x_396;
x_284 = x_397;
x_285 = x_450;
x_286 = x_338;
x_287 = x_339;
x_288 = x_455;
x_289 = x_399;
x_290 = x_438;
x_291 = x_451;
x_292 = x_470;
goto block_337;
}
}
}
}
}
else
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; uint8_t x_474; 
x_471 = lean_ctor_get(x_349, 0);
lean_inc(x_471);
lean_dec(x_349);
lean_inc(x_67);
x_472 = l_Lean_isTracingEnabledFor___at___Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_spec__2___redArg(x_67, x_340, x_394);
x_473 = lean_ctor_get(x_472, 0);
lean_inc(x_473);
x_474 = lean_unbox(x_473);
lean_dec(x_473);
if (x_474 == 0)
{
lean_object* x_475; 
lean_free_object(x_347);
lean_free_object(x_343);
lean_dec(x_22);
lean_dec(x_18);
lean_dec(x_14);
x_475 = lean_ctor_get(x_472, 1);
lean_inc(x_475);
lean_dec(x_472);
x_230 = x_396;
x_231 = x_397;
x_232 = x_471;
x_233 = x_338;
x_234 = x_339;
x_235 = x_340;
x_236 = x_341;
x_237 = x_475;
goto block_243;
}
else
{
lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; 
x_476 = lean_ctor_get(x_472, 1);
lean_inc(x_476);
if (lean_is_exclusive(x_472)) {
 lean_ctor_release(x_472, 0);
 lean_ctor_release(x_472, 1);
 x_477 = x_472;
} else {
 lean_dec_ref(x_472);
 x_477 = lean_box(0);
}
x_478 = lean_mk_string_unchecked("...precedences are ", 19, 19);
x_479 = l_Lean_stringToMessageData(x_478);
lean_dec(x_478);
lean_inc(x_4);
x_480 = l___private_Init_Data_Repr_0__Nat_reprFast(x_4);
x_481 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_481, 0, x_480);
x_482 = l_Lean_MessageData_ofFormat(x_481);
if (lean_is_scalar(x_477)) {
 x_483 = lean_alloc_ctor(7, 2, 0);
} else {
 x_483 = x_477;
 lean_ctor_set_tag(x_483, 7);
}
lean_ctor_set(x_483, 0, x_479);
lean_ctor_set(x_483, 1, x_482);
x_484 = lean_mk_string_unchecked(" >\? ", 4, 4);
x_485 = l_Lean_stringToMessageData(x_484);
lean_dec(x_484);
lean_ctor_set_tag(x_347, 7);
lean_ctor_set(x_347, 1, x_485);
lean_ctor_set(x_347, 0, x_483);
lean_inc(x_471);
x_486 = l___private_Init_Data_Repr_0__Nat_reprFast(x_471);
x_487 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_487, 0, x_486);
x_488 = l_Lean_MessageData_ofFormat(x_487);
lean_ctor_set_tag(x_343, 7);
lean_ctor_set(x_343, 1, x_488);
lean_ctor_set(x_343, 0, x_347);
x_489 = lean_mk_string_unchecked("", 0, 0);
x_490 = l_Lean_stringToMessageData(x_489);
lean_inc(x_490);
x_491 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_491, 0, x_343);
lean_ctor_set(x_491, 1, x_490);
if (x_2 == 0)
{
lean_object* x_492; lean_object* x_493; 
lean_dec(x_490);
lean_dec(x_18);
lean_dec(x_14);
x_492 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_492, 0, x_489);
x_493 = l_Lean_MessageData_ofFormat(x_492);
x_244 = x_341;
x_245 = x_340;
x_246 = x_397;
x_247 = x_396;
x_248 = x_339;
x_249 = x_338;
x_250 = x_471;
x_251 = x_476;
x_252 = x_491;
x_253 = x_493;
goto block_257;
}
else
{
lean_object* x_494; lean_object* x_495; 
lean_dec(x_489);
x_494 = lean_mk_string_unchecked(", ", 2, 2);
x_495 = l_Lean_stringToMessageData(x_494);
lean_dec(x_494);
if (lean_obj_tag(x_396) == 0)
{
lean_object* x_496; lean_object* x_497; lean_object* x_498; 
x_496 = lean_mk_string_unchecked("none", 4, 4);
x_497 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_497, 0, x_496);
x_498 = l_Lean_MessageData_ofFormat(x_497);
x_281 = x_341;
x_282 = x_340;
x_283 = x_396;
x_284 = x_397;
x_285 = x_490;
x_286 = x_338;
x_287 = x_339;
x_288 = x_495;
x_289 = x_471;
x_290 = x_476;
x_291 = x_491;
x_292 = x_498;
goto block_337;
}
else
{
lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; 
x_499 = lean_ctor_get(x_396, 0);
lean_inc(x_499);
x_500 = lean_mk_string_unchecked("some (", 6, 6);
x_501 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_501, 0, x_500);
x_502 = l_Lean_MessageData_ofFormat(x_501);
x_503 = l___private_Init_Data_Repr_0__Nat_reprFast(x_499);
x_504 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_504, 0, x_503);
x_505 = l_Lean_MessageData_ofFormat(x_504);
x_506 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_506, 0, x_502);
lean_ctor_set(x_506, 1, x_505);
x_507 = lean_mk_string_unchecked(")", 1, 1);
x_508 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_508, 0, x_507);
x_509 = l_Lean_MessageData_ofFormat(x_508);
x_510 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_510, 0, x_506);
lean_ctor_set(x_510, 1, x_509);
x_281 = x_341;
x_282 = x_340;
x_283 = x_396;
x_284 = x_397;
x_285 = x_490;
x_286 = x_338;
x_287 = x_339;
x_288 = x_495;
x_289 = x_471;
x_290 = x_476;
x_291 = x_491;
x_292 = x_510;
goto block_337;
}
}
}
}
}
else
{
lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; uint8_t x_518; 
x_511 = lean_ctor_get(x_347, 1);
lean_inc(x_511);
lean_dec(x_347);
x_512 = lean_ctor_get(x_348, 4);
lean_inc(x_512);
x_513 = lean_ctor_get(x_348, 5);
lean_inc(x_513);
lean_dec(x_348);
x_514 = lean_ctor_get(x_349, 0);
lean_inc(x_514);
if (lean_is_exclusive(x_349)) {
 lean_ctor_release(x_349, 0);
 x_515 = x_349;
} else {
 lean_dec_ref(x_349);
 x_515 = lean_box(0);
}
lean_inc(x_67);
x_516 = l_Lean_isTracingEnabledFor___at___Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_spec__2___redArg(x_67, x_340, x_511);
x_517 = lean_ctor_get(x_516, 0);
lean_inc(x_517);
x_518 = lean_unbox(x_517);
lean_dec(x_517);
if (x_518 == 0)
{
lean_object* x_519; 
lean_dec(x_515);
lean_free_object(x_343);
lean_dec(x_22);
lean_dec(x_18);
lean_dec(x_14);
x_519 = lean_ctor_get(x_516, 1);
lean_inc(x_519);
lean_dec(x_516);
x_230 = x_512;
x_231 = x_513;
x_232 = x_514;
x_233 = x_338;
x_234 = x_339;
x_235 = x_340;
x_236 = x_341;
x_237 = x_519;
goto block_243;
}
else
{
lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; 
x_520 = lean_ctor_get(x_516, 1);
lean_inc(x_520);
if (lean_is_exclusive(x_516)) {
 lean_ctor_release(x_516, 0);
 lean_ctor_release(x_516, 1);
 x_521 = x_516;
} else {
 lean_dec_ref(x_516);
 x_521 = lean_box(0);
}
x_522 = lean_mk_string_unchecked("...precedences are ", 19, 19);
x_523 = l_Lean_stringToMessageData(x_522);
lean_dec(x_522);
lean_inc(x_4);
x_524 = l___private_Init_Data_Repr_0__Nat_reprFast(x_4);
if (lean_is_scalar(x_515)) {
 x_525 = lean_alloc_ctor(3, 1, 0);
} else {
 x_525 = x_515;
 lean_ctor_set_tag(x_525, 3);
}
lean_ctor_set(x_525, 0, x_524);
x_526 = l_Lean_MessageData_ofFormat(x_525);
if (lean_is_scalar(x_521)) {
 x_527 = lean_alloc_ctor(7, 2, 0);
} else {
 x_527 = x_521;
 lean_ctor_set_tag(x_527, 7);
}
lean_ctor_set(x_527, 0, x_523);
lean_ctor_set(x_527, 1, x_526);
x_528 = lean_mk_string_unchecked(" >\? ", 4, 4);
x_529 = l_Lean_stringToMessageData(x_528);
lean_dec(x_528);
x_530 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_530, 0, x_527);
lean_ctor_set(x_530, 1, x_529);
lean_inc(x_514);
x_531 = l___private_Init_Data_Repr_0__Nat_reprFast(x_514);
x_532 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_532, 0, x_531);
x_533 = l_Lean_MessageData_ofFormat(x_532);
lean_ctor_set_tag(x_343, 7);
lean_ctor_set(x_343, 1, x_533);
lean_ctor_set(x_343, 0, x_530);
x_534 = lean_mk_string_unchecked("", 0, 0);
x_535 = l_Lean_stringToMessageData(x_534);
lean_inc(x_535);
x_536 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_536, 0, x_343);
lean_ctor_set(x_536, 1, x_535);
if (x_2 == 0)
{
lean_object* x_537; lean_object* x_538; 
lean_dec(x_535);
lean_dec(x_18);
lean_dec(x_14);
x_537 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_537, 0, x_534);
x_538 = l_Lean_MessageData_ofFormat(x_537);
x_244 = x_341;
x_245 = x_340;
x_246 = x_513;
x_247 = x_512;
x_248 = x_339;
x_249 = x_338;
x_250 = x_514;
x_251 = x_520;
x_252 = x_536;
x_253 = x_538;
goto block_257;
}
else
{
lean_object* x_539; lean_object* x_540; 
lean_dec(x_534);
x_539 = lean_mk_string_unchecked(", ", 2, 2);
x_540 = l_Lean_stringToMessageData(x_539);
lean_dec(x_539);
if (lean_obj_tag(x_512) == 0)
{
lean_object* x_541; lean_object* x_542; lean_object* x_543; 
x_541 = lean_mk_string_unchecked("none", 4, 4);
x_542 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_542, 0, x_541);
x_543 = l_Lean_MessageData_ofFormat(x_542);
x_281 = x_341;
x_282 = x_340;
x_283 = x_512;
x_284 = x_513;
x_285 = x_535;
x_286 = x_338;
x_287 = x_339;
x_288 = x_540;
x_289 = x_514;
x_290 = x_520;
x_291 = x_536;
x_292 = x_543;
goto block_337;
}
else
{
lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; 
x_544 = lean_ctor_get(x_512, 0);
lean_inc(x_544);
x_545 = lean_mk_string_unchecked("some (", 6, 6);
x_546 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_546, 0, x_545);
x_547 = l_Lean_MessageData_ofFormat(x_546);
x_548 = l___private_Init_Data_Repr_0__Nat_reprFast(x_544);
x_549 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_549, 0, x_548);
x_550 = l_Lean_MessageData_ofFormat(x_549);
x_551 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_551, 0, x_547);
lean_ctor_set(x_551, 1, x_550);
x_552 = lean_mk_string_unchecked(")", 1, 1);
x_553 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_553, 0, x_552);
x_554 = l_Lean_MessageData_ofFormat(x_553);
x_555 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_555, 0, x_551);
lean_ctor_set(x_555, 1, x_554);
x_281 = x_341;
x_282 = x_340;
x_283 = x_512;
x_284 = x_513;
x_285 = x_535;
x_286 = x_338;
x_287 = x_339;
x_288 = x_540;
x_289 = x_514;
x_290 = x_520;
x_291 = x_536;
x_292 = x_555;
goto block_337;
}
}
}
}
}
}
else
{
lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; 
x_556 = lean_ctor_get(x_343, 1);
lean_inc(x_556);
lean_dec(x_343);
x_557 = lean_st_ref_get(x_339, x_556);
x_558 = lean_ctor_get(x_557, 0);
lean_inc(x_558);
x_559 = lean_ctor_get(x_558, 3);
lean_inc(x_559);
if (lean_obj_tag(x_559) == 0)
{
lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; uint8_t x_564; 
lean_dec(x_558);
lean_dec(x_339);
lean_dec(x_338);
lean_dec(x_31);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_560 = lean_ctor_get(x_557, 1);
lean_inc(x_560);
if (lean_is_exclusive(x_557)) {
 lean_ctor_release(x_557, 0);
 lean_ctor_release(x_557, 1);
 x_561 = x_557;
} else {
 lean_dec_ref(x_557);
 x_561 = lean_box(0);
}
lean_inc(x_67);
x_562 = l_Lean_isTracingEnabledFor___at___Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_spec__2___redArg(x_67, x_340, x_560);
x_563 = lean_ctor_get(x_562, 0);
lean_inc(x_563);
x_564 = lean_unbox(x_563);
lean_dec(x_563);
if (x_564 == 0)
{
lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; 
lean_dec(x_561);
lean_dec(x_341);
lean_dec(x_340);
lean_dec(x_67);
lean_dec(x_12);
x_565 = lean_ctor_get(x_562, 1);
lean_inc(x_565);
if (lean_is_exclusive(x_562)) {
 lean_ctor_release(x_562, 0);
 lean_ctor_release(x_562, 1);
 x_566 = x_562;
} else {
 lean_dec_ref(x_562);
 x_566 = lean_box(0);
}
x_567 = lean_box(0);
if (lean_is_scalar(x_566)) {
 x_568 = lean_alloc_ctor(0, 2, 0);
} else {
 x_568 = x_566;
}
lean_ctor_set(x_568, 0, x_567);
lean_ctor_set(x_568, 1, x_565);
return x_568;
}
else
{
lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; uint8_t x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; 
x_569 = lean_ctor_get(x_562, 1);
lean_inc(x_569);
lean_dec(x_562);
x_570 = lean_mk_string_unchecked("visited a syntax tree without precedences\?!", 43, 43);
x_571 = l_Lean_stringToMessageData(x_570);
lean_dec(x_570);
x_572 = lean_box(1);
x_573 = lean_unbox(x_26);
x_574 = l_Lean_Syntax_formatStx(x_12, x_559, x_573);
if (lean_is_scalar(x_561)) {
 x_575 = lean_alloc_ctor(5, 2, 0);
} else {
 x_575 = x_561;
 lean_ctor_set_tag(x_575, 5);
}
lean_ctor_set(x_575, 0, x_572);
lean_ctor_set(x_575, 1, x_574);
x_576 = l_Lean_MessageData_ofFormat(x_575);
x_577 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_577, 0, x_571);
lean_ctor_set(x_577, 1, x_576);
x_578 = lean_mk_string_unchecked("", 0, 0);
x_579 = l_Lean_stringToMessageData(x_578);
lean_dec(x_578);
x_580 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_580, 0, x_577);
lean_ctor_set(x_580, 1, x_579);
x_581 = l_Lean_addTrace___at___Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_spec__3___redArg(x_67, x_580, x_340, x_341, x_569);
lean_dec(x_341);
lean_dec(x_340);
return x_581;
}
}
else
{
lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; uint8_t x_590; 
lean_dec(x_12);
x_582 = lean_ctor_get(x_557, 1);
lean_inc(x_582);
if (lean_is_exclusive(x_557)) {
 lean_ctor_release(x_557, 0);
 lean_ctor_release(x_557, 1);
 x_583 = x_557;
} else {
 lean_dec_ref(x_557);
 x_583 = lean_box(0);
}
x_584 = lean_ctor_get(x_558, 4);
lean_inc(x_584);
x_585 = lean_ctor_get(x_558, 5);
lean_inc(x_585);
lean_dec(x_558);
x_586 = lean_ctor_get(x_559, 0);
lean_inc(x_586);
if (lean_is_exclusive(x_559)) {
 lean_ctor_release(x_559, 0);
 x_587 = x_559;
} else {
 lean_dec_ref(x_559);
 x_587 = lean_box(0);
}
lean_inc(x_67);
x_588 = l_Lean_isTracingEnabledFor___at___Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_spec__2___redArg(x_67, x_340, x_582);
x_589 = lean_ctor_get(x_588, 0);
lean_inc(x_589);
x_590 = lean_unbox(x_589);
lean_dec(x_589);
if (x_590 == 0)
{
lean_object* x_591; 
lean_dec(x_587);
lean_dec(x_583);
lean_dec(x_22);
lean_dec(x_18);
lean_dec(x_14);
x_591 = lean_ctor_get(x_588, 1);
lean_inc(x_591);
lean_dec(x_588);
x_230 = x_584;
x_231 = x_585;
x_232 = x_586;
x_233 = x_338;
x_234 = x_339;
x_235 = x_340;
x_236 = x_341;
x_237 = x_591;
goto block_243;
}
else
{
lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; 
x_592 = lean_ctor_get(x_588, 1);
lean_inc(x_592);
if (lean_is_exclusive(x_588)) {
 lean_ctor_release(x_588, 0);
 lean_ctor_release(x_588, 1);
 x_593 = x_588;
} else {
 lean_dec_ref(x_588);
 x_593 = lean_box(0);
}
x_594 = lean_mk_string_unchecked("...precedences are ", 19, 19);
x_595 = l_Lean_stringToMessageData(x_594);
lean_dec(x_594);
lean_inc(x_4);
x_596 = l___private_Init_Data_Repr_0__Nat_reprFast(x_4);
if (lean_is_scalar(x_587)) {
 x_597 = lean_alloc_ctor(3, 1, 0);
} else {
 x_597 = x_587;
 lean_ctor_set_tag(x_597, 3);
}
lean_ctor_set(x_597, 0, x_596);
x_598 = l_Lean_MessageData_ofFormat(x_597);
if (lean_is_scalar(x_593)) {
 x_599 = lean_alloc_ctor(7, 2, 0);
} else {
 x_599 = x_593;
 lean_ctor_set_tag(x_599, 7);
}
lean_ctor_set(x_599, 0, x_595);
lean_ctor_set(x_599, 1, x_598);
x_600 = lean_mk_string_unchecked(" >\? ", 4, 4);
x_601 = l_Lean_stringToMessageData(x_600);
lean_dec(x_600);
if (lean_is_scalar(x_583)) {
 x_602 = lean_alloc_ctor(7, 2, 0);
} else {
 x_602 = x_583;
 lean_ctor_set_tag(x_602, 7);
}
lean_ctor_set(x_602, 0, x_599);
lean_ctor_set(x_602, 1, x_601);
lean_inc(x_586);
x_603 = l___private_Init_Data_Repr_0__Nat_reprFast(x_586);
x_604 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_604, 0, x_603);
x_605 = l_Lean_MessageData_ofFormat(x_604);
x_606 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_606, 0, x_602);
lean_ctor_set(x_606, 1, x_605);
x_607 = lean_mk_string_unchecked("", 0, 0);
x_608 = l_Lean_stringToMessageData(x_607);
lean_inc(x_608);
x_609 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_609, 0, x_606);
lean_ctor_set(x_609, 1, x_608);
if (x_2 == 0)
{
lean_object* x_610; lean_object* x_611; 
lean_dec(x_608);
lean_dec(x_18);
lean_dec(x_14);
x_610 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_610, 0, x_607);
x_611 = l_Lean_MessageData_ofFormat(x_610);
x_244 = x_341;
x_245 = x_340;
x_246 = x_585;
x_247 = x_584;
x_248 = x_339;
x_249 = x_338;
x_250 = x_586;
x_251 = x_592;
x_252 = x_609;
x_253 = x_611;
goto block_257;
}
else
{
lean_object* x_612; lean_object* x_613; 
lean_dec(x_607);
x_612 = lean_mk_string_unchecked(", ", 2, 2);
x_613 = l_Lean_stringToMessageData(x_612);
lean_dec(x_612);
if (lean_obj_tag(x_584) == 0)
{
lean_object* x_614; lean_object* x_615; lean_object* x_616; 
x_614 = lean_mk_string_unchecked("none", 4, 4);
x_615 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_615, 0, x_614);
x_616 = l_Lean_MessageData_ofFormat(x_615);
x_281 = x_341;
x_282 = x_340;
x_283 = x_584;
x_284 = x_585;
x_285 = x_608;
x_286 = x_338;
x_287 = x_339;
x_288 = x_613;
x_289 = x_586;
x_290 = x_592;
x_291 = x_609;
x_292 = x_616;
goto block_337;
}
else
{
lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; 
x_617 = lean_ctor_get(x_584, 0);
lean_inc(x_617);
x_618 = lean_mk_string_unchecked("some (", 6, 6);
x_619 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_619, 0, x_618);
x_620 = l_Lean_MessageData_ofFormat(x_619);
x_621 = l___private_Init_Data_Repr_0__Nat_reprFast(x_617);
x_622 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_622, 0, x_621);
x_623 = l_Lean_MessageData_ofFormat(x_622);
x_624 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_624, 0, x_620);
lean_ctor_set(x_624, 1, x_623);
x_625 = lean_mk_string_unchecked(")", 1, 1);
x_626 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_626, 0, x_625);
x_627 = l_Lean_MessageData_ofFormat(x_626);
x_628 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_628, 0, x_624);
lean_ctor_set(x_628, 1, x_627);
x_281 = x_341;
x_282 = x_340;
x_283 = x_584;
x_284 = x_585;
x_285 = x_608;
x_286 = x_338;
x_287 = x_339;
x_288 = x_613;
x_289 = x_586;
x_290 = x_592;
x_291 = x_609;
x_292 = x_628;
goto block_337;
}
}
}
}
}
}
else
{
lean_dec(x_341);
lean_dec(x_340);
lean_dec(x_339);
lean_dec(x_338);
lean_dec(x_67);
lean_dec(x_31);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_343;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getIdx___at___Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_MonadTraverser_getIdx___at___Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_spec__0___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getIdx___at___Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Syntax_MonadTraverser_getIdx___at___Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_setCur___at___Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Syntax_MonadTraverser_setCur___at___Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_spec__1___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_setCur___at___Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Syntax_MonadTraverser_setCur___at___Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isTracingEnabledFor___at___Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_spec__2___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_isTracingEnabledFor___at___Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_addTrace___at___Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_spec__3___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_addTrace___at___Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goRight___at___Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_MonadTraverser_goRight___at___Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_spec__4___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goRight___at___Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Syntax_MonadTraverser_goRight___at___Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_spec__4(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_2);
lean_dec(x_2);
x_12 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_3 = lean_st_ref_take(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_box(0);
x_8 = lean_box(0);
x_9 = lean_ctor_get(x_4, 3);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 4);
lean_inc(x_10);
x_11 = lean_ctor_get(x_4, 5);
lean_inc(x_11);
lean_dec(x_4);
x_12 = lean_box(1);
x_13 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_7);
lean_ctor_set(x_13, 2, x_8);
lean_ctor_set(x_13, 3, x_9);
lean_ctor_set(x_13, 4, x_10);
lean_ctor_set(x_13, 5, x_11);
x_14 = lean_unbox(x_12);
lean_ctor_set_uint8(x_13, sizeof(void*)*6, x_14);
x_15 = lean_st_ref_set(x_1, x_13, x_5);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_Syntax_MonadTraverser_goLeft___at___Lean_PrettyPrinter_Parenthesizer_visitArgs_spec__1___redArg(x_1, x_16);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_visitToken(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_visitToken___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Parenthesizer_visitToken(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at___Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_object* x_13; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_13 = l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(x_1, x_2, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_3, x_15);
lean_dec(x_3);
x_3 = x_16;
x_8 = x_14;
goto _start;
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at___Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Nat_forM_loop___at___Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer_spec__0___redArg(x_1, x_2, x_4, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_8 = l_Lean_Syntax_MonadTraverser_getCur___at___Lean_PrettyPrinter_Parenthesizer_visitArgs_spec__2___redArg(x_4, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_9);
x_11 = l_Lean_Syntax_getKind(x_9);
x_12 = lean_mk_string_unchecked("choice", 6, 6);
x_13 = l_Lean_Name_mkStr1(x_12);
x_14 = lean_name_eq(x_11, x_13);
lean_dec(x_13);
lean_dec(x_11);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_9);
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
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = l_Lean_Syntax_getArgs(x_9);
lean_dec(x_9);
x_32 = lean_array_get_size(x_31);
lean_dec(x_31);
lean_inc(x_32);
x_33 = lean_alloc_closure((void*)(l_Nat_forM_loop___at___Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer_spec__0___boxed), 10, 5);
lean_closure_set(x_33, 0, x_1);
lean_closure_set(x_33, 1, x_2);
lean_closure_set(x_33, 2, x_32);
lean_closure_set(x_33, 3, x_32);
lean_closure_set(x_33, 4, lean_box(0));
x_34 = l_Lean_PrettyPrinter_Parenthesizer_visitArgs(x_33, x_3, x_4, x_5, x_6, x_10);
return x_34;
}
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at___Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Nat_forM_loop___at___Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_recover_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_recover_x27_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_mkAntiquot_parenthesizer_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = lean_mk_antiquot_parenthesizer(x_1, x_2, x_10, x_11, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_liftCoreM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_3(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_liftCoreM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_apply_3(x_2, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_liftCoreM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Parenthesizer_liftCoreM(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_interpretParserDescr_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_pretty_printer_parenthesizer_interpret_parser_descr(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKindUnsafe(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_mk_string_unchecked("missing", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_name_eq(x_1, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_11 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_interpretParserDescr_x27___boxed), 4, 0);
lean_inc(x_5);
lean_inc(x_4);
x_12 = l_Lean_PrettyPrinter_runForNodeKind___redArg(x_10, x_1, x_11, x_4, x_5, x_6);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_apply_5(x_13, x_2, x_3, x_4, x_5, x_14);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_6);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_15; 
x_8 = l_Lean_Syntax_MonadTraverser_getCur___at___Lean_PrettyPrinter_Parenthesizer_visitArgs_spec__2___redArg(x_4, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_15 = l_Lean_Syntax_isAntiquot(x_9);
if (x_15 == 0)
{
uint8_t x_16; 
x_16 = l_Lean_Syntax_isAntiquotSplice(x_9);
lean_dec(x_9);
x_11 = x_16;
goto block_14;
}
else
{
lean_dec(x_9);
x_11 = x_15;
goto block_14;
}
block_14:
{
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_1);
x_12 = lean_apply_5(x_2, x_3, x_4, x_5, x_6, x_10);
return x_12;
}
else
{
lean_object* x_13; 
x_13 = l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(x_1, x_2, x_3, x_4, x_5, x_6, x_10);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_withAntiquotSuffixSplice_parenthesizer___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_withAntiquotSuffixSplice_parenthesizer___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = l_Lean_Syntax_MonadTraverser_getCur___at___Lean_PrettyPrinter_Parenthesizer_visitArgs_spec__2___redArg(x_4, x_7);
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
x_13 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_withAntiquotSuffixSplice_parenthesizer___redArg___lam__0), 7, 2);
lean_closure_set(x_13, 0, x_2);
lean_closure_set(x_13, 1, x_1);
x_14 = l_Lean_PrettyPrinter_Parenthesizer_visitArgs(x_13, x_3, x_4, x_5, x_6, x_10);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_withAntiquotSuffixSplice_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PrettyPrinter_Parenthesizer_withAntiquotSuffixSplice_parenthesizer___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_withAntiquotSuffixSplice_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PrettyPrinter_Parenthesizer_withAntiquotSuffixSplice_parenthesizer(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_tokenWithAntiquot_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = l_Lean_Syntax_MonadTraverser_getCur___at___Lean_PrettyPrinter_Parenthesizer_visitArgs_spec__2___redArg(x_3, x_6);
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
x_12 = l_Lean_PrettyPrinter_Parenthesizer_visitArgs(x_1, x_2, x_3, x_4, x_5, x_9);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at___Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_object* x_13; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_2);
lean_inc(x_1);
x_13 = l_Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore(x_1, x_2, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_3, x_15);
lean_dec(x_3);
x_3 = x_16;
x_8 = x_14;
goto _start;
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at___Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Nat_forM_loop___at___Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore_spec__0___redArg(x_1, x_2, x_4, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT uint8_t l_Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore___lam__0(uint8_t x_1, lean_object* x_2) {
_start:
{
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_28 = l_Lean_Syntax_MonadTraverser_getCur___at___Lean_PrettyPrinter_Parenthesizer_visitArgs_spec__2___redArg(x_4, x_7);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_ctor_get_uint8(x_3, sizeof(void*)*1);
lean_inc(x_1);
x_32 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_32, 0, x_1);
lean_ctor_set_uint8(x_32, sizeof(void*)*1, x_31);
lean_inc(x_29);
x_33 = l_Lean_Syntax_getKind(x_29);
x_34 = lean_mk_string_unchecked("choice", 6, 6);
x_35 = l_Lean_Name_mkStr1(x_34);
x_36 = lean_name_eq(x_33, x_35);
lean_dec(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_29);
lean_dec(x_2);
x_37 = lean_box(x_36);
x_38 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore___lam__0___boxed), 2, 1);
lean_closure_set(x_38, 0, x_37);
x_39 = lean_box(1);
x_40 = lean_unbox(x_39);
lean_inc(x_1);
x_41 = l_Lean_Name_toString(x_1, x_40, x_38);
lean_inc(x_1);
x_42 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_mkAntiquot_parenthesizer_x27___boxed), 9, 4);
lean_closure_set(x_42, 0, x_41);
lean_closure_set(x_42, 1, x_1);
lean_closure_set(x_42, 2, x_39);
lean_closure_set(x_42, 3, x_39);
x_43 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKindUnsafe), 6, 1);
lean_closure_set(x_43, 0, x_33);
lean_inc(x_4);
x_44 = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(x_42, x_43, x_32, x_4, x_5, x_6, x_30);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_8 = x_4;
x_9 = x_45;
goto block_27;
}
else
{
lean_dec(x_4);
lean_dec(x_1);
return x_44;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_33);
x_46 = l_Lean_Syntax_getArgs(x_29);
lean_dec(x_29);
x_47 = lean_array_get_size(x_46);
lean_dec(x_46);
lean_inc(x_47);
lean_inc(x_1);
x_48 = lean_alloc_closure((void*)(l_Nat_forM_loop___at___Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore_spec__0___boxed), 10, 5);
lean_closure_set(x_48, 0, x_1);
lean_closure_set(x_48, 1, x_2);
lean_closure_set(x_48, 2, x_47);
lean_closure_set(x_48, 3, x_47);
lean_closure_set(x_48, 4, lean_box(0));
lean_inc(x_4);
x_49 = l_Lean_PrettyPrinter_Parenthesizer_visitArgs(x_48, x_32, x_4, x_5, x_6, x_30);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec(x_49);
x_8 = x_4;
x_9 = x_50;
goto block_27;
}
else
{
lean_dec(x_4);
lean_dec(x_1);
return x_49;
}
}
block_27:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_10 = lean_st_ref_take(x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_11, 3);
lean_inc(x_15);
x_16 = lean_ctor_get(x_11, 4);
lean_inc(x_16);
x_17 = lean_ctor_get(x_11, 5);
lean_inc(x_17);
x_18 = lean_ctor_get_uint8(x_11, sizeof(void*)*6);
lean_dec(x_11);
x_19 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_14);
lean_ctor_set(x_19, 2, x_1);
lean_ctor_set(x_19, 3, x_15);
lean_ctor_set(x_19, 4, x_16);
lean_ctor_set(x_19, 5, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*6, x_18);
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
LEAN_EXPORT lean_object* l_Nat_forM_loop___at___Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Nat_forM_loop___at___Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at___Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Nat_forM_loop___at___Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore___lam__0(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_PrettyPrinter_categoryParenthesizerAttribute;
x_13 = l_Lean_KeyedDeclsAttribute_getValues___redArg(x_12, x_11, x_1);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = l_Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore(x_1, x_2, x_3, x_4, x_5, x_6, x_10);
lean_dec(x_3);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_1);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_apply_6(x_15, x_2, x_3, x_4, x_5, x_6, x_10);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_parserOfStack_parenthesizer___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_20 = l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKindUnsafe(x_19, x_2, x_3, x_4, x_5, x_9);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_parserOfStack_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Parenthesizer_parserOfStack_parenthesizer___redArg(x_1, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_parserOfStack_parenthesizer___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Parenthesizer_parserOfStack_parenthesizer___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_parserOfStack_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Parenthesizer_parserOfStack_parenthesizer(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer_wrapParens(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
x_4 = l_Lean_SourceInfo_fromRef(x_1, x_3);
x_5 = lean_box(2);
x_6 = l_Lean_Syntax_setInfo(x_5, x_1);
x_7 = lean_box(0);
x_8 = lean_unbox(x_2);
x_9 = l_Lean_SourceInfo_fromRef(x_7, x_8);
x_10 = lean_mk_string_unchecked("Lean", 4, 4);
x_11 = lean_mk_string_unchecked("Parser", 6, 6);
x_12 = lean_mk_string_unchecked("Term", 4, 4);
x_13 = lean_mk_string_unchecked("paren", 5, 5);
x_14 = l_Lean_Name_mkStr4(x_10, x_11, x_12, x_13);
x_15 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_9);
x_16 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_9);
x_18 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_18, 0, x_9);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_Syntax_node3(x_9, x_14, x_16, x_6, x_18);
x_20 = l_Lean_Syntax_setInfo(x_4, x_19);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_7 = lean_mk_string_unchecked("term", 4, 4);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_box(1);
x_10 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer_wrapParens), 1, 0);
lean_inc(x_1);
lean_inc(x_8);
x_11 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore___boxed), 7, 2);
lean_closure_set(x_11, 0, x_8);
lean_closure_set(x_11, 1, x_1);
x_12 = lean_unbox(x_9);
x_13 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize(x_8, x_12, x_10, x_1, x_11, x_2, x_3, x_4, x_5, x_6);
return x_13;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_categoryParenthesizerAttribute;
x_3 = lean_mk_string_unchecked("term", 4, 4);
lean_inc(x_3);
x_4 = l_Lean_Name_mkStr1(x_3);
x_5 = lean_mk_string_unchecked("Lean", 4, 4);
x_6 = lean_mk_string_unchecked("PrettyPrinter", 13, 13);
x_7 = lean_mk_string_unchecked("Parenthesizer", 13, 13);
x_8 = lean_mk_string_unchecked("parenthesizer", 13, 13);
x_9 = l_Lean_Name_mkStr5(x_5, x_6, x_7, x_3, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer), 6, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_4, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_2 = lean_box(0);
x_3 = lean_box(0);
x_4 = lean_unbox(x_3);
x_5 = l_Lean_SourceInfo_fromRef(x_2, x_4);
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("Parser", 6, 6);
x_8 = lean_mk_string_unchecked("Tactic", 6, 6);
x_9 = lean_mk_string_unchecked("paren", 5, 5);
x_10 = l_Lean_Name_mkStr4(x_6, x_7, x_8, x_9);
x_11 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_5);
x_12 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_5);
x_14 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_14, 0, x_5);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_Syntax_node3(x_5, x_10, x_12, x_1, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_7 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lam__0), 1, 0);
x_8 = lean_mk_string_unchecked("tactic", 6, 6);
x_9 = l_Lean_Name_mkStr1(x_8);
x_10 = lean_box(0);
lean_inc(x_1);
lean_inc(x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore___boxed), 7, 2);
lean_closure_set(x_11, 0, x_9);
lean_closure_set(x_11, 1, x_1);
x_12 = lean_unbox(x_10);
x_13 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize(x_9, x_12, x_7, x_1, x_11, x_2, x_3, x_4, x_5, x_6);
return x_13;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_categoryParenthesizerAttribute;
x_3 = lean_mk_string_unchecked("tactic", 6, 6);
lean_inc(x_3);
x_4 = l_Lean_Name_mkStr1(x_3);
x_5 = lean_mk_string_unchecked("Lean", 4, 4);
x_6 = lean_mk_string_unchecked("PrettyPrinter", 13, 13);
x_7 = lean_mk_string_unchecked("Parenthesizer", 13, 13);
x_8 = lean_mk_string_unchecked("parenthesizer", 13, 13);
x_9 = l_Lean_Name_mkStr5(x_5, x_6, x_7, x_3, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer), 6, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_4, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_2 = lean_box(0);
x_3 = lean_box(0);
x_4 = lean_unbox(x_3);
x_5 = l_Lean_SourceInfo_fromRef(x_2, x_4);
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("Parser", 6, 6);
x_8 = lean_mk_string_unchecked("Level", 5, 5);
x_9 = lean_mk_string_unchecked("paren", 5, 5);
x_10 = l_Lean_Name_mkStr4(x_6, x_7, x_8, x_9);
x_11 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_5);
x_12 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_5);
x_14 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_14, 0, x_5);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_Syntax_node3(x_5, x_10, x_12, x_1, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_7 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___lam__0), 1, 0);
x_8 = lean_mk_string_unchecked("level", 5, 5);
x_9 = l_Lean_Name_mkStr1(x_8);
x_10 = lean_box(0);
lean_inc(x_1);
lean_inc(x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore___boxed), 7, 2);
lean_closure_set(x_11, 0, x_9);
lean_closure_set(x_11, 1, x_1);
x_12 = lean_unbox(x_10);
x_13 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize(x_9, x_12, x_7, x_1, x_11, x_2, x_3, x_4, x_5, x_6);
return x_13;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_categoryParenthesizerAttribute;
x_3 = lean_mk_string_unchecked("level", 5, 5);
lean_inc(x_3);
x_4 = l_Lean_Name_mkStr1(x_3);
x_5 = lean_mk_string_unchecked("Lean", 4, 4);
x_6 = lean_mk_string_unchecked("PrettyPrinter", 13, 13);
x_7 = lean_mk_string_unchecked("Parenthesizer", 13, 13);
x_8 = lean_mk_string_unchecked("parenthesizer", 13, 13);
x_9 = l_Lean_Name_mkStr5(x_5, x_6, x_7, x_3, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer), 6, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_4, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_rawStx_parenthesizer___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_MonadTraverser_goLeft___at___Lean_PrettyPrinter_Parenthesizer_visitArgs_spec__1___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_rawStx_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Syntax_MonadTraverser_goLeft___at___Lean_PrettyPrinter_Parenthesizer_visitArgs_spec__1___redArg(x_3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_rawStx_parenthesizer___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PrettyPrinter_Parenthesizer_rawStx_parenthesizer___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_rawStx_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Parenthesizer_rawStx_parenthesizer(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_rawStx_parenthesizer__1___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Syntax_MonadTraverser_goLeft___at___Lean_PrettyPrinter_Parenthesizer_visitArgs_spec__1___redArg(x_3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_rawStx_parenthesizer__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = lean_alloc_closure((void*)(l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_rawStx_parenthesizer__1___lam__0___boxed), 6, 0);
x_3 = l_Lean_PrettyPrinter_categoryParenthesizerAttribute;
x_4 = lean_mk_string_unchecked("rawStx", 6, 6);
lean_inc(x_4);
x_5 = l_Lean_Name_mkStr1(x_4);
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("PrettyPrinter", 13, 13);
x_8 = lean_mk_string_unchecked("Parenthesizer", 13, 13);
x_9 = lean_mk_string_unchecked("parenthesizer", 13, 13);
x_10 = l_Lean_Name_mkStr5(x_6, x_7, x_8, x_4, x_9);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_3, x_5, x_10, x_2, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_rawStx_parenthesizer__1___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_rawStx_parenthesizer__1___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_error_parenthesizer___redArg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_error_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Parenthesizer_error_parenthesizer___redArg(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_error_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Parenthesizer_error_parenthesizer(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_errorAtSavedPos_parenthesizer___redArg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_errorAtSavedPos_parenthesizer(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Parenthesizer_errorAtSavedPos_parenthesizer___redArg(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_errorAtSavedPos_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Lean_PrettyPrinter_Parenthesizer_errorAtSavedPos_parenthesizer(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_atomic_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_lookahead_parenthesizer___redArg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_lookahead_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Parenthesizer_lookahead_parenthesizer___redArg(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_lookahead_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Parenthesizer_lookahead_parenthesizer(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_notFollowedBy_parenthesizer___redArg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_notFollowedBy_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Parenthesizer_notFollowedBy_parenthesizer___redArg(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_notFollowedBy_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Parenthesizer_notFollowedBy_parenthesizer(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkKind___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_Lean_Syntax_MonadTraverser_getCur___at___Lean_PrettyPrinter_Parenthesizer_visitArgs_spec__2___redArg(x_2, x_5);
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
x_13 = lean_mk_string_unchecked("parenthesize", 12, 12);
x_14 = lean_mk_string_unchecked("backtrack", 9, 9);
x_15 = l_Lean_Name_mkStr3(x_12, x_13, x_14);
lean_inc(x_15);
x_16 = l_Lean_isTracingEnabledFor___at___Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_spec__2___redArg(x_15, x_3, x_9);
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
x_20 = l_Lean_PrettyPrinter_Parenthesizer_throwBacktrack___redArg(x_19);
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
x_35 = l_Lean_addTrace___at___Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_spec__3___redArg(x_15, x_34, x_3, x_4, x_22);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = l_Lean_PrettyPrinter_Parenthesizer_throwBacktrack___redArg(x_36);
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
x_51 = l_Lean_addTrace___at___Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_spec__3___redArg(x_15, x_50, x_3, x_4, x_38);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec(x_51);
x_53 = l_Lean_PrettyPrinter_Parenthesizer_throwBacktrack___redArg(x_52);
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
x_60 = lean_mk_string_unchecked("parenthesize", 12, 12);
x_61 = lean_mk_string_unchecked("backtrack", 9, 9);
x_62 = l_Lean_Name_mkStr3(x_59, x_60, x_61);
lean_inc(x_62);
x_63 = l_Lean_isTracingEnabledFor___at___Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_spec__2___redArg(x_62, x_3, x_56);
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
x_67 = l_Lean_PrettyPrinter_Parenthesizer_throwBacktrack___redArg(x_66);
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
x_82 = l_Lean_addTrace___at___Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_spec__3___redArg(x_62, x_81, x_3, x_4, x_68);
x_83 = lean_ctor_get(x_82, 1);
lean_inc(x_83);
lean_dec(x_82);
x_84 = l_Lean_PrettyPrinter_Parenthesizer_throwBacktrack___redArg(x_83);
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkKind(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Parenthesizer_checkKind___redArg(x_1, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkKind___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Parenthesizer_checkKind___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkKind___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Parenthesizer_checkKind(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Parenthesizer_checkKind___redArg(x_1, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Lean_PrettyPrinter_Parenthesizer_visitArgs(x_2, x_3, x_4, x_5, x_6, x_9);
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkPrec_parenthesizer___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PrettyPrinter_Parenthesizer_addPrecCheck___redArg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkPrec_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Parenthesizer_addPrecCheck___redArg(x_1, x_3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkPrec_parenthesizer___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PrettyPrinter_Parenthesizer_checkPrec_parenthesizer___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkPrec_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Parenthesizer_checkPrec_parenthesizer(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_withFn_parenthesizer___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_withFn_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_apply_5(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_withFn_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Parenthesizer_withFn_parenthesizer(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_5);
x_9 = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_32; uint8_t x_33; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
lean_inc(x_2);
x_11 = l_Lean_PrettyPrinter_Parenthesizer_addPrecCheck___redArg(x_2, x_5, x_10);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_st_ref_take(x_5, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_box(0);
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
x_32 = lean_unsigned_to_nat(1023u);
x_33 = lean_nat_dec_le(x_32, x_2);
if (x_33 == 0)
{
x_18 = x_2;
goto block_31;
}
else
{
lean_dec(x_2);
x_18 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_ctor_get(x_14, 2);
lean_inc(x_20);
x_21 = lean_ctor_get(x_14, 3);
lean_inc(x_21);
x_22 = lean_ctor_get(x_14, 4);
lean_inc(x_22);
x_23 = lean_ctor_get(x_14, 5);
lean_inc(x_23);
x_24 = lean_ctor_get_uint8(x_14, sizeof(void*)*6);
lean_dec(x_14);
x_25 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_25, 0, x_17);
lean_ctor_set(x_25, 1, x_19);
lean_ctor_set(x_25, 2, x_20);
lean_ctor_set(x_25, 3, x_21);
lean_ctor_set(x_25, 4, x_22);
lean_ctor_set(x_25, 5, x_23);
lean_ctor_set_uint8(x_25, sizeof(void*)*6, x_24);
x_26 = lean_st_ref_set(x_5, x_25, x_15);
lean_dec(x_5);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
lean_ctor_set(x_26, 0, x_16);
return x_26;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_16);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
lean_dec(x_5);
lean_dec(x_2);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_9 = lean_apply_5(x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_PrettyPrinter_Parenthesizer_addPrecCheck___redArg(x_2, x_5, x_10);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_st_ref_take(x_5, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_4, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_14, 3);
lean_inc(x_19);
x_20 = lean_ctor_get(x_14, 4);
lean_inc(x_20);
x_21 = lean_ctor_get(x_14, 5);
lean_inc(x_21);
x_22 = lean_ctor_get_uint8(x_14, sizeof(void*)*6);
lean_dec(x_14);
lean_inc(x_18);
x_23 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_23, 0, x_16);
lean_ctor_set(x_23, 1, x_17);
lean_ctor_set(x_23, 2, x_18);
lean_ctor_set(x_23, 3, x_19);
lean_ctor_set(x_23, 4, x_20);
lean_ctor_set(x_23, 5, x_21);
lean_ctor_set_uint8(x_23, sizeof(void*)*6, x_22);
x_24 = lean_st_ref_set(x_5, x_23, x_15);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer(x_18, x_3, x_4, x_5, x_6, x_7, x_25);
return x_26;
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_PrettyPrinter_Parenthesizer_checkKind___redArg(x_1, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___lam__0), 8, 3);
lean_closure_set(x_12, 0, x_4);
lean_closure_set(x_12, 1, x_2);
lean_closure_set(x_12, 2, x_3);
x_13 = l_Lean_PrettyPrinter_Parenthesizer_visitArgs(x_12, x_5, x_6, x_7, x_8, x_11);
return x_13;
}
else
{
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
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_rawCh_parenthesizer___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_rawCh_parenthesizer(uint32_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(x_3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_rawCh_parenthesizer___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PrettyPrinter_Parenthesizer_rawCh_parenthesizer___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_rawCh_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint32_t x_7; lean_object* x_8; 
x_7 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_8 = l_Lean_PrettyPrinter_Parenthesizer_rawCh_parenthesizer(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_symbolNoAntiquot_parenthesizer___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_symbolNoAntiquot_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(x_3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_symbolNoAntiquot_parenthesizer___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PrettyPrinter_Parenthesizer_symbolNoAntiquot_parenthesizer___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_symbolNoAntiquot_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Parenthesizer_symbolNoAntiquot_parenthesizer(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_unicodeSymbolNoAntiquot_parenthesizer___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_unicodeSymbolNoAntiquot_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(x_4, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_unicodeSymbolNoAntiquot_parenthesizer___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PrettyPrinter_Parenthesizer_unicodeSymbolNoAntiquot_parenthesizer___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_unicodeSymbolNoAntiquot_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Parenthesizer_unicodeSymbolNoAntiquot_parenthesizer(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_identNoAntiquot_parenthesizer___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_mk_string_unchecked("ident", 5, 5);
x_6 = l_Lean_Name_mkStr1(x_5);
x_7 = l_Lean_PrettyPrinter_Parenthesizer_checkKind___redArg(x_6, x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(x_1, x_8);
return x_9;
}
else
{
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_identNoAntiquot_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Parenthesizer_identNoAntiquot_parenthesizer___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_identNoAntiquot_parenthesizer___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Parenthesizer_identNoAntiquot_parenthesizer___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_identNoAntiquot_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Parenthesizer_identNoAntiquot_parenthesizer(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_rawIdentNoAntiquot_parenthesizer___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_rawIdentNoAntiquot_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_rawIdentNoAntiquot_parenthesizer___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PrettyPrinter_Parenthesizer_rawIdentNoAntiquot_parenthesizer___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_rawIdentNoAntiquot_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Parenthesizer_rawIdentNoAntiquot_parenthesizer(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_identEq_parenthesizer___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_identEq_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(x_3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_identEq_parenthesizer___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PrettyPrinter_Parenthesizer_identEq_parenthesizer___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_identEq_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Parenthesizer_identEq_parenthesizer(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_nonReservedSymbolNoAntiquot_parenthesizer___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_nonReservedSymbolNoAntiquot_parenthesizer(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(x_4, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_nonReservedSymbolNoAntiquot_parenthesizer___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PrettyPrinter_Parenthesizer_nonReservedSymbolNoAntiquot_parenthesizer___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_nonReservedSymbolNoAntiquot_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Lean_PrettyPrinter_Parenthesizer_nonReservedSymbolNoAntiquot_parenthesizer(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_charLitNoAntiquot_parenthesizer___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_charLitNoAntiquot_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_charLitNoAntiquot_parenthesizer___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PrettyPrinter_Parenthesizer_charLitNoAntiquot_parenthesizer___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_charLitNoAntiquot_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Parenthesizer_charLitNoAntiquot_parenthesizer(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_strLitNoAntiquot_parenthesizer___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_strLitNoAntiquot_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_strLitNoAntiquot_parenthesizer___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PrettyPrinter_Parenthesizer_strLitNoAntiquot_parenthesizer___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_strLitNoAntiquot_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Parenthesizer_strLitNoAntiquot_parenthesizer(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_nameLitNoAntiquot_parenthesizer___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_nameLitNoAntiquot_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_nameLitNoAntiquot_parenthesizer___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PrettyPrinter_Parenthesizer_nameLitNoAntiquot_parenthesizer___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_nameLitNoAntiquot_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Parenthesizer_nameLitNoAntiquot_parenthesizer(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_numLitNoAntiquot_parenthesizer___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_numLitNoAntiquot_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_numLitNoAntiquot_parenthesizer___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PrettyPrinter_Parenthesizer_numLitNoAntiquot_parenthesizer___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_numLitNoAntiquot_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Parenthesizer_numLitNoAntiquot_parenthesizer(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_scientificLitNoAntiquot_parenthesizer___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_scientificLitNoAntiquot_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_scientificLitNoAntiquot_parenthesizer___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PrettyPrinter_Parenthesizer_scientificLitNoAntiquot_parenthesizer___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_scientificLitNoAntiquot_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Parenthesizer_scientificLitNoAntiquot_parenthesizer(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_fieldIdx_parenthesizer___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_fieldIdx_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_fieldIdx_parenthesizer___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PrettyPrinter_Parenthesizer_fieldIdx_parenthesizer___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_fieldIdx_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Parenthesizer_fieldIdx_parenthesizer(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at___Lean_PrettyPrinter_Parenthesizer_manyNoAntiquot_parenthesizer_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l_Nat_forM_loop___at___Lean_PrettyPrinter_Parenthesizer_manyNoAntiquot_parenthesizer_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_forM_loop___at___Lean_PrettyPrinter_Parenthesizer_manyNoAntiquot_parenthesizer_spec__0___redArg(x_1, x_3, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_manyNoAntiquot_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = l_Lean_Syntax_MonadTraverser_getCur___at___Lean_PrettyPrinter_Parenthesizer_visitArgs_spec__2___redArg(x_3, x_6);
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
x_12 = lean_alloc_closure((void*)(l_Nat_forM_loop___at___Lean_PrettyPrinter_Parenthesizer_manyNoAntiquot_parenthesizer_spec__0___boxed), 9, 4);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_11);
lean_closure_set(x_12, 2, x_11);
lean_closure_set(x_12, 3, lean_box(0));
x_13 = l_Lean_PrettyPrinter_Parenthesizer_visitArgs(x_12, x_2, x_3, x_4, x_5, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at___Lean_PrettyPrinter_Parenthesizer_manyNoAntiquot_parenthesizer_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_forM_loop___at___Lean_PrettyPrinter_Parenthesizer_manyNoAntiquot_parenthesizer_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_many1NoAntiquot_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Parenthesizer_manyNoAntiquot_parenthesizer(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_many1Unbox_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_7 = l_Lean_Syntax_MonadTraverser_getCur___at___Lean_PrettyPrinter_Parenthesizer_visitArgs_spec__2___redArg(x_3, x_6);
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
x_15 = l_Lean_PrettyPrinter_Parenthesizer_manyNoAntiquot_parenthesizer(x_1, x_2, x_3, x_4, x_5, x_9);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_optionalNoAntiquot_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Parenthesizer_visitArgs(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___Lean_PrettyPrinter_Parenthesizer_sepByNoAntiquot_parenthesizer_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
x_17 = lean_unsigned_to_nat(2u);
x_18 = lean_nat_mod(x_11, x_17);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_nat_dec_eq(x_18, x_19);
lean_dec(x_18);
if (x_20 == 0)
{
lean_object* x_21; 
lean_inc(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_21 = lean_apply_5(x_1, x_4, x_5, x_6, x_7, x_8);
x_13 = x_21;
goto block_16;
}
else
{
lean_object* x_22; 
lean_inc(x_2);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_22 = lean_apply_5(x_2, x_4, x_5, x_6, x_7, x_8);
x_13 = x_22;
goto block_16;
}
block_16:
{
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_3 = x_12;
x_8 = x_14;
goto _start;
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_sepByNoAntiquot_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_8 = l_Lean_Syntax_MonadTraverser_getCur___at___Lean_PrettyPrinter_Parenthesizer_visitArgs_spec__2___redArg(x_4, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Syntax_getArgs(x_9);
lean_dec(x_9);
x_12 = lean_array_get_size(x_11);
lean_dec(x_11);
x_13 = l_List_range(x_12);
x_14 = l_List_reverse___redArg(x_13);
x_15 = lean_alloc_closure((void*)(l_List_forM___at___Lean_PrettyPrinter_Parenthesizer_sepByNoAntiquot_parenthesizer_spec__0___boxed), 8, 3);
lean_closure_set(x_15, 0, x_2);
lean_closure_set(x_15, 1, x_1);
lean_closure_set(x_15, 2, x_14);
x_16 = l_Lean_PrettyPrinter_Parenthesizer_visitArgs(x_15, x_3, x_4, x_5, x_6, x_10);
return x_16;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___Lean_PrettyPrinter_Parenthesizer_sepByNoAntiquot_parenthesizer_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_forM___at___Lean_PrettyPrinter_Parenthesizer_sepByNoAntiquot_parenthesizer_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_sepBy1NoAntiquot_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Parenthesizer_sepByNoAntiquot_parenthesizer(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_withPosition_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_7 = lean_st_ref_take(x_3, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
x_11 = lean_box(0);
x_12 = lean_ctor_get(x_8, 2);
lean_inc(x_12);
x_13 = lean_ctor_get(x_8, 3);
lean_inc(x_13);
x_14 = lean_ctor_get(x_8, 4);
lean_inc(x_14);
x_15 = lean_ctor_get(x_8, 5);
lean_inc(x_15);
x_16 = lean_ctor_get_uint8(x_8, sizeof(void*)*6);
lean_dec(x_8);
x_17 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_11);
lean_ctor_set(x_17, 2, x_12);
lean_ctor_set(x_17, 3, x_13);
lean_ctor_set(x_17, 4, x_14);
lean_ctor_set(x_17, 5, x_15);
lean_ctor_set_uint8(x_17, sizeof(void*)*6, x_16);
x_18 = lean_st_ref_set(x_3, x_17, x_9);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_19);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_withPositionAfterLinebreak_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Parenthesizer_withPosition_parenthesizer(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_withoutInfo_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkStackTop_parenthesizer___redArg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkStackTop_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Parenthesizer_checkStackTop_parenthesizer___redArg(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkStackTop_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Parenthesizer_checkStackTop_parenthesizer(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkWsBefore_parenthesizer___redArg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkWsBefore_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Parenthesizer_checkWsBefore_parenthesizer___redArg(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkWsBefore_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Parenthesizer_checkWsBefore_parenthesizer(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkNoWsBefore_parenthesizer___redArg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkNoWsBefore_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Parenthesizer_checkNoWsBefore_parenthesizer___redArg(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkNoWsBefore_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Parenthesizer_checkNoWsBefore_parenthesizer(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkLinebreakBefore_parenthesizer___redArg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkLinebreakBefore_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Parenthesizer_checkLinebreakBefore_parenthesizer___redArg(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkLinebreakBefore_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Parenthesizer_checkLinebreakBefore_parenthesizer(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkTailWs_parenthesizer___redArg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkTailWs_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Parenthesizer_checkTailWs_parenthesizer___redArg(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkTailWs_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Parenthesizer_checkTailWs_parenthesizer(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkColEq_parenthesizer___redArg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkColEq_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Parenthesizer_checkColEq_parenthesizer___redArg(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkColEq_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Parenthesizer_checkColEq_parenthesizer(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkColGe_parenthesizer___redArg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkColGe_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Parenthesizer_checkColGe_parenthesizer___redArg(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkColGe_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Parenthesizer_checkColGe_parenthesizer(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkColGt_parenthesizer___redArg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkColGt_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Parenthesizer_checkColGt_parenthesizer___redArg(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkColGt_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Parenthesizer_checkColGt_parenthesizer(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkLineEq_parenthesizer___redArg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkLineEq_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Parenthesizer_checkLineEq_parenthesizer___redArg(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkLineEq_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Parenthesizer_checkLineEq_parenthesizer(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_eoi_parenthesizer___redArg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_eoi_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Parenthesizer_eoi_parenthesizer___redArg(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_eoi_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Parenthesizer_eoi_parenthesizer(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkNoImmediateColon_parenthesizer___redArg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkNoImmediateColon_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Parenthesizer_checkNoImmediateColon_parenthesizer___redArg(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkNoImmediateColon_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Parenthesizer_checkNoImmediateColon_parenthesizer(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_skip_parenthesizer___redArg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_skip_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Parenthesizer_skip_parenthesizer___redArg(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_skip_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Parenthesizer_skip_parenthesizer(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_pushNone_parenthesizer___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_MonadTraverser_goLeft___at___Lean_PrettyPrinter_Parenthesizer_visitArgs_spec__1___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_pushNone_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Syntax_MonadTraverser_goLeft___at___Lean_PrettyPrinter_Parenthesizer_visitArgs_spec__1___redArg(x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_pushNone_parenthesizer___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PrettyPrinter_Parenthesizer_pushNone_parenthesizer___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_pushNone_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Parenthesizer_pushNone_parenthesizer(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_hygieneInfoNoAntiquot_parenthesizer___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_MonadTraverser_goLeft___at___Lean_PrettyPrinter_Parenthesizer_visitArgs_spec__1___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_hygieneInfoNoAntiquot_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Syntax_MonadTraverser_goLeft___at___Lean_PrettyPrinter_Parenthesizer_visitArgs_spec__1___redArg(x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_hygieneInfoNoAntiquot_parenthesizer___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PrettyPrinter_Parenthesizer_hygieneInfoNoAntiquot_parenthesizer___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_hygieneInfoNoAntiquot_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Parenthesizer_hygieneInfoNoAntiquot_parenthesizer(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_PrettyPrinter_Parenthesizer_interpolatedStr_parenthesizer_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_19; 
x_19 = lean_usize_dec_eq(x_3, x_4);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
lean_dec(x_5);
x_20 = lean_array_uget(x_2, x_3);
x_21 = lean_mk_string_unchecked("interpolatedStrLitKind", 22, 22);
x_22 = l_Lean_Name_mkStr1(x_21);
x_23 = l_Lean_Syntax_isOfKind(x_20, x_22);
lean_dec(x_22);
if (x_23 == 0)
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
lean_object* x_25; 
x_25 = l_Lean_Syntax_MonadTraverser_goLeft___at___Lean_PrettyPrinter_Parenthesizer_visitArgs_spec__1___redArg(x_7, x_10);
x_11 = x_25;
goto block_18;
}
}
else
{
lean_object* x_26; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_5);
lean_ctor_set(x_26, 1, x_10);
return x_26;
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_interpolatedStr_parenthesizer___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_17 = l_Array_foldlMUnsafe_fold___at___Lean_PrettyPrinter_Parenthesizer_interpolatedStr_parenthesizer_spec__0(x_3, x_4, x_15, x_16, x_10, x_5, x_6, x_7, x_8, x_9);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_interpolatedStr_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = l_Lean_Syntax_MonadTraverser_getCur___at___Lean_PrettyPrinter_Parenthesizer_visitArgs_spec__2___redArg(x_3, x_6);
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
x_14 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_interpolatedStr_parenthesizer___lam__0___boxed), 9, 4);
lean_closure_set(x_14, 0, x_12);
lean_closure_set(x_14, 1, x_13);
lean_closure_set(x_14, 2, x_1);
lean_closure_set(x_14, 3, x_11);
x_15 = l_Lean_PrettyPrinter_Parenthesizer_visitArgs(x_14, x_2, x_3, x_4, x_5, x_9);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_PrettyPrinter_Parenthesizer_interpolatedStr_parenthesizer_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_foldlMUnsafe_fold___at___Lean_PrettyPrinter_Parenthesizer_interpolatedStr_parenthesizer_spec__0(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_interpolatedStr_parenthesizer___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_PrettyPrinter_Parenthesizer_interpolatedStr_parenthesizer___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_4416_(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_registerAlias(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_PrettyPrinter_Parenthesizer_parenthesizerAliasesRef;
x_5 = l_Lean_Parser_registerAliasCore(lean_box(0), x_4, x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_instCoeParenthesizerAliasValue___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_instCoeParenthesizerAliasValue() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_instCoeParenthesizerAliasValue___lam__0), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_instCoeForallParenthesizerAliasValue___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_instCoeForallParenthesizerAliasValue() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_instCoeForallParenthesizerAliasValue___lam__0), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_instCoeForallForallParenthesizerAliasValue___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_instCoeForallForallParenthesizerAliasValue() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_instCoeForallForallParenthesizerAliasValue___lam__0), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_PrettyPrinter_parenthesize_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_parenthesize(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_59 = lean_mk_string_unchecked("PrettyPrinter", 13, 13);
x_60 = lean_mk_string_unchecked("parenthesize", 12, 12);
x_61 = lean_mk_string_unchecked("input", 5, 5);
x_62 = l_Lean_Name_mkStr3(x_59, x_60, x_61);
lean_inc(x_62);
x_63 = l_Lean_isTracingEnabledFor___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20_spec__20___redArg(x_62, x_3, x_5);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_unbox(x_64);
lean_dec(x_64);
if (x_65 == 0)
{
lean_object* x_66; 
lean_dec(x_62);
x_66 = lean_ctor_get(x_63, 1);
lean_inc(x_66);
lean_dec(x_63);
x_19 = x_3;
x_20 = x_4;
x_21 = x_66;
goto block_58;
}
else
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_63);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_68 = lean_ctor_get(x_63, 1);
x_69 = lean_ctor_get(x_63, 0);
lean_dec(x_69);
x_70 = lean_mk_string_unchecked("", 0, 0);
x_71 = l_Lean_stringToMessageData(x_70);
lean_dec(x_70);
x_72 = lean_box(0);
x_73 = lean_box(0);
x_74 = lean_unbox(x_73);
lean_inc(x_2);
x_75 = l_Lean_Syntax_formatStx(x_2, x_72, x_74);
x_76 = l_Lean_MessageData_ofFormat(x_75);
lean_inc(x_71);
lean_ctor_set_tag(x_63, 7);
lean_ctor_set(x_63, 1, x_76);
lean_ctor_set(x_63, 0, x_71);
x_77 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_77, 0, x_63);
lean_ctor_set(x_77, 1, x_71);
x_78 = l_Lean_addTrace___at___Lean_PrettyPrinter_parenthesize_spec__0(x_62, x_77, x_3, x_4, x_68);
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
lean_dec(x_78);
x_19 = x_3;
x_20 = x_4;
x_21 = x_79;
goto block_58;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_80 = lean_ctor_get(x_63, 1);
lean_inc(x_80);
lean_dec(x_63);
x_81 = lean_mk_string_unchecked("", 0, 0);
x_82 = l_Lean_stringToMessageData(x_81);
lean_dec(x_81);
x_83 = lean_box(0);
x_84 = lean_box(0);
x_85 = lean_unbox(x_84);
lean_inc(x_2);
x_86 = l_Lean_Syntax_formatStx(x_2, x_83, x_85);
x_87 = l_Lean_MessageData_ofFormat(x_86);
lean_inc(x_82);
x_88 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_88, 0, x_82);
lean_ctor_set(x_88, 1, x_87);
x_89 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_82);
x_90 = l_Lean_addTrace___at___Lean_PrettyPrinter_parenthesize_spec__0(x_62, x_89, x_3, x_4, x_80);
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
lean_dec(x_90);
x_19 = x_3;
x_20 = x_4;
x_21 = x_91;
goto block_58;
}
}
block_18:
{
if (x_12 == 0)
{
if (lean_obj_tag(x_6) == 0)
{
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_10;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_6, 0);
lean_inc(x_13);
lean_dec(x_6);
x_14 = l___private_Lean_InternalExceptionId_0__Lean_beqInternalExceptionId____x40_Lean_InternalExceptionId___hyg_26_(x_9, x_13);
lean_dec(x_13);
lean_dec(x_9);
if (x_14 == 0)
{
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_10);
x_15 = lean_mk_string_unchecked("parenthesize: uncaught backtrack exception", 42, 42);
x_16 = l_Lean_stringToMessageData(x_15);
lean_dec(x_15);
x_17 = l_Lean_throwError___at___Lean_throwUnknownIdentifier___at___Lean_throwUnknownConstant___at___Lean_filterFieldList___at___Lean_realizeGlobalConstCore_spec__0_spec__2_spec__2_spec__2___redArg(x_16, x_11, x_8, x_7);
lean_dec(x_8);
lean_dec(x_11);
return x_17;
}
}
}
else
{
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_10;
}
}
block_58:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; 
x_22 = lean_box(0);
x_23 = l_Lean_Syntax_Traverser_fromSyntax(x_2);
x_24 = lean_box(0);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_24);
lean_ctor_set(x_26, 2, x_22);
lean_ctor_set(x_26, 3, x_24);
lean_ctor_set(x_26, 4, x_24);
lean_ctor_set(x_26, 5, x_22);
x_27 = lean_unbox(x_25);
lean_ctor_set_uint8(x_26, sizeof(void*)*6, x_27);
x_28 = lean_st_mk_ref(x_26, x_21);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_ctor_get(x_19, 2);
lean_inc(x_31);
x_32 = l_Lean_getPPParens(x_31);
lean_dec(x_31);
x_33 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_33, 0, x_22);
lean_ctor_set_uint8(x_33, sizeof(void*)*1, x_32);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_29);
x_34 = lean_apply_5(x_1, x_33, x_29, x_19, x_20, x_30);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
lean_dec(x_20);
lean_dec(x_19);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_st_ref_get(x_29, x_35);
lean_dec(x_29);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_36, 0);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec(x_39);
lean_ctor_set(x_36, 0, x_40);
return x_36;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_41 = lean_ctor_get(x_36, 0);
x_42 = lean_ctor_get(x_36, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_36);
x_43 = lean_ctor_get(x_41, 0);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec(x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_42);
return x_45;
}
}
else
{
uint8_t x_46; 
lean_dec(x_29);
x_46 = !lean_is_exclusive(x_34);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_47 = lean_ctor_get(x_34, 0);
x_48 = lean_ctor_get(x_34, 1);
x_49 = l_Lean_PrettyPrinter_backtrackExceptionId;
lean_inc(x_48);
lean_inc(x_47);
x_50 = l_Lean_Exception_isInterrupt(x_47);
if (x_50 == 0)
{
uint8_t x_51; 
x_51 = l_Lean_Exception_isRuntime(x_47);
x_6 = x_47;
x_7 = x_48;
x_8 = x_20;
x_9 = x_49;
x_10 = x_34;
x_11 = x_19;
x_12 = x_51;
goto block_18;
}
else
{
x_6 = x_47;
x_7 = x_48;
x_8 = x_20;
x_9 = x_49;
x_10 = x_34;
x_11 = x_19;
x_12 = x_50;
goto block_18;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_52 = lean_ctor_get(x_34, 0);
x_53 = lean_ctor_get(x_34, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_34);
x_54 = l_Lean_PrettyPrinter_backtrackExceptionId;
lean_inc(x_53);
lean_inc(x_52);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_52);
lean_ctor_set(x_55, 1, x_53);
x_56 = l_Lean_Exception_isInterrupt(x_52);
if (x_56 == 0)
{
uint8_t x_57; 
x_57 = l_Lean_Exception_isRuntime(x_52);
x_6 = x_52;
x_7 = x_53;
x_8 = x_20;
x_9 = x_54;
x_10 = x_55;
x_11 = x_19;
x_12 = x_57;
goto block_18;
}
else
{
x_6 = x_52;
x_7 = x_53;
x_8 = x_20;
x_9 = x_54;
x_10 = x_55;
x_11 = x_19;
x_12 = x_56;
goto block_18;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_PrettyPrinter_parenthesize_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_addTrace___at___Lean_PrettyPrinter_parenthesize_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_parenthesizeCategory(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer), 7, 2);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_6);
x_8 = l_Lean_PrettyPrinter_parenthesize(x_7, x_2, x_3, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_parenthesizeTerm(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_mk_string_unchecked("term", 4, 4);
x_6 = l_Lean_Name_mkStr1(x_5);
x_7 = l_Lean_PrettyPrinter_parenthesizeCategory(x_6, x_1, x_2, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_parenthesizeTactic(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_mk_string_unchecked("tactic", 6, 6);
x_6 = l_Lean_Name_mkStr1(x_5);
x_7 = l_Lean_PrettyPrinter_parenthesizeCategory(x_6, x_1, x_2, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_parenthesizeCommand(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_mk_string_unchecked("command", 7, 7);
x_6 = l_Lean_Name_mkStr1(x_5);
x_7 = l_Lean_PrettyPrinter_parenthesizeCategory(x_6, x_1, x_2, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_4746_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_2 = lean_mk_string_unchecked("PrettyPrinter", 13, 13);
x_3 = lean_mk_string_unchecked("parenthesize", 12, 12);
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
x_16 = lean_mk_string_unchecked("Parenthesizer", 13, 13);
x_17 = l_Lean_Name_str___override(x_15, x_16);
x_18 = lean_mk_string_unchecked("_hyg", 4, 4);
x_19 = l_Lean_Name_str___override(x_17, x_18);
x_20 = lean_unsigned_to_nat(4746u);
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
lean_object* initialize_Lean_Parser_Extension(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Parser_StrInterpolation(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_ParserCompiler_Attribute(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_PrettyPrinter_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_PrettyPrinter_Delaborator_Options(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_PrettyPrinter_Parenthesizer(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Parser_Extension(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_StrInterpolation(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ParserCompiler_Attribute(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_PrettyPrinter_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_PrettyPrinter_Delaborator_Options(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
if (builtin) {res = l_Lean_PrettyPrinter_mkParenthesizerAttribute(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_PrettyPrinter_parenthesizerAttribute = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_PrettyPrinter_parenthesizerAttribute);
lean_dec_ref(res);
}if (builtin) {res = l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_PrettyPrinter_categoryParenthesizerAttribute = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_PrettyPrinter_categoryParenthesizerAttribute);
lean_dec_ref(res);
}if (builtin) {res = l_Lean_PrettyPrinter_mkCombinatorParenthesizerAttribute(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_PrettyPrinter_combinatorParenthesizerAttribute = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_PrettyPrinter_combinatorParenthesizerAttribute);
lean_dec_ref(res);
}l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM = _init_l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM);
l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM = _init_l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM);
if (builtin) {res = l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_rawStx_parenthesizer__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_4416_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_PrettyPrinter_Parenthesizer_parenthesizerAliasesRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_parenthesizerAliasesRef);
lean_dec_ref(res);
}l_Lean_PrettyPrinter_Parenthesizer_instCoeParenthesizerAliasValue = _init_l_Lean_PrettyPrinter_Parenthesizer_instCoeParenthesizerAliasValue();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_instCoeParenthesizerAliasValue);
l_Lean_PrettyPrinter_Parenthesizer_instCoeForallParenthesizerAliasValue = _init_l_Lean_PrettyPrinter_Parenthesizer_instCoeForallParenthesizerAliasValue();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_instCoeForallParenthesizerAliasValue);
l_Lean_PrettyPrinter_Parenthesizer_instCoeForallForallParenthesizerAliasValue = _init_l_Lean_PrettyPrinter_Parenthesizer_instCoeForallForallParenthesizerAliasValue();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_instCoeForallForallParenthesizerAliasValue);
if (builtin) {res = l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_4746_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
