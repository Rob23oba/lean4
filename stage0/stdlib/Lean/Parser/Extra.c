// Lean compiler output
// Module: Lean.Parser.Extra
// Imports: Lean.Parser.Extension Lean.PrettyPrinter.Parenthesizer Lean.PrettyPrinter.Formatter
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
LEAN_EXPORT lean_object* l_Lean_Parser_sepByIndent_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_many1_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_antiquotNestedExpr_parenthesizer___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_setLhsPrec_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppHardSpace_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_withAntiquotSuffixSplice_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_checkColEq(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot_parenthesizer___lam__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_rawIdent_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Lean_Parser_sepByIndent_formatter_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkNameLit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_charLit_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_identWithPartialTrailingDot;
LEAN_EXPORT lean_object* l_Lean_Parser_dbgTraceState_formatter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppHardLineUnlessUngrouped;
LEAN_EXPORT lean_object* l_Lean_Parser_optional_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_ppDedent_docString__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppHardSpace_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepByIndent_formatter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_pushNone;
LEAN_EXPORT lean_object* l_Lean_Parser_rawIdent_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ppSpace_formatter___redArg___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_nameLitNoAntiquot;
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withCache_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppRealGroup_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_adaptCacheableContext_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Lean_Parser_sepByIndent_formatter_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppRealGroup___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_dbgTraceState_parenthesizer___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_orelse_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy_formatter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ppLine_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_fill(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_rawIdentNoAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_ppHardSpace_docString__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_manyIndent(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot_parenthesizer(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_adaptCacheableContext_parenthesizer___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth_parenthesizer___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppRealFill___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_setExpected_formatter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getString(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkPrec_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ppHardLineUnlessUngrouped_formatter___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_many_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_charLit_docString__1(lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_dbgTraceState_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_ppGroup_docString__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ppSpace_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepByIndent_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_termParser_formatter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_group_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_ident_docString__1(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_sepByNoAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_notSymbol(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1Indent_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ppHardLineUnlessUngrouped_formatter___redArg(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_PrettyPrinter_Formatter_pushWhitespace___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot_parenthesizer___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ppHardLineUnlessUngrouped_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepByElemParser_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_ppIndent_docString__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_optional(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_termParser_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nameLit_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_hygieneInfo_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_initFn___lam__0____x40_Lean_Parser_Extra___hyg_1755____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppDedent_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_termRegister__parser__alias_x28Kind_x3a_x3d___x29____________;
LEAN_EXPORT lean_object* l_Lean_Parser_evalInsideQuot_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_strLit;
LEAN_EXPORT lean_object* l_Lean_Parser_adaptCacheableContext_formatter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppLine_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppDedent___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepByElemParser_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withOpen_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_checkLinebreakBefore(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withOpenDecl_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withPositionAfterLinebreak_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_incQuotDepth_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_scientificLit_docString__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1_formatter(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkNoWsBefore_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_initFn___lam__7____x40_Lean_Parser_Extra___hyg_1755_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_orelse(lean_object*, lean_object*);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Parser_decQuotDepth_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_hygieneInfo;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkColEq_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot_parenthesizer___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotSpliceAndSuffix_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withForbidden_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_ppRealGroup_docString__1(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppAllowUngrouped_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_tokenWithAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ppHardSpace_formatter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_ppHardLineUnlessUngrouped_docString__1(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_charLitNoAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot_formatter___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withCache_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppLine_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_hygieneInfo_formatter___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser___aux__Lean__Parser__Extra______macroRules__Lean__Parser__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepByIndent_parenthesizer(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth_formatter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_antiquotNestedExpr_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy_formatter(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_InternalExceptionId_0__Lean_beqInternalExceptionId____x40_Lean_InternalExceptionId___hyg_26_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy_parenthesizer(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepByIndent_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_skip_parenthesizer___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_setExpected_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withCache_formatter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ppLine_formatter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_nameLit_docString__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withCache_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_group(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_ppDedentIfGrouped_docString__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppAllowUngrouped_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_notSymbol_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppGroup(lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkNoWsBefore_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_evalInsideQuot_formatter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_strLit_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_notSymbol_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Macro_resolveGlobalName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_withPosition(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_leadingNode_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nodeWithAntiquot_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_hygieneInfoNoAntiquot;
lean_object* l_Lean_Parser_optionalNoAntiquot(lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_setExpected_parenthesizer___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ident_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_Parser_sepByIndent_formatter_spec__2(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Parser_initFn___lam__6____x40_Lean_Parser_Extra___hyg_1755_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_setExpected_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_commandParser_formatter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_many1_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_commandParser_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_commandParser_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withoutPosition_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppRealFill_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_charLitNoAntiquot;
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Parser_initFn___lam__0____x40_Lean_Parser_Extra___hyg_1755_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_many1Indent_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_visitArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot_formatter___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ppAllowUngrouped_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_manyNoAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ppRealGroup_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepByElemParser_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_initFn___lam__2____x40_Lean_Parser_Extra___hyg_1755____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withOpen_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepByIndent_formatter___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkColGe_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_range(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbol_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_sepByNoAntiquot_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_PrettyPrinter_parenthesizerAttribute;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_identWithPartialTrailingDot_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot_parenthesizer___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_numLit_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbol_formatter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_rawIdentNoAntiquot;
LEAN_EXPORT lean_object* l_Lean_ppHardSpace_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Parser_sepByIndent_formatter_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_quoteNameMk(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ppHardSpace_formatter___redArg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___Lean_PrettyPrinter_Formatter_visitArgs_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_manyIndent_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ppLine_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepByIndent_formatter___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ppSpace_formatter___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_nameLitNoAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_registerAlias(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppHardLineUnlessUngrouped_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_sepBy1(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Parser_notFollowedBy(lean_object*, lean_object*);
lean_object* l_Lean_Parser_symbol(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1Indent_parenthesizer(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withForbidden_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_antiquotNestedExpr_formatter___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppHardLineUnlessUngrouped_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ppDedentIfGrouped_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppGroup___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_notFollowedBy_formatter___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_symbol_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withResetCache_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkLinebreakBefore_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppSpace;
lean_object* l_Lean_PrettyPrinter_Formatter_optionalNoAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nameLit_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nameLit;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_suppressInsideQuot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_checkNoWsBefore(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_hygieneInfo_formatter___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_symbol_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_withAntiquot(lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_withPosition_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ppAllowUngrouped_formatter___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Macro_throwError___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_pushAlign___redArg(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_pushLine___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_antiquotExpr_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkNoImmediateColon_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_initFn___lam__2____x40_Lean_Parser_Extra___hyg_1755_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppAllowUngrouped;
LEAN_EXPORT lean_object* l_Lean_Parser_withForbidden_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_scientificLit_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_suppressInsideQuot_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_many1_docString__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_many_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withResetCache_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbol_parenthesizer(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot_formatter___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotSpliceAndSuffix_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ppAllowUngrouped_formatter___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotSpliceAndSuffix_parenthesizer___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_adaptCacheableContext_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_antiquotNestedExpr_parenthesizer__1(lean_object*);
lean_object* l_Lean_Parser_many1NoAntiquot(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_charLit_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_node(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppLine_parenthesizer___redArg(lean_object*);
extern lean_object* l_Lean_Parser_numLitNoAntiquot;
LEAN_EXPORT lean_object* l_Lean_Parser_withForbidden_formatter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_hygieneInfo_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1Indent___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_group_docString__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbol_parenthesizer___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ppHardSpace_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_andthen(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppHardSpace;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_manyNoAntiquot_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_symbol_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy_parenthesizer___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withForbidden_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_strLit_docString__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_setExpected_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_checkColGe(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbol_parenthesizer___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_evalInsideQuot_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppSpace_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ident_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_charLit;
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppRealFill(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nodeWithAntiquot_parenthesizer(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_rawIdent;
LEAN_EXPORT lean_object* l_Lean_Parser_evalInsideQuot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_symbol_parenthesizer___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppIndent(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_commandParser_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_hygieneInfo_docString__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbol_formatter___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_scientificLit;
LEAN_EXPORT lean_object* l_Lean_Parser_many(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_1755_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1_parenthesizer___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ppDedent_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_pushNone_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1Indent_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppLine;
LEAN_EXPORT lean_object* l_Lean_ppSpace_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_antiquotNestedExpr_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppHardSpace_parenthesizer___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot_parenthesizer___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_initFn___lam__7____x40_Lean_Parser_Extra___hyg_1755____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_initFn___lam__3____x40_Lean_Parser_Extra___hyg_1755_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_manyIndent_docString__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1Indent_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withPosition_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_leadingNode_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_adaptCacheableContext_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_patternIgnore_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_termParser_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ident;
LEAN_EXPORT lean_object* l_Lean_Parser_optional_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbol_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_scientificLitNoAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_many1Indent(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_group(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_manyIndent_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_many1Indent_docString__1(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Lean_Parser_sepByIndent_formatter_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withoutForbidden_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_visitArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_dbgTraceState_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withCache_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepByElemParser_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_evalInsideQuot_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkNoImmediateColon_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_atomic_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppGroup_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_withAntiquotSpliceAndSuffix(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1Indent_formatter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_evalInsideQuot_parenthesizer___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Parser_sepByIndent_formatter_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_skip;
LEAN_EXPORT lean_object* l_Lean_Parser_decQuotDepth_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppIndent_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ppHardLineUnlessUngrouped_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotSpliceAndSuffix_formatter___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withoutPosition_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_scientificLitNoAntiquot;
LEAN_EXPORT lean_object* l_Lean_Parser_notSymbol_formatter___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbol_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_identWithPartialTrailingDot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_strLitNoAntiquot;
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_registerAlias(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1Indent(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Parser_patternIgnore(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_dbgTraceState_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Parser_sepByIndent_formatter_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppSpace_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_many1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_initFn___lam__8____x40_Lean_Parser_Extra___hyg_1755_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_antiquotExpr_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Std_Format_getIndent(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquotSplice_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withCache_parenthesizer___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_PrettyPrinter_backtrackExceptionId;
LEAN_EXPORT lean_object* l_Lean_Parser_termParser_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppRealGroup(lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___Lean_PrettyPrinter_Formatter_visitArgs_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_andthen_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_setExpected_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppDedent(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_indent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot_formatter___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkColGe_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_numLit_docString__1(lean_object*);
lean_object* l_Lean_Parser_sepBy(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PrettyPrinter_Formatter_strLitNoAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_identNoAntiquot;
LEAN_EXPORT lean_object* l_Lean_Parser_leadingNode_formatter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_withAntiquotSuffixSplice_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppAllowUngrouped_parenthesizer___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_many1Indent_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquotSplice_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_ppAllowUngrouped_docString__1(lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_tokenWithAntiquot_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Parser_sepByIndent(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Parser_ppDedentIfGrouped(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ppRealFill_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkAntiquot(lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_identNoAntiquot_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nodeWithAntiquot_formatter(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nodeWithAntiquot_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_incQuotDepth_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_symbol_parenthesizer___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_numLit;
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot_formatter(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppIndent___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_initFn___lam__5____x40_Lean_Parser_Extra___hyg_1755_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_PrettyPrinter_formatterAttribute;
LEAN_EXPORT lean_object* l_Lean_ppIndent_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Parser_sepByIndent_formatter_spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_strLit_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___Lean_PrettyPrinter_Parenthesizer_visitArgs_spec__1___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_notFollowedBy_parenthesizer___redArg(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbol_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_symbol_parenthesizer___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_group_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Lean_Parser_sepByIndent_formatter_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_numLit_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_ppLine_docString__1(lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_many_docString__1(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_categoryParser_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withOpenDecl_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_manyNoAntiquot(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_optional_docString__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ppLine_formatter___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1_parenthesizer(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_notSymbol_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ppAllowUngrouped_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppDedentIfGrouped_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_unicodeSymbolNoAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1_formatter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppHardLineUnlessUngrouped_parenthesizer___redArg(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepByIndent___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_ppSpace_docString__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_patternIgnore_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_notSymbol_parenthesizer___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppSpace_parenthesizer___redArg(lean_object*);
lean_object* l_String_toSubstring_x27(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withoutForbidden_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_dbgTraceState_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withForbidden_parenthesizer___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_concat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_patternIgnore_docString__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbol_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppDedentIfGrouped___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_adaptCacheableContext_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_notSymbol_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_numLitNoAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_ppRealFill_docString__1(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_scientificLit_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Parser_sepByIndent_formatter_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ppGroup_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_node_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbol_formatter(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_registerAlias(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot_parenthesizer___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_leadingNode_formatter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkPrec_formatter___boxed), 5, 0);
x_9 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_node_formatter), 7, 2);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_2);
x_10 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_setLhsPrec_formatter___boxed), 5, 0);
x_11 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_11, 0, x_9);
lean_closure_set(x_11, 1, x_10);
x_12 = l_Lean_PrettyPrinter_Formatter_andthen_formatter(x_8, x_11, x_3, x_4, x_5, x_6, x_7);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_leadingNode_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Parser_leadingNode_formatter___redArg(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_leadingNode_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Parser_leadingNode_formatter(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_termParser_formatter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_mk_string_unchecked("term", 4, 4);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = l_Lean_PrettyPrinter_Formatter_categoryParser_formatter(x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_termParser_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_termParser_formatter___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_termParser_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_termParser_formatter(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_termParser_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_mk_string_unchecked("term", 4, 4);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer(x_8, x_1, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_commandParser_formatter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_mk_string_unchecked("command", 7, 7);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = l_Lean_PrettyPrinter_Formatter_categoryParser_formatter(x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_commandParser_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_commandParser_formatter___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_commandParser_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_commandParser_formatter(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_commandParser_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_mk_string_unchecked("command", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer(x_8, x_1, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_atomic_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_setExpected_formatter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_setExpected_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_apply_5(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_setExpected_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Parser_setExpected_formatter(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_symbol_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter), 6, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = l_Lean_PrettyPrinter_Formatter_tokenWithAntiquot_formatter(x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_adaptCacheableContext_formatter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_adaptCacheableContext_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_apply_5(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_adaptCacheableContext_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Parser_adaptCacheableContext_formatter(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth_formatter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_apply_5(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth_formatter(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_decQuotDepth_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_antiquotNestedExpr_formatter___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_termParser_formatter___redArg(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_antiquotNestedExpr_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_antiquotNestedExpr_formatter___lam__0), 5, 0);
x_7 = lean_mk_string_unchecked("antiquotNestedExpr", 18, 18);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("(", 1, 1);
x_10 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter), 6, 1);
lean_closure_set(x_10, 0, x_9);
x_11 = lean_mk_string_unchecked(")", 1, 1);
x_12 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter), 6, 1);
lean_closure_set(x_12, 0, x_11);
x_13 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_13, 0, x_6);
lean_closure_set(x_13, 1, x_12);
x_14 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_14, 0, x_10);
lean_closure_set(x_14, 1, x_13);
x_15 = l_Lean_PrettyPrinter_Formatter_node_formatter(x_8, x_14, x_1, x_2, x_3, x_4, x_5);
return x_15;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_2 = l_Lean_PrettyPrinter_formatterAttribute;
x_3 = lean_mk_string_unchecked("antiquotNestedExpr", 18, 18);
lean_inc(x_3);
x_4 = l_Lean_Name_mkStr1(x_3);
x_5 = lean_mk_string_unchecked("Lean", 4, 4);
x_6 = lean_mk_string_unchecked("Parser", 6, 6);
x_7 = lean_mk_string_unchecked("formatter", 9, 9);
x_8 = l_Lean_Name_mkStr4(x_5, x_6, x_3, x_7);
x_9 = lean_alloc_closure((void*)(l_Lean_Parser_antiquotNestedExpr_formatter), 5, 0);
x_10 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_4, x_8, x_9, x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_antiquotExpr_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter), 5, 0);
x_7 = lean_mk_string_unchecked("_", 1, 1);
x_8 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter), 6, 1);
lean_closure_set(x_8, 0, x_7);
x_9 = lean_alloc_closure((void*)(l_Lean_Parser_antiquotNestedExpr_formatter), 5, 0);
x_10 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter), 7, 2);
lean_closure_set(x_10, 0, x_8);
lean_closure_set(x_10, 1, x_9);
x_11 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_6, x_10, x_1, x_2, x_3, x_4, x_5);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbol_formatter___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbol_formatter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_closure((void*)(l_Lean_Parser_nonReservedSymbol_formatter___redArg___lam__0), 6, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = l_Lean_PrettyPrinter_Formatter_tokenWithAntiquot_formatter(x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbol_formatter(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Parser_nonReservedSymbol_formatter___redArg(x_1, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbol_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Lean_Parser_nonReservedSymbol_formatter(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot_formatter___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_symbol_formatter(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot_formatter___lam__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (x_1 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_9 = lean_mk_string_unchecked("antiquotName", 12, 12);
x_10 = l_Lean_Name_mkStr1(x_9);
x_11 = lean_mk_string_unchecked(":", 1, 1);
x_12 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter), 6, 1);
lean_closure_set(x_12, 0, x_11);
x_13 = lean_box(x_1);
x_14 = lean_alloc_closure((void*)(l_Lean_Parser_nonReservedSymbol_formatter___boxed), 7, 2);
lean_closure_set(x_14, 0, x_2);
lean_closure_set(x_14, 1, x_13);
x_15 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_15, 0, x_12);
lean_closure_set(x_15, 1, x_14);
x_16 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_16, 0, x_3);
lean_closure_set(x_16, 1, x_15);
x_17 = l_Lean_PrettyPrinter_Formatter_node_formatter(x_10, x_16, x_4, x_5, x_6, x_7, x_8);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_18 = lean_mk_string_unchecked("antiquotName", 12, 12);
x_19 = l_Lean_Name_mkStr1(x_18);
x_20 = lean_mk_string_unchecked(":", 1, 1);
x_21 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter), 6, 1);
lean_closure_set(x_21, 0, x_20);
x_22 = lean_box(0);
x_23 = lean_alloc_closure((void*)(l_Lean_Parser_nonReservedSymbol_formatter___boxed), 7, 2);
lean_closure_set(x_23, 0, x_2);
lean_closure_set(x_23, 1, x_22);
x_24 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_24, 0, x_21);
lean_closure_set(x_24, 1, x_23);
x_25 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_25, 0, x_3);
lean_closure_set(x_25, 1, x_24);
x_26 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_node_formatter), 7, 2);
lean_closure_set(x_26, 0, x_19);
lean_closure_set(x_26, 1, x_25);
x_27 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkNoImmediateColon_formatter___boxed), 5, 0);
x_28 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_pushNone_formatter___boxed), 5, 0);
x_29 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_29, 0, x_27);
lean_closure_set(x_29, 1, x_28);
x_30 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_26, x_29, x_4, x_5, x_6, x_7, x_8);
return x_30;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot_formatter___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Formatter_andthen_formatter(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot_formatter(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
if (x_4 == 0)
{
lean_object* x_30; 
x_30 = lean_box(0);
x_10 = x_30;
goto block_29;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_mk_string_unchecked("pseudo", 6, 6);
x_32 = l_Lean_Name_mkStr1(x_31);
x_10 = x_32;
goto block_29;
}
block_29:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_11 = l_Lean_Name_append(x_2, x_10);
x_12 = lean_mk_string_unchecked("antiquot", 8, 8);
x_13 = l_Lean_Name_mkStr1(x_12);
x_14 = l_Lean_Name_append(x_11, x_13);
x_15 = lean_mk_string_unchecked("$", 1, 1);
lean_inc(x_15);
x_16 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___lam__0), 6, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter), 6, 1);
lean_closure_set(x_17, 0, x_15);
x_18 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkNoWsBefore_formatter___boxed), 5, 0);
x_19 = lean_box(x_3);
lean_inc(x_18);
x_20 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___lam__1___boxed), 8, 3);
lean_closure_set(x_20, 0, x_19);
lean_closure_set(x_20, 1, x_1);
lean_closure_set(x_20, 2, x_18);
lean_inc(x_18);
x_21 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_21, 0, x_18);
lean_closure_set(x_21, 1, x_17);
x_22 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_manyNoAntiquot_formatter), 6, 1);
lean_closure_set(x_22, 0, x_21);
x_23 = lean_alloc_closure((void*)(l_Lean_Parser_antiquotExpr_formatter), 5, 0);
x_24 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_24, 0, x_23);
lean_closure_set(x_24, 1, x_20);
x_25 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_25, 0, x_18);
lean_closure_set(x_25, 1, x_24);
x_26 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_26, 0, x_22);
lean_closure_set(x_26, 1, x_25);
x_27 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___lam__2), 7, 2);
lean_closure_set(x_27, 0, x_16);
lean_closure_set(x_27, 1, x_26);
x_28 = l_Lean_Parser_leadingNode_formatter___redArg(x_14, x_27, x_5, x_6, x_7, x_8, x_9);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot_formatter___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = l_Lean_Parser_mkAntiquot_formatter___lam__1(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = l_Lean_Parser_mkAntiquot_formatter(x_1, x_2, x_10, x_11, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_setExpected_parenthesizer___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_setExpected_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_apply_5(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_setExpected_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Parser_setExpected_parenthesizer(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_symbol_parenthesizer___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_symbol_parenthesizer___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___redArg___lam__0___boxed), 5, 0);
x_7 = l_Lean_PrettyPrinter_Parenthesizer_tokenWithAntiquot_parenthesizer(x_6, x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_symbol_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_symbol_parenthesizer___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_symbol_parenthesizer___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_symbol_parenthesizer___redArg___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_symbol_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_symbol_parenthesizer(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_adaptCacheableContext_parenthesizer___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_adaptCacheableContext_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_apply_5(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_adaptCacheableContext_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Parser_adaptCacheableContext_parenthesizer(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth_parenthesizer___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_apply_5(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth_parenthesizer(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_decQuotDepth_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_antiquotNestedExpr_parenthesizer___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_termParser_parenthesizer(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_antiquotNestedExpr_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___redArg___lam__0___boxed), 5, 0);
x_7 = lean_mk_string_unchecked("antiquotNestedExpr", 18, 18);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_antiquotNestedExpr_parenthesizer___lam__2), 6, 1);
lean_closure_set(x_10, 0, x_9);
lean_inc(x_6);
x_11 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_11, 0, x_10);
lean_closure_set(x_11, 1, x_6);
x_12 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_12, 0, x_6);
lean_closure_set(x_12, 1, x_11);
x_13 = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer(x_8, x_12, x_1, x_2, x_3, x_4, x_5);
return x_13;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_antiquotNestedExpr_parenthesizer__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_3 = lean_mk_string_unchecked("antiquotNestedExpr", 18, 18);
lean_inc(x_3);
x_4 = l_Lean_Name_mkStr1(x_3);
x_5 = lean_mk_string_unchecked("Lean", 4, 4);
x_6 = lean_mk_string_unchecked("Parser", 6, 6);
x_7 = lean_mk_string_unchecked("parenthesizer", 13, 13);
x_8 = l_Lean_Name_mkStr4(x_5, x_6, x_3, x_7);
x_9 = lean_alloc_closure((void*)(l_Lean_Parser_antiquotNestedExpr_parenthesizer), 5, 0);
x_10 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_4, x_8, x_9, x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_antiquotExpr_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___redArg___lam__0___boxed), 5, 0);
x_7 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_identNoAntiquot_parenthesizer___boxed), 5, 0);
x_8 = lean_alloc_closure((void*)(l_Lean_Parser_antiquotNestedExpr_parenthesizer), 5, 0);
x_9 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer), 7, 2);
lean_closure_set(x_9, 0, x_6);
lean_closure_set(x_9, 1, x_8);
x_10 = l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(x_7, x_9, x_1, x_2, x_3, x_4, x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbol_parenthesizer___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___redArg___lam__0___boxed), 5, 0);
x_7 = l_Lean_PrettyPrinter_Parenthesizer_tokenWithAntiquot_parenthesizer(x_6, x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbol_parenthesizer(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Parser_nonReservedSymbol_parenthesizer___redArg(x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbol_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Lean_Parser_nonReservedSymbol_parenthesizer(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot_parenthesizer___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Syntax_MonadTraverser_goLeft___at___Lean_PrettyPrinter_Parenthesizer_visitArgs_spec__1___redArg(x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot_parenthesizer___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_symbol_parenthesizer___redArg(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot_parenthesizer___lam__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (x_1 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_4);
x_10 = lean_mk_string_unchecked("antiquotName", 12, 12);
x_11 = l_Lean_Name_mkStr1(x_10);
x_12 = lean_mk_string_unchecked(":", 1, 1);
x_13 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___boxed), 6, 1);
lean_closure_set(x_13, 0, x_12);
x_14 = lean_box(x_1);
x_15 = lean_alloc_closure((void*)(l_Lean_Parser_nonReservedSymbol_parenthesizer___boxed), 7, 2);
lean_closure_set(x_15, 0, x_2);
lean_closure_set(x_15, 1, x_14);
x_16 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_16, 0, x_13);
lean_closure_set(x_16, 1, x_15);
x_17 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_17, 0, x_3);
lean_closure_set(x_17, 1, x_16);
x_18 = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer(x_11, x_17, x_5, x_6, x_7, x_8, x_9);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_19 = lean_mk_string_unchecked("antiquotName", 12, 12);
x_20 = l_Lean_Name_mkStr1(x_19);
x_21 = lean_mk_string_unchecked(":", 1, 1);
x_22 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___boxed), 6, 1);
lean_closure_set(x_22, 0, x_21);
x_23 = lean_box(0);
x_24 = lean_alloc_closure((void*)(l_Lean_Parser_nonReservedSymbol_parenthesizer___boxed), 7, 2);
lean_closure_set(x_24, 0, x_2);
lean_closure_set(x_24, 1, x_23);
x_25 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_25, 0, x_22);
lean_closure_set(x_25, 1, x_24);
x_26 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_26, 0, x_3);
lean_closure_set(x_26, 1, x_25);
x_27 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer), 7, 2);
lean_closure_set(x_27, 0, x_20);
lean_closure_set(x_27, 1, x_26);
x_28 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkNoImmediateColon_parenthesizer___boxed), 5, 0);
x_29 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_29, 0, x_28);
lean_closure_set(x_29, 1, x_4);
x_30 = l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(x_27, x_29, x_5, x_6, x_7, x_8, x_9);
return x_30;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot_parenthesizer___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot_parenthesizer(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___lam__0___boxed), 5, 0);
x_11 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___lam__1), 5, 0);
if (x_4 == 0)
{
lean_object* x_32; 
x_32 = lean_box(0);
x_12 = x_32;
goto block_31;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_mk_string_unchecked("pseudo", 6, 6);
x_34 = l_Lean_Name_mkStr1(x_33);
x_12 = x_34;
goto block_31;
}
block_31:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_13 = l_Lean_Name_append(x_2, x_12);
x_14 = lean_mk_string_unchecked("antiquot", 8, 8);
x_15 = l_Lean_Name_mkStr1(x_14);
x_16 = l_Lean_Name_append(x_13, x_15);
x_17 = lean_unsigned_to_nat(1024u);
x_18 = lean_mk_string_unchecked("$", 1, 1);
x_19 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___boxed), 6, 1);
lean_closure_set(x_19, 0, x_18);
x_20 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkNoWsBefore_parenthesizer___boxed), 5, 0);
x_21 = lean_box(x_3);
lean_inc(x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___lam__2___boxed), 9, 4);
lean_closure_set(x_22, 0, x_21);
lean_closure_set(x_22, 1, x_1);
lean_closure_set(x_22, 2, x_20);
lean_closure_set(x_22, 3, x_10);
lean_inc(x_20);
x_23 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_23, 0, x_20);
lean_closure_set(x_23, 1, x_19);
x_24 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_manyNoAntiquot_parenthesizer), 6, 1);
lean_closure_set(x_24, 0, x_23);
x_25 = lean_alloc_closure((void*)(l_Lean_Parser_antiquotExpr_parenthesizer), 5, 0);
x_26 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_26, 0, x_25);
lean_closure_set(x_26, 1, x_22);
x_27 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_27, 0, x_20);
lean_closure_set(x_27, 1, x_26);
x_28 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_28, 0, x_24);
lean_closure_set(x_28, 1, x_27);
x_29 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___lam__3), 7, 2);
lean_closure_set(x_29, 0, x_11);
lean_closure_set(x_29, 1, x_28);
x_30 = l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer(x_16, x_17, x_29, x_5, x_6, x_7, x_8, x_9);
return x_30;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot_parenthesizer___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_mkAntiquot_parenthesizer___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot_parenthesizer___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_1);
lean_dec(x_1);
x_11 = l_Lean_Parser_mkAntiquot_parenthesizer___lam__2(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = l_Lean_Parser_mkAntiquot_parenthesizer(x_1, x_2, x_10, x_11, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nodeWithAntiquot_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_box(0);
x_11 = lean_box(x_4);
lean_inc(x_2);
x_12 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_2);
lean_closure_set(x_12, 2, x_11);
lean_closure_set(x_12, 3, x_10);
x_13 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_node_formatter), 7, 2);
lean_closure_set(x_13, 0, x_2);
lean_closure_set(x_13, 1, x_3);
x_14 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_12, x_13, x_5, x_6, x_7, x_8, x_9);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nodeWithAntiquot_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = l_Lean_Parser_nodeWithAntiquot_formatter(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nodeWithAntiquot_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_box(0);
x_11 = lean_box(x_4);
lean_inc(x_2);
x_12 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_2);
lean_closure_set(x_12, 2, x_11);
lean_closure_set(x_12, 3, x_10);
x_13 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer), 7, 2);
lean_closure_set(x_13, 0, x_2);
lean_closure_set(x_13, 1, x_3);
x_14 = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(x_12, x_13, x_5, x_6, x_7, x_8, x_9);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nodeWithAntiquot_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = l_Lean_Parser_nodeWithAntiquot_parenthesizer(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquotSplice_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_9 = lean_mk_string_unchecked("antiquot_scope", 14, 14);
x_10 = l_Lean_Name_mkStr1(x_9);
x_11 = l_Lean_Name_append(x_1, x_10);
x_12 = lean_mk_string_unchecked("$", 1, 1);
lean_inc(x_12);
x_13 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___lam__0), 6, 1);
lean_closure_set(x_13, 0, x_12);
x_14 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter), 6, 1);
lean_closure_set(x_14, 0, x_12);
x_15 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkNoWsBefore_formatter___boxed), 5, 0);
lean_inc(x_15);
x_16 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_16, 0, x_15);
lean_closure_set(x_16, 1, x_14);
x_17 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_manyNoAntiquot_formatter), 6, 1);
lean_closure_set(x_17, 0, x_16);
x_18 = lean_mk_string_unchecked("[", 1, 1);
x_19 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter), 6, 1);
lean_closure_set(x_19, 0, x_18);
x_20 = lean_mk_string_unchecked("null", 4, 4);
x_21 = l_Lean_Name_mkStr1(x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_node_formatter), 7, 2);
lean_closure_set(x_22, 0, x_21);
lean_closure_set(x_22, 1, x_2);
x_23 = lean_mk_string_unchecked("]", 1, 1);
x_24 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter), 6, 1);
lean_closure_set(x_24, 0, x_23);
x_25 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_25, 0, x_24);
lean_closure_set(x_25, 1, x_3);
x_26 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_26, 0, x_22);
lean_closure_set(x_26, 1, x_25);
x_27 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_27, 0, x_19);
lean_closure_set(x_27, 1, x_26);
x_28 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_28, 0, x_15);
lean_closure_set(x_28, 1, x_27);
x_29 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_29, 0, x_17);
lean_closure_set(x_29, 1, x_28);
x_30 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___lam__2), 7, 2);
lean_closure_set(x_30, 0, x_13);
lean_closure_set(x_30, 1, x_29);
x_31 = l_Lean_Parser_leadingNode_formatter___redArg(x_11, x_30, x_4, x_5, x_6, x_7, x_8);
return x_31;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotSpliceAndSuffix_formatter___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotSpliceAndSuffix_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_inc(x_2);
x_9 = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotSpliceAndSuffix_formatter___lam__0), 6, 1);
lean_closure_set(x_9, 0, x_2);
lean_inc(x_3);
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquotSplice_formatter), 8, 3);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_9);
lean_closure_set(x_10, 2, x_3);
x_11 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_withAntiquotSuffixSplice_formatter___boxed), 8, 3);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_2);
lean_closure_set(x_11, 2, x_3);
x_12 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_10, x_11, x_4, x_5, x_6, x_7, x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepByElemParser_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_8 = lean_mk_string_unchecked("sepBy", 5, 5);
x_9 = l_Lean_Name_mkStr1(x_8);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_string_utf8_byte_size(x_2);
x_12 = l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(x_2, x_11, x_10);
x_13 = l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(x_2, x_12, x_11);
x_14 = lean_string_utf8_extract(x_2, x_12, x_13);
lean_dec(x_13);
lean_dec(x_12);
x_15 = lean_mk_string_unchecked("*", 1, 1);
x_16 = lean_string_append(x_14, x_15);
lean_dec(x_15);
x_17 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter), 6, 1);
lean_closure_set(x_17, 0, x_16);
x_18 = l_Lean_Parser_withAntiquotSpliceAndSuffix_formatter(x_9, x_1, x_17, x_3, x_4, x_5, x_6, x_7);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepByElemParser_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Parser_sepByElemParser_formatter(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy_formatter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_closure((void*)(l_Lean_Parser_sepByElemParser_formatter___boxed), 7, 2);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_2);
x_10 = l_Lean_PrettyPrinter_Formatter_sepByNoAntiquot_formatter(x_9, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Parser_sepBy_formatter___redArg(x_1, x_2, x_3, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = l_Lean_Parser_sepBy_formatter(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquotSplice_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_9 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___lam__1), 5, 0);
x_10 = lean_mk_string_unchecked("antiquot_scope", 14, 14);
x_11 = l_Lean_Name_mkStr1(x_10);
x_12 = l_Lean_Name_append(x_1, x_11);
x_13 = lean_unsigned_to_nat(1024u);
x_14 = lean_mk_string_unchecked("$", 1, 1);
x_15 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___boxed), 6, 1);
lean_closure_set(x_15, 0, x_14);
x_16 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkNoWsBefore_parenthesizer___boxed), 5, 0);
lean_inc(x_16);
x_17 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_17, 0, x_16);
lean_closure_set(x_17, 1, x_15);
x_18 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_manyNoAntiquot_parenthesizer), 6, 1);
lean_closure_set(x_18, 0, x_17);
x_19 = lean_mk_string_unchecked("[", 1, 1);
x_20 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___boxed), 6, 1);
lean_closure_set(x_20, 0, x_19);
x_21 = lean_mk_string_unchecked("null", 4, 4);
x_22 = l_Lean_Name_mkStr1(x_21);
x_23 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer), 7, 2);
lean_closure_set(x_23, 0, x_22);
lean_closure_set(x_23, 1, x_2);
x_24 = lean_mk_string_unchecked("]", 1, 1);
x_25 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___boxed), 6, 1);
lean_closure_set(x_25, 0, x_24);
x_26 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_26, 0, x_25);
lean_closure_set(x_26, 1, x_3);
x_27 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_27, 0, x_23);
lean_closure_set(x_27, 1, x_26);
x_28 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_28, 0, x_20);
lean_closure_set(x_28, 1, x_27);
x_29 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_29, 0, x_16);
lean_closure_set(x_29, 1, x_28);
x_30 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_30, 0, x_18);
lean_closure_set(x_30, 1, x_29);
x_31 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___lam__3), 7, 2);
lean_closure_set(x_31, 0, x_9);
lean_closure_set(x_31, 1, x_30);
x_32 = l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer(x_12, x_13, x_31, x_4, x_5, x_6, x_7, x_8);
return x_32;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotSpliceAndSuffix_parenthesizer___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotSpliceAndSuffix_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_inc(x_2);
x_9 = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotSpliceAndSuffix_parenthesizer___lam__0), 6, 1);
lean_closure_set(x_9, 0, x_2);
lean_inc(x_3);
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquotSplice_parenthesizer), 8, 3);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_9);
lean_closure_set(x_10, 2, x_3);
x_11 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_withAntiquotSuffixSplice_parenthesizer___boxed), 8, 3);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_2);
lean_closure_set(x_11, 2, x_3);
x_12 = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(x_10, x_11, x_4, x_5, x_6, x_7, x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepByElemParser_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_8 = lean_mk_string_unchecked("sepBy", 5, 5);
x_9 = l_Lean_Name_mkStr1(x_8);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_string_utf8_byte_size(x_2);
x_12 = l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(x_2, x_11, x_10);
x_13 = l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(x_2, x_12, x_11);
x_14 = lean_string_utf8_extract(x_2, x_12, x_13);
lean_dec(x_13);
lean_dec(x_12);
x_15 = lean_mk_string_unchecked("*", 1, 1);
x_16 = lean_string_append(x_14, x_15);
lean_dec(x_15);
x_17 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___boxed), 6, 1);
lean_closure_set(x_17, 0, x_16);
x_18 = l_Lean_Parser_withAntiquotSpliceAndSuffix_parenthesizer(x_9, x_1, x_17, x_3, x_4, x_5, x_6, x_7);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepByElemParser_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Parser_sepByElemParser_parenthesizer(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy_parenthesizer___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_closure((void*)(l_Lean_Parser_sepByElemParser_parenthesizer___boxed), 7, 2);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_2);
x_10 = l_Lean_PrettyPrinter_Parenthesizer_sepByNoAntiquot_parenthesizer(x_9, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Parser_sepBy_parenthesizer___redArg(x_1, x_2, x_3, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = l_Lean_Parser_sepBy_parenthesizer(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1_formatter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_closure((void*)(l_Lean_Parser_sepByElemParser_formatter___boxed), 7, 2);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_2);
x_10 = l_Lean_PrettyPrinter_Formatter_sepByNoAntiquot_formatter(x_9, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Parser_sepBy1_formatter___redArg(x_1, x_2, x_3, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = l_Lean_Parser_sepBy1_formatter(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1_parenthesizer___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_closure((void*)(l_Lean_Parser_sepByElemParser_parenthesizer___boxed), 7, 2);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_2);
x_10 = l_Lean_PrettyPrinter_Parenthesizer_sepByNoAntiquot_parenthesizer(x_9, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Parser_sepBy1_parenthesizer___redArg(x_1, x_2, x_3, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = l_Lean_Parser_sepBy1_parenthesizer(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbol_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_unicodeSymbolNoAntiquot_formatter), 7, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_2);
x_9 = l_Lean_PrettyPrinter_Formatter_tokenWithAntiquot_formatter(x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbol_parenthesizer___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___redArg___lam__0___boxed), 5, 0);
x_7 = l_Lean_PrettyPrinter_Parenthesizer_tokenWithAntiquot_parenthesizer(x_6, x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbol_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Parser_unicodeSymbol_parenthesizer___redArg(x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbol_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Parser_unicodeSymbol_parenthesizer(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withCache_formatter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withCache_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_apply_5(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withCache_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Parser_withCache_formatter(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withCache_parenthesizer___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withCache_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_apply_5(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withCache_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Parser_withCache_parenthesizer(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withResetCache_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withResetCache_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withPosition_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withPositionAfterLinebreak_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withoutPosition_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withoutPosition_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withForbidden_formatter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withForbidden_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_apply_5(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withForbidden_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Parser_withForbidden_formatter(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withForbidden_parenthesizer___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withForbidden_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_apply_5(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withForbidden_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Parser_withForbidden_parenthesizer(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withoutForbidden_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withoutForbidden_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_incQuotDepth_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_incQuotDepth_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_suppressInsideQuot_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_suppressInsideQuot_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalInsideQuot_formatter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalInsideQuot_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_apply_5(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalInsideQuot_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Parser_evalInsideQuot_formatter(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalInsideQuot_parenthesizer___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalInsideQuot_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_apply_5(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalInsideQuot_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Parser_evalInsideQuot_parenthesizer(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withOpen_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withOpen_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withOpenDecl_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withOpenDecl_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_dbgTraceState_formatter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_dbgTraceState_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_apply_5(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_dbgTraceState_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Parser_dbgTraceState_formatter(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_dbgTraceState_parenthesizer___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_dbgTraceState_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_apply_5(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_dbgTraceState_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Parser_dbgTraceState_parenthesizer(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_optional_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_mk_string_unchecked("optional", 8, 8);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("\?", 1, 1);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter), 6, 1);
lean_closure_set(x_10, 0, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotSpliceAndSuffix_formatter), 8, 3);
lean_closure_set(x_11, 0, x_8);
lean_closure_set(x_11, 1, x_1);
lean_closure_set(x_11, 2, x_10);
x_12 = l_Lean_PrettyPrinter_Formatter_optionalNoAntiquot_formatter(x_11, x_2, x_3, x_4, x_5, x_6);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_optional_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_mk_string_unchecked("optional", 8, 8);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("\?", 1, 1);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___boxed), 6, 1);
lean_closure_set(x_10, 0, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotSpliceAndSuffix_parenthesizer), 8, 3);
lean_closure_set(x_11, 0, x_8);
lean_closure_set(x_11, 1, x_1);
lean_closure_set(x_11, 2, x_10);
x_12 = l_Lean_PrettyPrinter_Parenthesizer_visitArgs(x_11, x_2, x_3, x_4, x_5, x_6);
return x_12;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_optional_docString__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("optional", 8, 8);
x_5 = l_Lean_Name_mkStr3(x_2, x_3, x_4);
x_6 = lean_mk_string_unchecked("The parser `optional(p)`, or `(p)\?`, parses `p` if it succeeds,\notherwise it succeeds with no value.\n\nNote that because `\?` is a legal identifier character, one must write `(p)\?` or `p \?` for\nit to parse correctly. `ident\?` will not work; one must write `(ident)\?` instead.\n\nThis parser has arity 1: it produces a `nullKind` node containing either zero arguments\n(for the `none` case) or the list of arguments produced by `p`.\n(In particular, if `p` has arity 0 then the two cases are not differentiated!) ", 506, 506);
x_7 = l_Lean_addBuiltinDocString(x_5, x_6, x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_optional(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_mk_string_unchecked("optional", 8, 8);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_mk_string_unchecked("\?", 1, 1);
x_5 = l_Lean_Parser_symbol(x_4);
lean_dec(x_4);
x_6 = l_Lean_Parser_withAntiquotSpliceAndSuffix(x_3, x_1, x_5);
x_7 = l_Lean_Parser_optionalNoAntiquot(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_many_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_mk_string_unchecked("many", 4, 4);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("*", 1, 1);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter), 6, 1);
lean_closure_set(x_10, 0, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotSpliceAndSuffix_formatter), 8, 3);
lean_closure_set(x_11, 0, x_8);
lean_closure_set(x_11, 1, x_1);
lean_closure_set(x_11, 2, x_10);
x_12 = l_Lean_PrettyPrinter_Formatter_manyNoAntiquot_formatter(x_11, x_2, x_3, x_4, x_5, x_6);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_many_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_mk_string_unchecked("many", 4, 4);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("*", 1, 1);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___boxed), 6, 1);
lean_closure_set(x_10, 0, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotSpliceAndSuffix_parenthesizer), 8, 3);
lean_closure_set(x_11, 0, x_8);
lean_closure_set(x_11, 1, x_1);
lean_closure_set(x_11, 2, x_10);
x_12 = l_Lean_PrettyPrinter_Parenthesizer_manyNoAntiquot_parenthesizer(x_11, x_2, x_3, x_4, x_5, x_6);
return x_12;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_many_docString__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("many", 4, 4);
x_5 = l_Lean_Name_mkStr3(x_2, x_3, x_4);
x_6 = lean_mk_string_unchecked("The parser `many(p)`, or `p*`, repeats `p` until it fails, and returns the list of results.\n\nThe argument `p` is \"auto-grouped\", meaning that if the arity is greater than 1 it will be\nautomatically replaced by `group(p)` to ensure that it produces exactly 1 value.\n\nThis parser has arity 1: it produces a `nullKind` node containing one argument for each\ninvocation of `p` (or `group(p)`). ", 389, 389);
x_7 = l_Lean_addBuiltinDocString(x_5, x_6, x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_many(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_mk_string_unchecked("many", 4, 4);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_mk_string_unchecked("*", 1, 1);
x_5 = l_Lean_Parser_symbol(x_4);
lean_dec(x_4);
x_6 = l_Lean_Parser_withAntiquotSpliceAndSuffix(x_3, x_1, x_5);
x_7 = l_Lean_Parser_manyNoAntiquot(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_many1_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_mk_string_unchecked("many", 4, 4);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("*", 1, 1);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter), 6, 1);
lean_closure_set(x_10, 0, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotSpliceAndSuffix_formatter), 8, 3);
lean_closure_set(x_11, 0, x_8);
lean_closure_set(x_11, 1, x_1);
lean_closure_set(x_11, 2, x_10);
x_12 = l_Lean_PrettyPrinter_Formatter_manyNoAntiquot_formatter(x_11, x_2, x_3, x_4, x_5, x_6);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_many1_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_mk_string_unchecked("many", 4, 4);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("*", 1, 1);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___boxed), 6, 1);
lean_closure_set(x_10, 0, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotSpliceAndSuffix_parenthesizer), 8, 3);
lean_closure_set(x_11, 0, x_8);
lean_closure_set(x_11, 1, x_1);
lean_closure_set(x_11, 2, x_10);
x_12 = l_Lean_PrettyPrinter_Parenthesizer_manyNoAntiquot_parenthesizer(x_11, x_2, x_3, x_4, x_5, x_6);
return x_12;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_many1_docString__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("many1", 5, 5);
x_5 = l_Lean_Name_mkStr3(x_2, x_3, x_4);
x_6 = lean_mk_string_unchecked("The parser `many1(p)`, or `p+`, repeats `p` until it fails, and returns the list of results.\n`p` must succeed at least once, or this parser will fail.\n\nNote that this parser produces the same parse tree as the `many(p)` / `p*` combinator,\nand one matches both `p*` and `p+` using `$[ .. ]*` syntax in a syntax match.\n(There is no `$[ .. ]+` syntax.)\n\nThe argument `p` is \"auto-grouped\", meaning that if the arity is greater than 1 it will be\nautomatically replaced by `group(p)` to ensure that it produces exactly 1 value.\n\nThis parser has arity 1: it produces a `nullKind` node containing one argument for each\ninvocation of `p` (or `group(p)`). ", 647, 647);
x_7 = l_Lean_addBuiltinDocString(x_5, x_6, x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_many1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_mk_string_unchecked("many", 4, 4);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_mk_string_unchecked("*", 1, 1);
x_5 = l_Lean_Parser_symbol(x_4);
lean_dec(x_4);
x_6 = l_Lean_Parser_withAntiquotSpliceAndSuffix(x_3, x_1, x_5);
x_7 = l_Lean_Parser_many1NoAntiquot(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ident_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_mk_string_unchecked("ident", 5, 5);
lean_inc(x_6);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = lean_box(1);
x_9 = lean_box(0);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(x_10, 0, x_6);
lean_closure_set(x_10, 1, x_7);
lean_closure_set(x_10, 2, x_8);
lean_closure_set(x_10, 3, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter), 5, 0);
x_12 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_10, x_11, x_1, x_2, x_3, x_4, x_5);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ident_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_mk_string_unchecked("ident", 5, 5);
lean_inc(x_6);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = lean_box(1);
x_9 = lean_box(0);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(x_10, 0, x_6);
lean_closure_set(x_10, 1, x_7);
lean_closure_set(x_10, 2, x_8);
lean_closure_set(x_10, 3, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_identNoAntiquot_parenthesizer___boxed), 5, 0);
x_12 = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(x_10, x_11, x_1, x_2, x_3, x_4, x_5);
return x_12;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_ident_docString__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("ident", 5, 5);
x_5 = l_Lean_Name_mkStr3(x_2, x_3, x_4);
x_6 = lean_mk_string_unchecked("The parser `ident` parses a single identifier, possibly with namespaces, such as `foo` or\n`bar.baz`. The identifier must not be a declared token, so for example it will not match `\"def\"`\nbecause `def` is a keyword token. Tokens are implicitly declared by using them in string literals\nin parser declarations, so `syntax foo := \"bla\"` will make `bla` no longer legal as an identifier.\n\nIdentifiers can contain special characters or keywords if they are escaped using the `«»` characters:\n`«def»` is an identifier named `def`, and `«x»` is treated the same as `x`. This is useful for\nusing disallowed characters in identifiers such as `«foo.bar».baz` or `«hello world»`.\n\nThis parser has arity 1: it produces a `Syntax.ident` node containing the parsed identifier.\nYou can use `TSyntax.getId` to extract the name from the resulting syntax object. ", 855, 845);
x_7 = l_Lean_addBuiltinDocString(x_5, x_6, x_1);
return x_7;
}
}
static lean_object* _init_l_Lean_Parser_ident() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_1 = lean_mk_string_unchecked("ident", 5, 5);
lean_inc(x_1);
x_2 = l_Lean_Name_mkStr1(x_1);
x_3 = lean_box(1);
x_4 = lean_box(0);
x_5 = lean_unbox(x_3);
x_6 = lean_unbox(x_4);
x_7 = l_Lean_Parser_mkAntiquot(x_1, x_2, x_5, x_6);
lean_dec(x_1);
x_8 = l_Lean_Parser_identNoAntiquot;
x_9 = l_Lean_Parser_withAntiquot(x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_identWithPartialTrailingDot_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_ident_formatter), 5, 0);
x_7 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkNoWsBefore_formatter___boxed), 5, 0);
x_8 = lean_mk_string_unchecked(".", 1, 1);
x_9 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter), 6, 1);
lean_closure_set(x_9, 0, x_8);
lean_inc(x_6);
lean_inc(x_7);
x_10 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_10, 0, x_7);
lean_closure_set(x_10, 1, x_6);
x_11 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_11, 0, x_9);
lean_closure_set(x_11, 1, x_10);
x_12 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_12, 0, x_7);
lean_closure_set(x_12, 1, x_11);
x_13 = lean_alloc_closure((void*)(l_Lean_Parser_optional_formatter), 6, 1);
lean_closure_set(x_13, 0, x_12);
x_14 = l_Lean_PrettyPrinter_Formatter_andthen_formatter(x_6, x_13, x_1, x_2, x_3, x_4, x_5);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_identWithPartialTrailingDot_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_ident_parenthesizer), 5, 0);
x_7 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkNoWsBefore_parenthesizer___boxed), 5, 0);
x_8 = lean_mk_string_unchecked(".", 1, 1);
x_9 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___boxed), 6, 1);
lean_closure_set(x_9, 0, x_8);
lean_inc(x_6);
lean_inc(x_7);
x_10 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_10, 0, x_7);
lean_closure_set(x_10, 1, x_6);
x_11 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_11, 0, x_9);
lean_closure_set(x_11, 1, x_10);
x_12 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_12, 0, x_7);
lean_closure_set(x_12, 1, x_11);
x_13 = lean_alloc_closure((void*)(l_Lean_Parser_optional_parenthesizer), 6, 1);
lean_closure_set(x_13, 0, x_12);
x_14 = l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer(x_6, x_13, x_1, x_2, x_3, x_4, x_5);
return x_14;
}
}
static lean_object* _init_l_Lean_Parser_identWithPartialTrailingDot() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_1 = l_Lean_Parser_ident;
x_2 = lean_mk_string_unchecked("no space before", 15, 15);
x_3 = l_Lean_Parser_checkNoWsBefore(x_2);
x_4 = lean_mk_string_unchecked(".", 1, 1);
x_5 = l_Lean_Parser_symbol(x_4);
lean_dec(x_4);
lean_inc(x_3);
x_6 = l_Lean_Parser_andthen(x_3, x_1);
x_7 = l_Lean_Parser_andthen(x_5, x_6);
x_8 = l_Lean_Parser_andthen(x_3, x_7);
x_9 = l_Lean_Parser_optional(x_8);
x_10 = l_Lean_Parser_andthen(x_1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_rawIdent_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_mk_string_unchecked("ident", 5, 5);
lean_inc(x_6);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = lean_box(1);
x_9 = lean_box(0);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(x_10, 0, x_6);
lean_closure_set(x_10, 1, x_7);
lean_closure_set(x_10, 2, x_8);
lean_closure_set(x_10, 3, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_rawIdentNoAntiquot_formatter), 5, 0);
x_12 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_10, x_11, x_1, x_2, x_3, x_4, x_5);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_rawIdent_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___redArg___lam__0___boxed), 5, 0);
x_7 = lean_mk_string_unchecked("ident", 5, 5);
lean_inc(x_7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_box(1);
x_10 = lean_box(0);
x_11 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(x_11, 0, x_7);
lean_closure_set(x_11, 1, x_8);
lean_closure_set(x_11, 2, x_9);
lean_closure_set(x_11, 3, x_10);
x_12 = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(x_11, x_6, x_1, x_2, x_3, x_4, x_5);
return x_12;
}
}
static lean_object* _init_l_Lean_Parser_rawIdent() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_1 = lean_mk_string_unchecked("ident", 5, 5);
lean_inc(x_1);
x_2 = l_Lean_Name_mkStr1(x_1);
x_3 = lean_box(1);
x_4 = lean_box(0);
x_5 = lean_unbox(x_3);
x_6 = lean_unbox(x_4);
x_7 = l_Lean_Parser_mkAntiquot(x_1, x_2, x_5, x_6);
lean_dec(x_1);
x_8 = l_Lean_Parser_rawIdentNoAntiquot;
x_9 = l_Lean_Parser_withAntiquot(x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_hygieneInfo_formatter___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Syntax_MonadTraverser_goLeft___at___Lean_PrettyPrinter_Formatter_visitArgs_spec__1(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_hygieneInfo_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_hygieneInfo_formatter___lam__0___boxed), 5, 0);
x_7 = lean_mk_string_unchecked("hygieneInfo", 11, 11);
lean_inc(x_7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_box(0);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(x_10, 0, x_7);
lean_closure_set(x_10, 1, x_8);
lean_closure_set(x_10, 2, x_9);
lean_closure_set(x_10, 3, x_9);
x_11 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_10, x_6, x_1, x_2, x_3, x_4, x_5);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_hygieneInfo_formatter___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_hygieneInfo_formatter___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_hygieneInfo_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___lam__0___boxed), 5, 0);
x_7 = lean_mk_string_unchecked("hygieneInfo", 11, 11);
lean_inc(x_7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_box(0);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(x_10, 0, x_7);
lean_closure_set(x_10, 1, x_8);
lean_closure_set(x_10, 2, x_9);
lean_closure_set(x_10, 3, x_9);
x_11 = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(x_10, x_6, x_1, x_2, x_3, x_4, x_5);
return x_11;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_hygieneInfo_docString__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("hygieneInfo", 11, 11);
x_5 = l_Lean_Name_mkStr3(x_2, x_3, x_4);
x_6 = lean_mk_string_unchecked("The parser `hygieneInfo` parses no text, but captures the current macro scope information\nas though it parsed an identifier at the current position. It returns a `hygieneInfoKind` node\naround an `.ident` which is `Name.anonymous` but with macro scopes like a regular identifier.\n\nThis is used to implement `have := ...` syntax: the `hygieneInfo` between the `have` and `:=`\nsubstitutes for the identifier which would normally go there as in `have x :=`, so that we\ncan expand `have :=` to `have this :=` while retaining the usual macro name resolution behavior.\nSee [doc/macro_overview.md](https://github.com/leanprover/lean4/blob/master/doc/macro_overview.md)\nfor more information about macro hygiene.\n\nThis parser has arity 1: it produces a `Syntax.ident` node containing the parsed identifier.\nYou can use `TSyntax.getHygieneInfo` to extract the name from the resulting syntax object. ", 888, 888);
x_7 = l_Lean_addBuiltinDocString(x_5, x_6, x_1);
return x_7;
}
}
static lean_object* _init_l_Lean_Parser_hygieneInfo() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_1 = lean_mk_string_unchecked("hygieneInfo", 11, 11);
lean_inc(x_1);
x_2 = l_Lean_Name_mkStr1(x_1);
x_3 = lean_box(0);
x_4 = lean_unbox(x_3);
x_5 = lean_unbox(x_3);
x_6 = l_Lean_Parser_mkAntiquot(x_1, x_2, x_4, x_5);
lean_dec(x_1);
x_7 = l_Lean_Parser_hygieneInfoNoAntiquot;
x_8 = l_Lean_Parser_withAntiquot(x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_numLit_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_mk_string_unchecked("num", 3, 3);
lean_inc(x_6);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = lean_box(1);
x_9 = lean_box(0);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(x_10, 0, x_6);
lean_closure_set(x_10, 1, x_7);
lean_closure_set(x_10, 2, x_8);
lean_closure_set(x_10, 3, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_numLitNoAntiquot_formatter), 5, 0);
x_12 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_10, x_11, x_1, x_2, x_3, x_4, x_5);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_numLit_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___redArg___lam__0___boxed), 5, 0);
x_7 = lean_mk_string_unchecked("num", 3, 3);
lean_inc(x_7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_box(1);
x_10 = lean_box(0);
x_11 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(x_11, 0, x_7);
lean_closure_set(x_11, 1, x_8);
lean_closure_set(x_11, 2, x_9);
lean_closure_set(x_11, 3, x_10);
x_12 = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(x_11, x_6, x_1, x_2, x_3, x_4, x_5);
return x_12;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_numLit_docString__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("numLit", 6, 6);
x_5 = l_Lean_Name_mkStr3(x_2, x_3, x_4);
x_6 = lean_mk_string_unchecked("The parser `num` parses a numeric literal in several bases:\n\n* Decimal: `129`\n* Hexadecimal: `0xdeadbeef`\n* Octal: `0o755`\n* Binary: `0b1101`\n\nThis parser has arity 1: it produces a `numLitKind` node containing an atom with the text of the\nliteral.\nYou can use `TSyntax.getNat` to extract the number from the resulting syntax object. ", 334, 334);
x_7 = l_Lean_addBuiltinDocString(x_5, x_6, x_1);
return x_7;
}
}
static lean_object* _init_l_Lean_Parser_numLit() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_1 = lean_mk_string_unchecked("num", 3, 3);
lean_inc(x_1);
x_2 = l_Lean_Name_mkStr1(x_1);
x_3 = lean_box(1);
x_4 = lean_box(0);
x_5 = lean_unbox(x_3);
x_6 = lean_unbox(x_4);
x_7 = l_Lean_Parser_mkAntiquot(x_1, x_2, x_5, x_6);
lean_dec(x_1);
x_8 = l_Lean_Parser_numLitNoAntiquot;
x_9 = l_Lean_Parser_withAntiquot(x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_scientificLit_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_mk_string_unchecked("scientific", 10, 10);
lean_inc(x_6);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = lean_box(1);
x_9 = lean_box(0);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(x_10, 0, x_6);
lean_closure_set(x_10, 1, x_7);
lean_closure_set(x_10, 2, x_8);
lean_closure_set(x_10, 3, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_scientificLitNoAntiquot_formatter), 5, 0);
x_12 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_10, x_11, x_1, x_2, x_3, x_4, x_5);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_scientificLit_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___redArg___lam__0___boxed), 5, 0);
x_7 = lean_mk_string_unchecked("scientific", 10, 10);
lean_inc(x_7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_box(1);
x_10 = lean_box(0);
x_11 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(x_11, 0, x_7);
lean_closure_set(x_11, 1, x_8);
lean_closure_set(x_11, 2, x_9);
lean_closure_set(x_11, 3, x_10);
x_12 = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(x_11, x_6, x_1, x_2, x_3, x_4, x_5);
return x_12;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_scientificLit_docString__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("scientificLit", 13, 13);
x_5 = l_Lean_Name_mkStr3(x_2, x_3, x_4);
x_6 = lean_mk_string_unchecked("The parser `scientific` parses a scientific-notation literal, such as `1.3e-24`.\n\nThis parser has arity 1: it produces a `scientificLitKind` node containing an atom with the text\nof the literal.\nYou can use `TSyntax.getScientific` to extract the parts from the resulting syntax object. ", 286, 286);
x_7 = l_Lean_addBuiltinDocString(x_5, x_6, x_1);
return x_7;
}
}
static lean_object* _init_l_Lean_Parser_scientificLit() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_1 = lean_mk_string_unchecked("scientific", 10, 10);
lean_inc(x_1);
x_2 = l_Lean_Name_mkStr1(x_1);
x_3 = lean_box(1);
x_4 = lean_box(0);
x_5 = lean_unbox(x_3);
x_6 = lean_unbox(x_4);
x_7 = l_Lean_Parser_mkAntiquot(x_1, x_2, x_5, x_6);
lean_dec(x_1);
x_8 = l_Lean_Parser_scientificLitNoAntiquot;
x_9 = l_Lean_Parser_withAntiquot(x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_strLit_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_mk_string_unchecked("str", 3, 3);
lean_inc(x_6);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = lean_box(1);
x_9 = lean_box(0);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(x_10, 0, x_6);
lean_closure_set(x_10, 1, x_7);
lean_closure_set(x_10, 2, x_8);
lean_closure_set(x_10, 3, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_strLitNoAntiquot_formatter), 5, 0);
x_12 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_10, x_11, x_1, x_2, x_3, x_4, x_5);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_strLit_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___redArg___lam__0___boxed), 5, 0);
x_7 = lean_mk_string_unchecked("str", 3, 3);
lean_inc(x_7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_box(1);
x_10 = lean_box(0);
x_11 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(x_11, 0, x_7);
lean_closure_set(x_11, 1, x_8);
lean_closure_set(x_11, 2, x_9);
lean_closure_set(x_11, 3, x_10);
x_12 = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(x_11, x_6, x_1, x_2, x_3, x_4, x_5);
return x_12;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_strLit_docString__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("strLit", 6, 6);
x_5 = l_Lean_Name_mkStr3(x_2, x_3, x_4);
x_6 = lean_mk_string_unchecked("The parser `str` parses a string literal, such as `\"foo\"` or `\"\\r\\n\"`. Strings can contain\nC-style escapes like `\\n`, `\\\"`, `\\x00` or `\\u2665`, as well as literal unicode characters like `∈`.\nNewlines in a string are interpreted literally.\n\nThis parser has arity 1: it produces a `strLitKind` node containing an atom with the raw\nliteral (including the quote marks and without interpreting the escapes).\nYou can use `TSyntax.getString` to decode the string from the resulting syntax object. ", 493, 491);
x_7 = l_Lean_addBuiltinDocString(x_5, x_6, x_1);
return x_7;
}
}
static lean_object* _init_l_Lean_Parser_strLit() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_1 = lean_mk_string_unchecked("str", 3, 3);
lean_inc(x_1);
x_2 = l_Lean_Name_mkStr1(x_1);
x_3 = lean_box(1);
x_4 = lean_box(0);
x_5 = lean_unbox(x_3);
x_6 = lean_unbox(x_4);
x_7 = l_Lean_Parser_mkAntiquot(x_1, x_2, x_5, x_6);
lean_dec(x_1);
x_8 = l_Lean_Parser_strLitNoAntiquot;
x_9 = l_Lean_Parser_withAntiquot(x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_charLit_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_mk_string_unchecked("char", 4, 4);
lean_inc(x_6);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = lean_box(1);
x_9 = lean_box(0);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(x_10, 0, x_6);
lean_closure_set(x_10, 1, x_7);
lean_closure_set(x_10, 2, x_8);
lean_closure_set(x_10, 3, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_charLitNoAntiquot_formatter), 5, 0);
x_12 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_10, x_11, x_1, x_2, x_3, x_4, x_5);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_charLit_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___redArg___lam__0___boxed), 5, 0);
x_7 = lean_mk_string_unchecked("char", 4, 4);
lean_inc(x_7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_box(1);
x_10 = lean_box(0);
x_11 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(x_11, 0, x_7);
lean_closure_set(x_11, 1, x_8);
lean_closure_set(x_11, 2, x_9);
lean_closure_set(x_11, 3, x_10);
x_12 = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(x_11, x_6, x_1, x_2, x_3, x_4, x_5);
return x_12;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_charLit_docString__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("charLit", 7, 7);
x_5 = l_Lean_Name_mkStr3(x_2, x_3, x_4);
x_6 = lean_mk_string_unchecked("The parser `char` parses a character literal, such as `'a'` or `'\\n'`. Character literals can\ncontain C-style escapes like `\\n`, `\\\"`, `\\x00` or `\\u2665`, as well as literal unicode characters\nlike `∈`, but must evaluate to a single unicode codepoint, so `'♥'` is allowed but `'❤️'` is not\n(since it is two codepoints but one grapheme cluster).\n\nThis parser has arity 1: it produces a `charLitKind` node containing an atom with the raw\nliteral (including the quote marks and without interpreting the escapes).\nYou can use `TSyntax.getChar` to decode the string from the resulting syntax object. ", 603, 595);
x_7 = l_Lean_addBuiltinDocString(x_5, x_6, x_1);
return x_7;
}
}
static lean_object* _init_l_Lean_Parser_charLit() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_1 = lean_mk_string_unchecked("char", 4, 4);
lean_inc(x_1);
x_2 = l_Lean_Name_mkStr1(x_1);
x_3 = lean_box(1);
x_4 = lean_box(0);
x_5 = lean_unbox(x_3);
x_6 = lean_unbox(x_4);
x_7 = l_Lean_Parser_mkAntiquot(x_1, x_2, x_5, x_6);
lean_dec(x_1);
x_8 = l_Lean_Parser_charLitNoAntiquot;
x_9 = l_Lean_Parser_withAntiquot(x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nameLit_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_mk_string_unchecked("name", 4, 4);
lean_inc(x_6);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = lean_box(1);
x_9 = lean_box(0);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(x_10, 0, x_6);
lean_closure_set(x_10, 1, x_7);
lean_closure_set(x_10, 2, x_8);
lean_closure_set(x_10, 3, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_nameLitNoAntiquot_formatter), 5, 0);
x_12 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_10, x_11, x_1, x_2, x_3, x_4, x_5);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nameLit_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___redArg___lam__0___boxed), 5, 0);
x_7 = lean_mk_string_unchecked("name", 4, 4);
lean_inc(x_7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_box(1);
x_10 = lean_box(0);
x_11 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(x_11, 0, x_7);
lean_closure_set(x_11, 1, x_8);
lean_closure_set(x_11, 2, x_9);
lean_closure_set(x_11, 3, x_10);
x_12 = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(x_11, x_6, x_1, x_2, x_3, x_4, x_5);
return x_12;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_nameLit_docString__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("nameLit", 7, 7);
x_5 = l_Lean_Name_mkStr3(x_2, x_3, x_4);
x_6 = lean_mk_string_unchecked("The parser `name` parses a name literal like `` `foo``. The syntax is the same as for identifiers\n(see `ident`) but with a leading backquote.\n\nThis parser has arity 1: it produces a `nameLitKind` node containing the raw literal\n(including the backquote).\nYou can use `TSyntax.getName` to extract the name from the resulting syntax object. ", 339, 339);
x_7 = l_Lean_addBuiltinDocString(x_5, x_6, x_1);
return x_7;
}
}
static lean_object* _init_l_Lean_Parser_nameLit() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_1 = lean_mk_string_unchecked("name", 4, 4);
lean_inc(x_1);
x_2 = l_Lean_Name_mkStr1(x_1);
x_3 = lean_box(1);
x_4 = lean_box(0);
x_5 = lean_unbox(x_3);
x_6 = lean_unbox(x_4);
x_7 = l_Lean_Parser_mkAntiquot(x_1, x_2, x_5, x_6);
lean_dec(x_1);
x_8 = l_Lean_Parser_nameLitNoAntiquot;
x_9 = l_Lean_Parser_withAntiquot(x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_group_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_mk_string_unchecked("group", 5, 5);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = l_Lean_PrettyPrinter_Formatter_node_formatter(x_8, x_1, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_group_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_mk_string_unchecked("group", 5, 5);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer(x_8, x_1, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_group_docString__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("group", 5, 5);
x_5 = l_Lean_Name_mkStr3(x_2, x_3, x_4);
x_6 = lean_mk_string_unchecked("The parser `group(p)` parses the same thing as `p`, but it wraps the results in a `groupKind`\nnode.\n\nThis parser always has arity 1, even if `p` does not. Parsers like `p*` are automatically\nrewritten to `group(p)*` if `p` does not have arity 1, so that the results from separate invocations\nof `p` can be differentiated. ", 322, 322);
x_7 = l_Lean_addBuiltinDocString(x_5, x_6, x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_group(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_mk_string_unchecked("group", 5, 5);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = l_Lean_Parser_node(x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_many1Indent_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkColGe_formatter___boxed), 5, 0);
x_8 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_8, 0, x_7);
lean_closure_set(x_8, 1, x_1);
x_9 = l_Lean_Parser_many1_formatter(x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_many1Indent_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkColGe_parenthesizer___boxed), 5, 0);
x_8 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_8, 0, x_7);
lean_closure_set(x_8, 1, x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_Parser_many1_parenthesizer), 6, 1);
lean_closure_set(x_9, 0, x_8);
x_10 = l_Lean_PrettyPrinter_Parenthesizer_withPosition_parenthesizer(x_9, x_2, x_3, x_4, x_5, x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_many1Indent_docString__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("many1Indent", 11, 11);
x_5 = l_Lean_Name_mkStr3(x_2, x_3, x_4);
x_6 = lean_mk_string_unchecked("The parser `many1Indent(p)` is equivalent to `withPosition((colGe p)+)`. This has the effect of\nparsing one or more occurrences of `p`, where each subsequent `p` parse needs to be indented\nthe same or more than the first parse.\n\nThis parser has arity 1, and returns a list of the results from `p`.\n`p` is \"auto-grouped\" if it is not arity 1. ", 342, 342);
x_7 = l_Lean_addBuiltinDocString(x_5, x_6, x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_many1Indent(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_mk_string_unchecked("irrelevant", 10, 10);
x_3 = l_Lean_Parser_checkColGe(x_2);
x_4 = l_Lean_Parser_andthen(x_3, x_1);
x_5 = l_Lean_Parser_many1(x_4);
x_6 = l_Lean_Parser_withPosition(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_manyIndent_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkColGe_formatter___boxed), 5, 0);
x_8 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_8, 0, x_7);
lean_closure_set(x_8, 1, x_1);
x_9 = l_Lean_Parser_many_formatter(x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_manyIndent_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkColGe_parenthesizer___boxed), 5, 0);
x_8 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_8, 0, x_7);
lean_closure_set(x_8, 1, x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_Parser_many_parenthesizer), 6, 1);
lean_closure_set(x_9, 0, x_8);
x_10 = l_Lean_PrettyPrinter_Parenthesizer_withPosition_parenthesizer(x_9, x_2, x_3, x_4, x_5, x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_manyIndent_docString__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("manyIndent", 10, 10);
x_5 = l_Lean_Name_mkStr3(x_2, x_3, x_4);
x_6 = lean_mk_string_unchecked("The parser `manyIndent(p)` is equivalent to `withPosition((colGe p)*)`. This has the effect of\nparsing zero or more occurrences of `p`, where each subsequent `p` parse needs to be indented\nthe same or more than the first parse.\n\nThis parser has arity 1, and returns a list of the results from `p`.\n`p` is \"auto-grouped\" if it is not arity 1. ", 342, 342);
x_7 = l_Lean_addBuiltinDocString(x_5, x_6, x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_manyIndent(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_mk_string_unchecked("irrelevant", 10, 10);
x_3 = l_Lean_Parser_checkColGe(x_2);
x_4 = l_Lean_Parser_andthen(x_3, x_1);
x_5 = l_Lean_Parser_many(x_4);
x_6 = l_Lean_Parser_withPosition(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepByIndent(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_5 = lean_mk_string_unchecked("sepBy", 5, 5);
x_6 = l_Lean_Name_mkStr1(x_5);
x_7 = lean_mk_string_unchecked("*", 1, 1);
x_8 = l_Lean_Parser_symbol(x_7);
lean_dec(x_7);
x_9 = l_Lean_Parser_withAntiquotSpliceAndSuffix(x_6, x_1, x_8);
x_10 = lean_mk_string_unchecked("irrelevant", 10, 10);
lean_inc(x_10);
x_11 = l_Lean_Parser_checkColGe(x_10);
x_12 = l_Lean_Parser_andthen(x_11, x_9);
x_13 = l_Lean_Parser_checkColEq(x_10);
x_14 = lean_mk_string_unchecked("line break", 10, 10);
x_15 = l_Lean_Parser_checkLinebreakBefore(x_14);
x_16 = l_Lean_Parser_pushNone;
x_17 = l_Lean_Parser_andthen(x_15, x_16);
x_18 = l_Lean_Parser_andthen(x_13, x_17);
x_19 = l_Lean_Parser_orelse(x_3, x_18);
x_20 = l_Lean_Parser_sepBy(x_12, x_2, x_19, x_4);
x_21 = l_Lean_Parser_withPosition(x_20);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepByIndent___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_4);
lean_dec(x_4);
x_6 = l_Lean_Parser_sepByIndent(x_1, x_2, x_3, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1Indent(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_5 = lean_mk_string_unchecked("sepBy", 5, 5);
x_6 = l_Lean_Name_mkStr1(x_5);
x_7 = lean_mk_string_unchecked("*", 1, 1);
x_8 = l_Lean_Parser_symbol(x_7);
lean_dec(x_7);
x_9 = l_Lean_Parser_withAntiquotSpliceAndSuffix(x_6, x_1, x_8);
x_10 = lean_mk_string_unchecked("irrelevant", 10, 10);
lean_inc(x_10);
x_11 = l_Lean_Parser_checkColGe(x_10);
x_12 = l_Lean_Parser_andthen(x_11, x_9);
x_13 = l_Lean_Parser_checkColEq(x_10);
x_14 = lean_mk_string_unchecked("line break", 10, 10);
x_15 = l_Lean_Parser_checkLinebreakBefore(x_14);
x_16 = l_Lean_Parser_pushNone;
x_17 = l_Lean_Parser_andthen(x_15, x_16);
x_18 = l_Lean_Parser_andthen(x_13, x_17);
x_19 = l_Lean_Parser_orelse(x_3, x_18);
x_20 = l_Lean_Parser_sepBy1(x_12, x_2, x_19, x_4);
x_21 = l_Lean_Parser_withPosition(x_20);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1Indent___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_4);
lean_dec(x_4);
x_6 = l_Lean_Parser_sepBy1Indent(x_1, x_2, x_3, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Lean_Parser_sepByIndent_formatter_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_3, x_6);
if (x_7 == 1)
{
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_16; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_3, x_8);
lean_dec(x_3);
x_22 = lean_unsigned_to_nat(2u);
x_23 = lean_nat_mod(x_4, x_22);
x_24 = lean_nat_dec_eq(x_23, x_8);
lean_dec(x_23);
if (x_24 == 0)
{
x_16 = x_24;
goto block_21;
}
else
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_array_fget(x_2, x_4);
x_26 = l_Lean_Syntax_matchesNull(x_25, x_6);
x_16 = x_26;
goto block_21;
}
block_15:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_nat_add(x_4, x_8);
lean_dec(x_4);
x_12 = lean_box(x_10);
x_13 = lean_array_push(x_5, x_12);
x_3 = x_9;
x_4 = x_11;
x_5 = x_13;
goto _start;
}
block_21:
{
if (x_16 == 0)
{
x_10 = x_16;
goto block_15;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = l_Lean_Syntax_getArgs(x_1);
x_18 = lean_array_get_size(x_17);
lean_dec(x_17);
x_19 = lean_nat_sub(x_18, x_8);
lean_dec(x_18);
x_20 = lean_nat_dec_eq(x_4, x_19);
lean_dec(x_19);
if (x_20 == 0)
{
x_10 = x_16;
goto block_15;
}
else
{
x_10 = x_7;
goto block_15;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Lean_Parser_sepByIndent_formatter_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_mapFinIdxM_map___at___Lean_Parser_sepByIndent_formatter_spec__0___redArg(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Parser_sepByIndent_formatter_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_11; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
lean_dec(x_5);
x_12 = lean_ctor_get(x_4, 0);
x_13 = lean_ctor_get(x_4, 1);
x_14 = lean_box(0);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_unsigned_to_nat(2u);
x_21 = lean_nat_mod(x_12, x_20);
x_22 = lean_nat_dec_eq(x_21, x_19);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_st_ref_get(x_7, x_10);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_1);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_26 = lean_apply_5(x_1, x_6, x_7, x_8, x_9, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_dec(x_24);
x_15 = x_26;
goto block_18;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_45; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
x_29 = l_Lean_PrettyPrinter_backtrackExceptionId;
x_45 = l_Lean_Exception_isInterrupt(x_27);
if (x_45 == 0)
{
uint8_t x_46; 
x_46 = l_Lean_Exception_isRuntime(x_27);
x_30 = x_46;
goto block_44;
}
else
{
x_30 = x_45;
goto block_44;
}
block_44:
{
if (x_30 == 0)
{
if (lean_obj_tag(x_27) == 0)
{
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_24);
x_15 = x_26;
goto block_18;
}
else
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_27, 0);
lean_inc(x_31);
lean_dec(x_27);
x_32 = l___private_Lean_InternalExceptionId_0__Lean_beqInternalExceptionId____x40_Lean_InternalExceptionId___hyg_26_(x_29, x_31);
lean_dec(x_31);
if (x_32 == 0)
{
lean_dec(x_28);
lean_dec(x_24);
x_15 = x_26;
goto block_18;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
lean_dec(x_26);
x_33 = lean_st_ref_set(x_7, x_24, x_28);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_unsigned_to_nat(1u);
x_36 = lean_nat_sub(x_2, x_35);
x_37 = lean_nat_dec_eq(x_12, x_36);
lean_dec(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_mk_string_unchecked("\n", 1, 1);
x_39 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_40 = l_Lean_PrettyPrinter_Formatter_pushWhitespace___redArg(x_39, x_7, x_34);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_42 = l_Lean_Syntax_MonadTraverser_goLeft___at___Lean_PrettyPrinter_Formatter_visitArgs_spec__1(x_6, x_7, x_8, x_9, x_41);
x_15 = x_42;
goto block_18;
}
else
{
lean_object* x_43; 
x_43 = l_Lean_Syntax_MonadTraverser_goLeft___at___Lean_PrettyPrinter_Formatter_visitArgs_spec__1(x_6, x_7, x_8, x_9, x_34);
x_15 = x_43;
goto block_18;
}
}
}
}
else
{
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_24);
x_15 = x_26;
goto block_18;
}
}
}
}
else
{
lean_object* x_47; 
lean_inc(x_3);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_47 = lean_apply_5(x_3, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_4 = x_13;
x_5 = x_14;
x_10 = x_48;
goto _start;
}
else
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
return x_47;
}
}
block_18:
{
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_4 = x_13;
x_5 = x_14;
x_10 = x_16;
goto _start;
}
else
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
return x_15;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Parser_sepByIndent_formatter_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_List_forIn_x27_loop___at___Lean_Parser_sepByIndent_formatter_spec__1___redArg(x_1, x_2, x_3, x_5, x_6, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_Parser_sepByIndent_formatter_spec__2(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_uget(x_1, x_2);
x_6 = lean_unbox(x_5);
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
LEAN_EXPORT lean_object* l_Lean_Parser_sepByIndent_formatter___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_5);
x_11 = l_List_forIn_x27_loop___at___Lean_Parser_sepByIndent_formatter_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
lean_ctor_set(x_11, 0, x_5);
return x_11;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_5);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
lean_dec(x_5);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepByIndent_formatter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_8 = l_Lean_Syntax_MonadTraverser_getCur___at___Lean_PrettyPrinter_Formatter_visitArgs_spec__2(x_3, x_4, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Syntax_getArgs(x_9);
x_12 = lean_array_get_size(x_11);
x_26 = lean_unsigned_to_nat(0u);
x_27 = lean_mk_empty_array_with_capacity(x_12);
lean_inc(x_12);
x_28 = l_Array_mapFinIdxM_map___at___Lean_Parser_sepByIndent_formatter_spec__0___redArg(x_9, x_11, x_12, x_26, x_27);
lean_dec(x_11);
lean_dec(x_9);
x_29 = lean_array_get_size(x_28);
x_30 = lean_nat_dec_lt(x_26, x_29);
if (x_30 == 0)
{
lean_dec(x_29);
lean_dec(x_28);
x_13 = x_30;
goto block_25;
}
else
{
if (x_30 == 0)
{
lean_dec(x_29);
lean_dec(x_28);
x_13 = x_30;
goto block_25;
}
else
{
size_t x_31; size_t x_32; uint8_t x_33; 
x_31 = lean_usize_of_nat(x_26);
x_32 = lean_usize_of_nat(x_29);
lean_dec(x_29);
x_33 = l_Array_anyMUnsafe_any___at___Lean_Parser_sepByIndent_formatter_spec__2(x_28, x_31, x_32);
lean_dec(x_28);
x_13 = x_33;
goto block_25;
}
}
block_25:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_inc(x_12);
x_14 = l_List_range(x_12);
x_15 = l_List_reverse___redArg(x_14);
x_16 = lean_box(0);
x_17 = lean_alloc_closure((void*)(l_Lean_Parser_sepByIndent_formatter___redArg___lam__0___boxed), 10, 5);
lean_closure_set(x_17, 0, x_2);
lean_closure_set(x_17, 1, x_12);
lean_closure_set(x_17, 2, x_1);
lean_closure_set(x_17, 3, x_15);
lean_closure_set(x_17, 4, x_16);
lean_inc(x_4);
x_18 = l_Lean_PrettyPrinter_Formatter_visitArgs(x_17, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_18) == 0)
{
if (x_13 == 0)
{
uint8_t x_19; 
lean_dec(x_4);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
lean_ctor_set(x_18, 0, x_16);
return x_18;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_16);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_dec(x_18);
x_24 = l_Lean_PrettyPrinter_Formatter_pushAlign___redArg(x_13, x_4, x_23);
lean_dec(x_4);
return x_24;
}
}
else
{
lean_dec(x_4);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepByIndent_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Parser_sepByIndent_formatter___redArg(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Lean_Parser_sepByIndent_formatter_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_mapFinIdxM_map___at___Lean_Parser_sepByIndent_formatter_spec__0___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Lean_Parser_sepByIndent_formatter_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_mapFinIdxM_map___at___Lean_Parser_sepByIndent_formatter_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Parser_sepByIndent_formatter_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_List_forIn_x27_loop___at___Lean_Parser_sepByIndent_formatter_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_4);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Parser_sepByIndent_formatter_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_List_forIn_x27_loop___at___Lean_Parser_sepByIndent_formatter_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Parser_sepByIndent_formatter_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Array_anyMUnsafe_any___at___Lean_Parser_sepByIndent_formatter_spec__2(x_1, x_4, x_5);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepByIndent_formatter___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Parser_sepByIndent_formatter___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_4);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepByIndent_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Parser_sepByIndent_formatter(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1Indent_formatter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Parser_sepByIndent_formatter___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1Indent_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Parser_sepByIndent_formatter___redArg(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1Indent_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Parser_sepBy1Indent_formatter(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepByIndent_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___lam__0___boxed), 5, 0);
x_11 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkColGe_parenthesizer___boxed), 5, 0);
x_12 = lean_mk_string_unchecked("sepBy", 5, 5);
x_13 = l_Lean_Name_mkStr1(x_12);
x_14 = lean_mk_string_unchecked("*", 1, 1);
x_15 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___boxed), 6, 1);
lean_closure_set(x_15, 0, x_14);
x_16 = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotSpliceAndSuffix_parenthesizer), 8, 3);
lean_closure_set(x_16, 0, x_13);
lean_closure_set(x_16, 1, x_1);
lean_closure_set(x_16, 2, x_15);
x_17 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_17, 0, x_11);
lean_closure_set(x_17, 1, x_16);
x_18 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkColEq_parenthesizer___boxed), 5, 0);
x_19 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkLinebreakBefore_parenthesizer___boxed), 5, 0);
x_20 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_20, 0, x_19);
lean_closure_set(x_20, 1, x_10);
x_21 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_21, 0, x_18);
lean_closure_set(x_21, 1, x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer), 7, 2);
lean_closure_set(x_22, 0, x_3);
lean_closure_set(x_22, 1, x_21);
x_23 = lean_box(x_4);
x_24 = lean_alloc_closure((void*)(l_Lean_Parser_sepBy_parenthesizer___boxed), 9, 4);
lean_closure_set(x_24, 0, x_17);
lean_closure_set(x_24, 1, x_2);
lean_closure_set(x_24, 2, x_22);
lean_closure_set(x_24, 3, x_23);
x_25 = l_Lean_PrettyPrinter_Parenthesizer_withPosition_parenthesizer(x_24, x_5, x_6, x_7, x_8, x_9);
return x_25;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepByIndent_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = l_Lean_Parser_sepByIndent_parenthesizer(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1Indent_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___lam__0___boxed), 5, 0);
x_11 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkColGe_parenthesizer___boxed), 5, 0);
x_12 = lean_mk_string_unchecked("sepBy", 5, 5);
x_13 = l_Lean_Name_mkStr1(x_12);
x_14 = lean_mk_string_unchecked("*", 1, 1);
x_15 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___boxed), 6, 1);
lean_closure_set(x_15, 0, x_14);
x_16 = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotSpliceAndSuffix_parenthesizer), 8, 3);
lean_closure_set(x_16, 0, x_13);
lean_closure_set(x_16, 1, x_1);
lean_closure_set(x_16, 2, x_15);
x_17 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_17, 0, x_11);
lean_closure_set(x_17, 1, x_16);
x_18 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkColEq_parenthesizer___boxed), 5, 0);
x_19 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkLinebreakBefore_parenthesizer___boxed), 5, 0);
x_20 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_20, 0, x_19);
lean_closure_set(x_20, 1, x_10);
x_21 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_21, 0, x_18);
lean_closure_set(x_21, 1, x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer), 7, 2);
lean_closure_set(x_22, 0, x_3);
lean_closure_set(x_22, 1, x_21);
x_23 = lean_box(x_4);
x_24 = lean_alloc_closure((void*)(l_Lean_Parser_sepBy1_parenthesizer___boxed), 9, 4);
lean_closure_set(x_24, 0, x_17);
lean_closure_set(x_24, 1, x_2);
lean_closure_set(x_24, 2, x_22);
lean_closure_set(x_24, 3, x_23);
x_25 = l_Lean_PrettyPrinter_Parenthesizer_withPosition_parenthesizer(x_24, x_5, x_6, x_7, x_8, x_9);
return x_25;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1Indent_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = l_Lean_Parser_sepBy1Indent_parenthesizer(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_notSymbol_formatter___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Formatter_notFollowedBy_formatter___redArg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_notSymbol_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Formatter_notFollowedBy_formatter___redArg(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_notSymbol_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_notSymbol_formatter(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_notSymbol_parenthesizer___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Parenthesizer_notFollowedBy_parenthesizer___redArg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_notSymbol_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Parenthesizer_notFollowedBy_parenthesizer___redArg(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_notSymbol_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_notSymbol_parenthesizer(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_notSymbol(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Parser_symbol(x_1);
x_3 = l_Lean_Parser_notFollowedBy(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_patternIgnore_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_mk_string_unchecked("patternIgnore", 13, 13);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = l_Lean_PrettyPrinter_Formatter_node_formatter(x_8, x_1, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_patternIgnore_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_mk_string_unchecked("patternIgnore", 13, 13);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer(x_8, x_1, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_patternIgnore_docString__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("patternIgnore", 13, 13);
x_5 = l_Lean_Name_mkStr3(x_2, x_3, x_4);
x_6 = lean_mk_string_unchecked("No-op parser combinator that annotates subtrees to be ignored in syntax patterns. ", 82, 82);
x_7 = l_Lean_addBuiltinDocString(x_5, x_6, x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_patternIgnore(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_mk_string_unchecked("patternIgnore", 13, 13);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = l_Lean_Parser_node(x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_ppHardSpace_docString__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("ppHardSpace", 11, 11);
x_5 = l_Lean_Name_mkStr3(x_2, x_3, x_4);
x_6 = lean_mk_string_unchecked("No-op parser that advises the pretty printer to emit a non-breaking space. ", 75, 75);
x_7 = l_Lean_addBuiltinDocString(x_5, x_6, x_1);
return x_7;
}
}
static lean_object* _init_l_Lean_Parser_ppHardSpace() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_skip;
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_ppSpace_docString__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("ppSpace", 7, 7);
x_5 = l_Lean_Name_mkStr3(x_2, x_3, x_4);
x_6 = lean_mk_string_unchecked("No-op parser that advises the pretty printer to emit a space/soft line break. ", 78, 78);
x_7 = l_Lean_addBuiltinDocString(x_5, x_6, x_1);
return x_7;
}
}
static lean_object* _init_l_Lean_Parser_ppSpace() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_skip;
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_ppLine_docString__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("ppLine", 6, 6);
x_5 = l_Lean_Name_mkStr3(x_2, x_3, x_4);
x_6 = lean_mk_string_unchecked("No-op parser that advises the pretty printer to emit a hard line break. ", 72, 72);
x_7 = l_Lean_addBuiltinDocString(x_5, x_6, x_1);
return x_7;
}
}
static lean_object* _init_l_Lean_Parser_ppLine() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_skip;
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_ppRealFill_docString__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("ppRealFill", 10, 10);
x_5 = l_Lean_Name_mkStr3(x_2, x_3, x_4);
x_6 = lean_mk_string_unchecked("No-op parser combinator that advises the pretty printer to emit a `Format.fill` node. ", 86, 86);
x_7 = l_Lean_addBuiltinDocString(x_5, x_6, x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppRealFill(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppRealFill___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_ppRealFill(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_ppRealGroup_docString__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("ppRealGroup", 11, 11);
x_5 = l_Lean_Name_mkStr3(x_2, x_3, x_4);
x_6 = lean_mk_string_unchecked("No-op parser combinator that advises the pretty printer to emit a `Format.group` node. ", 87, 87);
x_7 = l_Lean_addBuiltinDocString(x_5, x_6, x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppRealGroup(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppRealGroup___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_ppRealGroup(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_ppIndent_docString__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("ppIndent", 8, 8);
x_5 = l_Lean_Name_mkStr3(x_2, x_3, x_4);
x_6 = lean_mk_string_unchecked("No-op parser combinator that advises the pretty printer to indent the given syntax without grouping it. ", 104, 104);
x_7 = l_Lean_addBuiltinDocString(x_5, x_6, x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppIndent(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppIndent___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_ppIndent(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_ppGroup_docString__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("ppGroup", 7, 7);
x_5 = l_Lean_Name_mkStr3(x_2, x_3, x_4);
x_6 = lean_mk_string_unchecked("No-op parser combinator that advises the pretty printer to group and indent the given syntax.\nBy default, only syntax categories are grouped. ", 142, 142);
x_7 = l_Lean_addBuiltinDocString(x_5, x_6, x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppGroup(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppGroup___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_ppGroup(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_ppDedent_docString__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("ppDedent", 8, 8);
x_5 = l_Lean_Name_mkStr3(x_2, x_3, x_4);
x_6 = lean_mk_string_unchecked("No-op parser combinator that advises the pretty printer to dedent the given syntax.\nDedenting can in particular be used to counteract automatic indentation. ", 157, 157);
x_7 = l_Lean_addBuiltinDocString(x_5, x_6, x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppDedent(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppDedent___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_ppDedent(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_ppAllowUngrouped_docString__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("ppAllowUngrouped", 16, 16);
x_5 = l_Lean_Name_mkStr3(x_2, x_3, x_4);
x_6 = lean_mk_string_unchecked("No-op parser combinator that allows the pretty printer to omit the group and\nindent operation in the enclosing category parser.\n```\nsyntax ppAllowUngrouped \"by \" tacticSeq : term\n-- allows a `by` after `:=` without linebreak in between:\ntheorem foo : True := by\n  trivial\n```\n", 276, 276);
x_7 = l_Lean_addBuiltinDocString(x_5, x_6, x_1);
return x_7;
}
}
static lean_object* _init_l_Lean_Parser_ppAllowUngrouped() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_skip;
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_ppDedentIfGrouped_docString__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("ppDedentIfGrouped", 17, 17);
x_5 = l_Lean_Name_mkStr3(x_2, x_3, x_4);
x_6 = lean_mk_string_unchecked("No-op parser combinator that advises the pretty printer to dedent the given syntax,\nif it was grouped by the category parser.\nDedenting can in particular be used to counteract automatic indentation. ", 199, 199);
x_7 = l_Lean_addBuiltinDocString(x_5, x_6, x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppDedentIfGrouped(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppDedentIfGrouped___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_ppDedentIfGrouped(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_ppHardLineUnlessUngrouped_docString__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("ppHardLineUnlessUngrouped", 25, 25);
x_5 = l_Lean_Name_mkStr3(x_2, x_3, x_4);
x_6 = lean_mk_string_unchecked("No-op parser combinator that prints a line break.\nThe line break is soft if the combinator is followed\nby an ungrouped parser (see ppAllowUngrouped), otherwise hard. ", 166, 166);
x_7 = l_Lean_addBuiltinDocString(x_5, x_6, x_1);
return x_7;
}
}
static lean_object* _init_l_Lean_Parser_ppHardLineUnlessUngrouped() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_skip;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_ppHardSpace_formatter___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_mk_string_unchecked(" ", 1, 1);
x_4 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_4, 0, x_3);
x_5 = l_Lean_PrettyPrinter_Formatter_pushWhitespace___redArg(x_4, x_1, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_ppHardSpace_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_ppHardSpace_formatter___redArg(x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_ppHardSpace_formatter___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_ppHardSpace_formatter___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_ppHardSpace_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_ppHardSpace_formatter(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_ppSpace_formatter___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PrettyPrinter_Formatter_pushLine___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_ppSpace_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Formatter_pushLine___redArg(x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_ppSpace_formatter___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_ppSpace_formatter___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_ppSpace_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_ppSpace_formatter(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_ppLine_formatter___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_mk_string_unchecked("\n", 1, 1);
x_4 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_4, 0, x_3);
x_5 = l_Lean_PrettyPrinter_Formatter_pushWhitespace___redArg(x_4, x_1, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_ppLine_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_ppLine_formatter___redArg(x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_ppLine_formatter___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_ppLine_formatter___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_ppLine_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_ppLine_formatter(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_ppRealFill_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Formatter_fill(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_ppRealGroup_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Formatter_group(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_ppIndent_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = l_Lean_PrettyPrinter_Formatter_indent(x_1, x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_ppDedent_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = lean_ctor_get(x_4, 2);
lean_inc(x_7);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_to_int(x_8);
x_10 = l_Std_Format_getIndent(x_7);
lean_dec(x_7);
x_11 = lean_nat_to_int(x_10);
x_12 = lean_int_sub(x_9, x_11);
lean_dec(x_11);
lean_dec(x_9);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = l_Lean_PrettyPrinter_Formatter_indent(x_1, x_13, x_2, x_3, x_4, x_5, x_6);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_ppAllowUngrouped_formatter___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; uint8_t x_15; 
x_3 = lean_st_ref_take(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
x_8 = lean_ctor_get_uint8(x_4, sizeof(void*)*3);
x_9 = lean_ctor_get_uint8(x_4, sizeof(void*)*3 + 1);
x_10 = lean_box(0);
x_11 = lean_ctor_get(x_4, 2);
lean_inc(x_11);
lean_dec(x_4);
x_12 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_12, 0, x_6);
lean_ctor_set(x_12, 1, x_7);
lean_ctor_set(x_12, 2, x_11);
lean_ctor_set_uint8(x_12, sizeof(void*)*3, x_8);
lean_ctor_set_uint8(x_12, sizeof(void*)*3 + 1, x_9);
x_13 = lean_unbox(x_10);
lean_ctor_set_uint8(x_12, sizeof(void*)*3 + 2, x_13);
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
LEAN_EXPORT lean_object* l_Lean_ppAllowUngrouped_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_ppAllowUngrouped_formatter___redArg(x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_ppAllowUngrouped_formatter___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_ppAllowUngrouped_formatter___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_ppAllowUngrouped_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_ppAllowUngrouped_formatter(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_ppDedentIfGrouped_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_PrettyPrinter_Formatter_concat(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_st_ref_get(x_3, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get_uint8(x_10, sizeof(void*)*3 + 1);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_st_ref_take(x_3, x_12);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; lean_object* x_22; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
x_19 = lean_ctor_get_uint8(x_15, sizeof(void*)*3);
x_20 = lean_ctor_get_uint8(x_15, sizeof(void*)*3 + 1);
x_21 = lean_ctor_get_uint8(x_15, sizeof(void*)*3 + 2);
x_32 = lean_ctor_get(x_15, 2);
lean_inc(x_32);
lean_dec(x_15);
x_33 = lean_array_get_size(x_32);
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_nat_sub(x_33, x_34);
x_36 = lean_nat_dec_lt(x_35, x_33);
lean_dec(x_33);
if (x_36 == 0)
{
lean_dec(x_35);
lean_free_object(x_13);
lean_dec(x_4);
x_22 = x_32;
goto block_31;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_37 = lean_ctor_get(x_4, 2);
lean_inc(x_37);
lean_dec(x_4);
x_38 = l_Std_Format_getIndent(x_37);
lean_dec(x_37);
x_39 = lean_array_fget(x_32, x_35);
x_40 = lean_box(0);
x_41 = lean_array_fset(x_32, x_35, x_40);
x_42 = lean_unsigned_to_nat(0u);
x_43 = lean_nat_to_int(x_42);
x_44 = lean_nat_to_int(x_38);
x_45 = lean_int_sub(x_43, x_44);
lean_dec(x_44);
lean_dec(x_43);
lean_ctor_set_tag(x_13, 4);
lean_ctor_set(x_13, 1, x_39);
lean_ctor_set(x_13, 0, x_45);
x_46 = lean_array_fset(x_41, x_35, x_13);
lean_dec(x_35);
x_22 = x_46;
goto block_31;
}
block_31:
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_23, 0, x_17);
lean_ctor_set(x_23, 1, x_18);
lean_ctor_set(x_23, 2, x_22);
lean_ctor_set_uint8(x_23, sizeof(void*)*3, x_19);
lean_ctor_set_uint8(x_23, sizeof(void*)*3 + 1, x_20);
lean_ctor_set_uint8(x_23, sizeof(void*)*3 + 2, x_21);
x_24 = lean_st_ref_set(x_3, x_23, x_16);
lean_dec(x_3);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
x_27 = lean_box(0);
lean_ctor_set(x_24, 0, x_27);
return x_24;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_24, 1);
lean_inc(x_28);
lean_dec(x_24);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; lean_object* x_54; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_47 = lean_ctor_get(x_13, 0);
x_48 = lean_ctor_get(x_13, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_13);
x_49 = lean_ctor_get(x_47, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
x_51 = lean_ctor_get_uint8(x_47, sizeof(void*)*3);
x_52 = lean_ctor_get_uint8(x_47, sizeof(void*)*3 + 1);
x_53 = lean_ctor_get_uint8(x_47, sizeof(void*)*3 + 2);
x_62 = lean_ctor_get(x_47, 2);
lean_inc(x_62);
lean_dec(x_47);
x_63 = lean_array_get_size(x_62);
x_64 = lean_unsigned_to_nat(1u);
x_65 = lean_nat_sub(x_63, x_64);
x_66 = lean_nat_dec_lt(x_65, x_63);
lean_dec(x_63);
if (x_66 == 0)
{
lean_dec(x_65);
lean_dec(x_4);
x_54 = x_62;
goto block_61;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_67 = lean_ctor_get(x_4, 2);
lean_inc(x_67);
lean_dec(x_4);
x_68 = l_Std_Format_getIndent(x_67);
lean_dec(x_67);
x_69 = lean_array_fget(x_62, x_65);
x_70 = lean_box(0);
x_71 = lean_array_fset(x_62, x_65, x_70);
x_72 = lean_unsigned_to_nat(0u);
x_73 = lean_nat_to_int(x_72);
x_74 = lean_nat_to_int(x_68);
x_75 = lean_int_sub(x_73, x_74);
lean_dec(x_74);
lean_dec(x_73);
x_76 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_69);
x_77 = lean_array_fset(x_71, x_65, x_76);
lean_dec(x_65);
x_54 = x_77;
goto block_61;
}
block_61:
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_55 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_55, 0, x_49);
lean_ctor_set(x_55, 1, x_50);
lean_ctor_set(x_55, 2, x_54);
lean_ctor_set_uint8(x_55, sizeof(void*)*3, x_51);
lean_ctor_set_uint8(x_55, sizeof(void*)*3 + 1, x_52);
lean_ctor_set_uint8(x_55, sizeof(void*)*3 + 2, x_53);
x_56 = lean_st_ref_set(x_3, x_55, x_48);
lean_dec(x_3);
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
x_59 = lean_box(0);
if (lean_is_scalar(x_58)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_58;
}
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_57);
return x_60;
}
}
}
else
{
uint8_t x_78; 
lean_dec(x_4);
lean_dec(x_3);
x_78 = !lean_is_exclusive(x_9);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_9, 0);
lean_dec(x_79);
x_80 = lean_box(0);
lean_ctor_set(x_9, 0, x_80);
return x_9;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_9, 1);
lean_inc(x_81);
lean_dec(x_9);
x_82 = lean_box(0);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_81);
return x_83;
}
}
}
else
{
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ppHardLineUnlessUngrouped_formatter___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_st_ref_get(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get_uint8(x_4, sizeof(void*)*3 + 1);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = l_Lean_ppLine_formatter___redArg(x_1, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_dec(x_3);
x_9 = l_Lean_PrettyPrinter_Formatter_pushLine___redArg(x_1, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ppHardLineUnlessUngrouped_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_ppHardLineUnlessUngrouped_formatter___redArg(x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_ppHardLineUnlessUngrouped_formatter___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_ppHardLineUnlessUngrouped_formatter___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_ppHardLineUnlessUngrouped_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_ppHardLineUnlessUngrouped_formatter(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppHardSpace_parenthesizer___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Parenthesizer_skip_parenthesizer___redArg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppHardSpace_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Parenthesizer_skip_parenthesizer___redArg(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppHardSpace_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_ppHardSpace_parenthesizer(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppSpace_parenthesizer___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Parenthesizer_skip_parenthesizer___redArg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppSpace_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Parenthesizer_skip_parenthesizer___redArg(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppSpace_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_ppSpace_parenthesizer(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppLine_parenthesizer___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Parenthesizer_skip_parenthesizer___redArg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppLine_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Parenthesizer_skip_parenthesizer___redArg(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppLine_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_ppLine_parenthesizer(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppGroup_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_closure((void*)(l_Lean_ppIndent_formatter), 6, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = l_Lean_PrettyPrinter_Formatter_fill(x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppRealFill_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppIndent_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppGroup_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppRealGroup_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppDedent_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppAllowUngrouped_parenthesizer___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Parenthesizer_skip_parenthesizer___redArg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppAllowUngrouped_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Parenthesizer_skip_parenthesizer___redArg(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppAllowUngrouped_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_ppAllowUngrouped_parenthesizer(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppDedentIfGrouped_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppHardLineUnlessUngrouped_parenthesizer___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Parenthesizer_skip_parenthesizer___redArg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppHardLineUnlessUngrouped_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Parenthesizer_skip_parenthesizer___redArg(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ppHardLineUnlessUngrouped_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_ppHardLineUnlessUngrouped_parenthesizer(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Parser_termRegister__parser__alias_x28Kind_x3a_x3d___x29____________() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("termRegister_parser_alias(Kind:=_)______", 40, 40);
lean_inc(x_2);
lean_inc(x_1);
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
x_5 = lean_unsigned_to_nat(1022u);
x_6 = lean_mk_string_unchecked("andthen", 7, 7);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = lean_mk_string_unchecked("register_parser_alias ", 22, 22);
x_9 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_mk_string_unchecked("optional", 8, 8);
x_11 = l_Lean_Name_mkStr1(x_10);
x_12 = lean_mk_string_unchecked("group", 5, 5);
x_13 = l_Lean_Name_mkStr1(x_12);
x_14 = lean_mk_string_unchecked("(", 1, 1);
x_15 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_mk_string_unchecked("kind", 4, 4);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_18, 0, x_16);
x_19 = lean_unbox(x_17);
lean_ctor_set_uint8(x_18, sizeof(void*)*1, x_19);
lean_inc(x_7);
x_20 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_20, 0, x_7);
lean_ctor_set(x_20, 1, x_15);
lean_ctor_set(x_20, 2, x_18);
x_21 = lean_mk_string_unchecked(" := ", 4, 4);
x_22 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_22, 0, x_21);
lean_inc(x_7);
x_23 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_23, 0, x_7);
lean_ctor_set(x_23, 1, x_20);
lean_ctor_set(x_23, 2, x_22);
x_24 = lean_mk_string_unchecked("term", 4, 4);
x_25 = l_Lean_Name_mkStr1(x_24);
x_26 = lean_unsigned_to_nat(0u);
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
lean_inc(x_27);
lean_inc(x_7);
x_28 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_28, 0, x_7);
lean_ctor_set(x_28, 1, x_23);
lean_ctor_set(x_28, 2, x_27);
x_29 = lean_mk_string_unchecked(") ", 2, 2);
x_30 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_30, 0, x_29);
lean_inc(x_7);
x_31 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_31, 0, x_7);
lean_ctor_set(x_31, 1, x_28);
lean_ctor_set(x_31, 2, x_30);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_13);
lean_ctor_set(x_32, 1, x_31);
lean_inc(x_11);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_11);
lean_ctor_set(x_33, 1, x_32);
lean_inc(x_7);
x_34 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_34, 0, x_7);
lean_ctor_set(x_34, 1, x_9);
lean_ctor_set(x_34, 2, x_33);
x_35 = lean_mk_string_unchecked("strLit", 6, 6);
x_36 = l_Lean_Name_mkStr3(x_1, x_2, x_35);
x_37 = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = lean_mk_string_unchecked("ppSpace", 7, 7);
x_39 = l_Lean_Name_mkStr1(x_38);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_39);
lean_inc(x_40);
lean_inc(x_7);
x_41 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_41, 0, x_7);
lean_ctor_set(x_41, 1, x_37);
lean_ctor_set(x_41, 2, x_40);
lean_inc(x_11);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_11);
lean_ctor_set(x_42, 1, x_41);
lean_inc(x_7);
x_43 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_43, 0, x_7);
lean_ctor_set(x_43, 1, x_34);
lean_ctor_set(x_43, 2, x_42);
x_44 = lean_mk_string_unchecked("ident", 5, 5);
x_45 = l_Lean_Name_mkStr1(x_44);
x_46 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_46, 0, x_45);
lean_inc(x_7);
x_47 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_47, 0, x_7);
lean_ctor_set(x_47, 1, x_43);
lean_ctor_set(x_47, 2, x_46);
x_48 = lean_mk_string_unchecked("colGt", 5, 5);
x_49 = l_Lean_Name_mkStr1(x_48);
x_50 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_50, 0, x_49);
lean_inc(x_7);
x_51 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_51, 0, x_7);
lean_ctor_set(x_51, 1, x_40);
lean_ctor_set(x_51, 2, x_50);
lean_inc(x_7);
x_52 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_52, 0, x_7);
lean_ctor_set(x_52, 1, x_51);
lean_ctor_set(x_52, 2, x_27);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_11);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_54, 0, x_7);
lean_ctor_set(x_54, 1, x_47);
lean_ctor_set(x_54, 2, x_53);
x_55 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_55, 0, x_4);
lean_ctor_set(x_55, 1, x_5);
lean_ctor_set(x_55, 2, x_54);
return x_55;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser___aux__Lean__Parser__Extra______macroRules__Lean__Parser__termRegister__parser__alias_x28Kind_x3a_x3d___x29______________1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_314; lean_object* x_315; uint8_t x_316; 
x_9 = lean_mk_string_unchecked("Lean", 4, 4);
x_88 = lean_mk_string_unchecked("Parser", 6, 6);
x_314 = lean_mk_string_unchecked("termRegister_parser_alias(Kind:=_)______", 40, 40);
lean_inc(x_88);
lean_inc(x_9);
x_315 = l_Lean_Name_mkStr3(x_9, x_88, x_314);
lean_inc(x_1);
x_316 = l_Lean_Syntax_isOfKind(x_1, x_315);
lean_dec(x_315);
if (x_316 == 0)
{
lean_object* x_317; lean_object* x_318; 
lean_dec(x_88);
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_317 = lean_box(1);
x_318 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_318, 0, x_317);
lean_ctor_set(x_318, 1, x_3);
return x_318;
}
else
{
lean_object* x_319; lean_object* x_320; uint8_t x_321; 
x_319 = lean_unsigned_to_nat(1u);
x_320 = l_Lean_Syntax_getArg(x_1, x_319);
x_321 = l_Lean_Syntax_isNone(x_320);
if (x_321 == 0)
{
uint8_t x_322; 
lean_inc(x_320);
x_322 = l_Lean_Syntax_matchesNull(x_320, x_319);
if (x_322 == 0)
{
lean_object* x_323; lean_object* x_324; 
lean_dec(x_320);
lean_dec(x_88);
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_323 = lean_box(1);
x_324 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_324, 0, x_323);
lean_ctor_set(x_324, 1, x_3);
return x_324;
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; uint8_t x_329; 
x_325 = lean_unsigned_to_nat(0u);
x_326 = l_Lean_Syntax_getArg(x_320, x_325);
lean_dec(x_320);
x_327 = lean_mk_string_unchecked("group", 5, 5);
x_328 = l_Lean_Name_mkStr1(x_327);
lean_inc(x_326);
x_329 = l_Lean_Syntax_isOfKind(x_326, x_328);
lean_dec(x_328);
if (x_329 == 0)
{
lean_object* x_330; lean_object* x_331; 
lean_dec(x_326);
lean_dec(x_88);
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_330 = lean_box(1);
x_331 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_331, 0, x_330);
lean_ctor_set(x_331, 1, x_3);
return x_331;
}
else
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; 
x_332 = lean_unsigned_to_nat(3u);
x_333 = l_Lean_Syntax_getArg(x_326, x_332);
lean_dec(x_326);
x_334 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_334, 0, x_333);
x_299 = x_334;
x_300 = x_2;
x_301 = x_3;
goto block_313;
}
}
}
else
{
lean_object* x_335; 
lean_dec(x_320);
x_335 = lean_box(0);
x_299 = x_335;
x_300 = x_2;
x_301 = x_3;
goto block_313;
}
}
block_8:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_mk_string_unchecked("expected non-overloaded constant name", 37, 37);
x_7 = l_Lean_Macro_throwError___redArg(x_6, x_4, x_5);
lean_dec(x_4);
return x_7;
}
block_87:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_inc(x_13);
lean_inc(x_28);
x_37 = l_Lean_Syntax_node1(x_28, x_13, x_36);
lean_inc(x_30);
lean_inc(x_28);
x_38 = l_Lean_Syntax_node2(x_28, x_30, x_10, x_37);
x_39 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_28);
x_40 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_40, 0, x_28);
lean_ctor_set(x_40, 1, x_39);
lean_inc(x_28);
x_41 = l_Lean_Syntax_node5(x_28, x_26, x_23, x_17, x_20, x_38, x_40);
lean_inc(x_21);
lean_inc(x_35);
lean_inc(x_13);
lean_inc(x_28);
x_42 = l_Lean_Syntax_node5(x_28, x_13, x_35, x_33, x_21, x_15, x_41);
lean_inc(x_30);
lean_inc(x_28);
x_43 = l_Lean_Syntax_node2(x_28, x_30, x_27, x_42);
lean_inc(x_18);
lean_inc(x_28);
x_44 = l_Lean_Syntax_node1(x_28, x_18, x_43);
x_45 = l_Array_mkArray0(lean_box(0));
lean_inc(x_13);
lean_inc(x_28);
x_46 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_46, 0, x_28);
lean_ctor_set(x_46, 1, x_13);
lean_ctor_set(x_46, 2, x_45);
lean_inc(x_46);
lean_inc(x_14);
lean_inc(x_28);
x_47 = l_Lean_Syntax_node2(x_28, x_14, x_44, x_46);
x_48 = lean_mk_string_unchecked("PrettyPrinter.Formatter.registerAlias", 37, 37);
x_49 = l_String_toSubstring_x27(x_48);
x_50 = lean_mk_string_unchecked("PrettyPrinter", 13, 13);
x_51 = lean_mk_string_unchecked("Formatter", 9, 9);
lean_inc(x_22);
lean_inc(x_51);
lean_inc(x_50);
x_52 = l_Lean_Name_mkStr3(x_50, x_51, x_22);
lean_inc(x_29);
lean_inc(x_24);
x_53 = l_Lean_addMacroScope(x_24, x_52, x_29);
lean_inc(x_22);
lean_inc(x_50);
lean_inc(x_9);
x_54 = l_Lean_Name_mkStr4(x_9, x_50, x_51, x_22);
lean_inc(x_31);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_31);
lean_inc(x_34);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_34);
lean_inc(x_28);
x_57 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_57, 0, x_28);
lean_ctor_set(x_57, 1, x_49);
lean_ctor_set(x_57, 2, x_53);
lean_ctor_set(x_57, 3, x_56);
x_58 = lean_mk_string_unchecked("formatter", 9, 9);
x_59 = l_Lean_Name_mkStr1(x_58);
lean_inc(x_11);
x_60 = l_Lean_Name_append(x_11, x_59);
x_61 = l_Lean_mkIdentFrom(x_21, x_60, x_16);
lean_inc(x_35);
lean_inc(x_13);
lean_inc(x_28);
x_62 = l_Lean_Syntax_node2(x_28, x_13, x_35, x_61);
lean_inc(x_30);
lean_inc(x_28);
x_63 = l_Lean_Syntax_node2(x_28, x_30, x_57, x_62);
lean_inc(x_18);
lean_inc(x_28);
x_64 = l_Lean_Syntax_node1(x_28, x_18, x_63);
lean_inc(x_46);
lean_inc(x_14);
lean_inc(x_28);
x_65 = l_Lean_Syntax_node2(x_28, x_14, x_64, x_46);
x_66 = lean_mk_string_unchecked("PrettyPrinter.Parenthesizer.registerAlias", 41, 41);
x_67 = l_String_toSubstring_x27(x_66);
x_68 = lean_mk_string_unchecked("Parenthesizer", 13, 13);
lean_inc(x_22);
lean_inc(x_68);
lean_inc(x_50);
x_69 = l_Lean_Name_mkStr3(x_50, x_68, x_22);
x_70 = l_Lean_addMacroScope(x_24, x_69, x_29);
x_71 = l_Lean_Name_mkStr4(x_9, x_50, x_68, x_22);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_31);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_34);
lean_inc(x_28);
x_74 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_74, 0, x_28);
lean_ctor_set(x_74, 1, x_67);
lean_ctor_set(x_74, 2, x_70);
lean_ctor_set(x_74, 3, x_73);
x_75 = lean_mk_string_unchecked("parenthesizer", 13, 13);
x_76 = l_Lean_Name_mkStr1(x_75);
x_77 = l_Lean_Name_append(x_11, x_76);
x_78 = l_Lean_mkIdentFrom(x_21, x_77, x_16);
lean_dec(x_21);
lean_inc(x_13);
lean_inc(x_28);
x_79 = l_Lean_Syntax_node2(x_28, x_13, x_35, x_78);
lean_inc(x_28);
x_80 = l_Lean_Syntax_node2(x_28, x_30, x_74, x_79);
lean_inc(x_28);
x_81 = l_Lean_Syntax_node1(x_28, x_18, x_80);
lean_inc(x_28);
x_82 = l_Lean_Syntax_node2(x_28, x_14, x_81, x_46);
lean_inc(x_28);
x_83 = l_Lean_Syntax_node3(x_28, x_13, x_47, x_65, x_82);
lean_inc(x_28);
x_84 = l_Lean_Syntax_node1(x_28, x_32, x_83);
x_85 = l_Lean_Syntax_node2(x_28, x_25, x_12, x_84);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_19);
return x_86;
}
block_149:
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_114 = lean_mk_string_unchecked("namedArgument", 13, 13);
lean_inc(x_111);
lean_inc(x_88);
lean_inc(x_9);
x_115 = l_Lean_Name_mkStr4(x_9, x_88, x_111, x_114);
x_116 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_96);
x_117 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_117, 0, x_96);
lean_ctor_set(x_117, 1, x_116);
x_118 = lean_mk_string_unchecked("kind\?", 5, 5);
lean_inc(x_118);
x_119 = l_String_toSubstring_x27(x_118);
x_120 = l_Lean_Name_mkStr1(x_118);
lean_inc(x_99);
lean_inc(x_90);
x_121 = l_Lean_addMacroScope(x_90, x_120, x_99);
lean_inc(x_106);
lean_inc(x_96);
x_122 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_122, 0, x_96);
lean_ctor_set(x_122, 1, x_119);
lean_ctor_set(x_122, 2, x_121);
lean_ctor_set(x_122, 3, x_106);
x_123 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_96);
x_124 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_124, 0, x_96);
lean_ctor_set(x_124, 1, x_123);
x_125 = lean_mk_string_unchecked("some", 4, 4);
lean_inc(x_125);
x_126 = l_String_toSubstring_x27(x_125);
lean_inc(x_125);
x_127 = l_Lean_Name_mkStr1(x_125);
lean_inc(x_99);
lean_inc(x_90);
x_128 = l_Lean_addMacroScope(x_90, x_127, x_99);
x_129 = lean_mk_string_unchecked("Option", 6, 6);
x_130 = l_Lean_Name_mkStr2(x_129, x_125);
lean_inc(x_101);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_101);
lean_inc(x_106);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_106);
lean_inc(x_96);
x_133 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_133, 0, x_96);
lean_ctor_set(x_133, 1, x_126);
lean_ctor_set(x_133, 2, x_128);
lean_ctor_set(x_133, 3, x_132);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_134; 
lean_inc(x_104);
lean_inc(x_101);
x_134 = l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(x_101, x_104);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; 
lean_dec(x_111);
lean_dec(x_92);
lean_dec(x_88);
x_135 = l_Lean_quoteNameMk(x_104);
x_10 = x_133;
x_11 = x_91;
x_12 = x_93;
x_13 = x_94;
x_14 = x_97;
x_15 = x_113;
x_16 = x_98;
x_17 = x_122;
x_18 = x_103;
x_19 = x_107;
x_20 = x_124;
x_21 = x_110;
x_22 = x_112;
x_23 = x_117;
x_24 = x_90;
x_25 = x_89;
x_26 = x_115;
x_27 = x_95;
x_28 = x_96;
x_29 = x_99;
x_30 = x_100;
x_31 = x_101;
x_32 = x_102;
x_33 = x_105;
x_34 = x_106;
x_35 = x_109;
x_36 = x_135;
goto block_87;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_dec(x_104);
x_136 = lean_ctor_get(x_134, 0);
lean_inc(x_136);
lean_dec(x_134);
x_137 = lean_mk_string_unchecked("quotedName", 10, 10);
lean_inc(x_9);
x_138 = l_Lean_Name_mkStr4(x_9, x_88, x_111, x_137);
x_139 = lean_mk_string_unchecked(".", 1, 1);
x_140 = l_String_intercalate(x_139, x_136);
lean_dec(x_139);
x_141 = lean_string_append(x_92, x_140);
lean_dec(x_140);
x_142 = lean_box(2);
x_143 = l_Lean_Syntax_mkNameLit(x_141, x_142);
x_144 = lean_unsigned_to_nat(1u);
x_145 = lean_mk_empty_array_with_capacity(x_144);
x_146 = lean_array_push(x_145, x_143);
x_147 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_147, 0, x_142);
lean_ctor_set(x_147, 1, x_138);
lean_ctor_set(x_147, 2, x_146);
x_10 = x_133;
x_11 = x_91;
x_12 = x_93;
x_13 = x_94;
x_14 = x_97;
x_15 = x_113;
x_16 = x_98;
x_17 = x_122;
x_18 = x_103;
x_19 = x_107;
x_20 = x_124;
x_21 = x_110;
x_22 = x_112;
x_23 = x_117;
x_24 = x_90;
x_25 = x_89;
x_26 = x_115;
x_27 = x_95;
x_28 = x_96;
x_29 = x_99;
x_30 = x_100;
x_31 = x_101;
x_32 = x_102;
x_33 = x_105;
x_34 = x_106;
x_35 = x_109;
x_36 = x_147;
goto block_87;
}
}
else
{
lean_object* x_148; 
lean_dec(x_111);
lean_dec(x_104);
lean_dec(x_92);
lean_dec(x_88);
x_148 = lean_ctor_get(x_108, 0);
lean_inc(x_148);
lean_dec(x_108);
x_10 = x_133;
x_11 = x_91;
x_12 = x_93;
x_13 = x_94;
x_14 = x_97;
x_15 = x_113;
x_16 = x_98;
x_17 = x_122;
x_18 = x_103;
x_19 = x_107;
x_20 = x_124;
x_21 = x_110;
x_22 = x_112;
x_23 = x_117;
x_24 = x_90;
x_25 = x_89;
x_26 = x_115;
x_27 = x_95;
x_28 = x_96;
x_29 = x_99;
x_30 = x_100;
x_31 = x_101;
x_32 = x_102;
x_33 = x_105;
x_34 = x_106;
x_35 = x_109;
x_36 = x_148;
goto block_87;
}
}
block_223:
{
lean_object* x_159; lean_object* x_160; uint8_t x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_159 = lean_ctor_get(x_151, 5);
lean_inc(x_159);
x_160 = lean_box(0);
x_161 = lean_unbox(x_160);
x_162 = l_Lean_SourceInfo_fromRef(x_159, x_161);
lean_dec(x_159);
x_163 = lean_ctor_get(x_151, 2);
lean_inc(x_163);
x_164 = lean_ctor_get(x_151, 1);
lean_inc(x_164);
lean_dec(x_151);
x_165 = lean_mk_string_unchecked("Term", 4, 4);
x_166 = lean_mk_string_unchecked("do", 2, 2);
lean_inc(x_166);
lean_inc(x_165);
lean_inc(x_88);
lean_inc(x_9);
x_167 = l_Lean_Name_mkStr4(x_9, x_88, x_165, x_166);
lean_inc(x_162);
x_168 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_168, 0, x_162);
lean_ctor_set(x_168, 1, x_166);
x_169 = lean_mk_string_unchecked("doSeqIndent", 11, 11);
lean_inc(x_165);
lean_inc(x_88);
lean_inc(x_9);
x_170 = l_Lean_Name_mkStr4(x_9, x_88, x_165, x_169);
x_171 = lean_mk_string_unchecked("null", 4, 4);
x_172 = l_Lean_Name_mkStr1(x_171);
x_173 = lean_mk_string_unchecked("doSeqItem", 9, 9);
lean_inc(x_165);
lean_inc(x_88);
lean_inc(x_9);
x_174 = l_Lean_Name_mkStr4(x_9, x_88, x_165, x_173);
x_175 = lean_mk_string_unchecked("doExpr", 6, 6);
lean_inc(x_165);
lean_inc(x_88);
lean_inc(x_9);
x_176 = l_Lean_Name_mkStr4(x_9, x_88, x_165, x_175);
x_177 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_165);
lean_inc(x_88);
lean_inc(x_9);
x_178 = l_Lean_Name_mkStr4(x_9, x_88, x_165, x_177);
x_179 = lean_mk_string_unchecked("Parser.registerAlias", 20, 20);
x_180 = l_String_toSubstring_x27(x_179);
x_181 = lean_mk_string_unchecked("registerAlias", 13, 13);
lean_inc(x_181);
lean_inc(x_88);
x_182 = l_Lean_Name_mkStr2(x_88, x_181);
lean_inc(x_163);
lean_inc(x_164);
x_183 = l_Lean_addMacroScope(x_164, x_182, x_163);
lean_inc(x_181);
lean_inc(x_88);
lean_inc(x_9);
x_184 = l_Lean_Name_mkStr3(x_9, x_88, x_181);
lean_inc(x_157);
lean_inc(x_184);
x_185 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_157);
x_186 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_186, 0, x_184);
x_187 = lean_box(0);
x_188 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_188, 0, x_186);
lean_ctor_set(x_188, 1, x_187);
x_189 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_189, 0, x_185);
lean_ctor_set(x_189, 1, x_188);
lean_inc(x_162);
x_190 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_190, 0, x_162);
lean_ctor_set(x_190, 1, x_180);
lean_ctor_set(x_190, 2, x_183);
lean_ctor_set(x_190, 3, x_189);
x_191 = lean_mk_string_unchecked("doubleQuotedName", 16, 16);
lean_inc(x_165);
lean_inc(x_88);
lean_inc(x_9);
x_192 = l_Lean_Name_mkStr4(x_9, x_88, x_165, x_191);
x_193 = lean_mk_string_unchecked("`", 1, 1);
lean_inc(x_193);
lean_inc(x_162);
x_194 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_194, 0, x_162);
lean_ctor_set(x_194, 1, x_193);
lean_inc(x_156);
lean_inc(x_194);
lean_inc(x_162);
x_195 = l_Lean_Syntax_node3(x_162, x_192, x_194, x_194, x_156);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_196; uint8_t x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; uint8_t x_220; 
x_196 = lean_box(0);
x_197 = lean_unbox(x_160);
x_198 = l_Lean_SourceInfo_fromRef(x_196, x_197);
x_199 = lean_mk_string_unchecked("choice", 6, 6);
x_200 = l_Lean_Name_mkStr1(x_199);
x_201 = lean_mk_string_unchecked("term{}", 6, 6);
x_202 = l_Lean_Name_mkStr1(x_201);
x_203 = lean_mk_string_unchecked("{", 1, 1);
lean_inc(x_198);
x_204 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_204, 0, x_198);
lean_ctor_set(x_204, 1, x_203);
x_205 = lean_mk_string_unchecked("}", 1, 1);
lean_inc(x_198);
x_206 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_206, 0, x_198);
lean_ctor_set(x_206, 1, x_205);
lean_inc(x_206);
lean_inc(x_204);
lean_inc(x_198);
x_207 = l_Lean_Syntax_node2(x_198, x_202, x_204, x_206);
x_208 = lean_mk_string_unchecked("structInst", 10, 10);
lean_inc(x_165);
lean_inc(x_88);
lean_inc(x_9);
x_209 = l_Lean_Name_mkStr4(x_9, x_88, x_165, x_208);
x_210 = l_Array_mkArray0(lean_box(0));
lean_inc(x_172);
lean_inc(x_198);
x_211 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_211, 0, x_198);
lean_ctor_set(x_211, 1, x_172);
lean_ctor_set(x_211, 2, x_210);
x_212 = lean_mk_string_unchecked("structInstFields", 16, 16);
lean_inc(x_165);
lean_inc(x_88);
lean_inc(x_9);
x_213 = l_Lean_Name_mkStr4(x_9, x_88, x_165, x_212);
lean_inc(x_211);
lean_inc(x_198);
x_214 = l_Lean_Syntax_node1(x_198, x_213, x_211);
x_215 = lean_mk_string_unchecked("optEllipsis", 11, 11);
lean_inc(x_165);
lean_inc(x_88);
lean_inc(x_9);
x_216 = l_Lean_Name_mkStr4(x_9, x_88, x_165, x_215);
lean_inc(x_211);
lean_inc(x_198);
x_217 = l_Lean_Syntax_node1(x_198, x_216, x_211);
lean_inc(x_211);
lean_inc(x_198);
x_218 = l_Lean_Syntax_node6(x_198, x_209, x_204, x_211, x_214, x_217, x_211, x_206);
x_219 = l_Lean_Syntax_node2(x_198, x_200, x_207, x_218);
x_220 = lean_unbox(x_160);
x_89 = x_167;
x_90 = x_164;
x_91 = x_152;
x_92 = x_193;
x_93 = x_168;
x_94 = x_172;
x_95 = x_190;
x_96 = x_162;
x_97 = x_174;
x_98 = x_220;
x_99 = x_163;
x_100 = x_178;
x_101 = x_157;
x_102 = x_170;
x_103 = x_176;
x_104 = x_150;
x_105 = x_195;
x_106 = x_187;
x_107 = x_154;
x_108 = x_155;
x_109 = x_158;
x_110 = x_156;
x_111 = x_165;
x_112 = x_181;
x_113 = x_219;
goto block_149;
}
else
{
lean_object* x_221; uint8_t x_222; 
x_221 = lean_ctor_get(x_153, 0);
lean_inc(x_221);
lean_dec(x_153);
x_222 = lean_unbox(x_160);
x_89 = x_167;
x_90 = x_164;
x_91 = x_152;
x_92 = x_193;
x_93 = x_168;
x_94 = x_172;
x_95 = x_190;
x_96 = x_162;
x_97 = x_174;
x_98 = x_222;
x_99 = x_163;
x_100 = x_178;
x_101 = x_157;
x_102 = x_170;
x_103 = x_176;
x_104 = x_150;
x_105 = x_195;
x_106 = x_187;
x_107 = x_154;
x_108 = x_155;
x_109 = x_158;
x_110 = x_156;
x_111 = x_165;
x_112 = x_181;
x_113 = x_221;
goto block_149;
}
}
block_284:
{
lean_object* x_231; lean_object* x_232; 
x_231 = l_Lean_Syntax_getId(x_229);
lean_dec(x_229);
lean_inc(x_224);
lean_inc(x_231);
x_232 = l_Lean_Macro_resolveGlobalName(x_231, x_224, x_226);
if (lean_obj_tag(x_232) == 0)
{
lean_object* x_233; 
x_233 = lean_ctor_get(x_232, 0);
lean_inc(x_233);
if (lean_obj_tag(x_233) == 0)
{
lean_object* x_234; 
lean_dec(x_231);
lean_dec(x_230);
lean_dec(x_228);
lean_dec(x_227);
lean_dec(x_225);
lean_dec(x_88);
lean_dec(x_9);
x_234 = lean_ctor_get(x_232, 1);
lean_inc(x_234);
lean_dec(x_232);
x_4 = x_224;
x_5 = x_234;
goto block_8;
}
else
{
lean_object* x_235; lean_object* x_236; 
x_235 = lean_ctor_get(x_233, 0);
lean_inc(x_235);
x_236 = lean_ctor_get(x_235, 1);
lean_inc(x_236);
if (lean_obj_tag(x_236) == 0)
{
lean_object* x_237; 
x_237 = lean_ctor_get(x_233, 1);
lean_inc(x_237);
lean_dec(x_233);
if (lean_obj_tag(x_237) == 0)
{
if (lean_obj_tag(x_230) == 0)
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_238 = lean_ctor_get(x_232, 1);
lean_inc(x_238);
lean_dec(x_232);
x_239 = lean_ctor_get(x_235, 0);
lean_inc(x_239);
lean_dec(x_235);
lean_inc(x_231);
x_240 = l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(x_236, x_231);
if (lean_obj_tag(x_240) == 0)
{
lean_object* x_241; 
lean_inc(x_231);
x_241 = l_Lean_quoteNameMk(x_231);
x_150 = x_239;
x_151 = x_224;
x_152 = x_231;
x_153 = x_225;
x_154 = x_238;
x_155 = x_228;
x_156 = x_227;
x_157 = x_236;
x_158 = x_241;
goto block_223;
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; 
x_242 = lean_ctor_get(x_240, 0);
lean_inc(x_242);
lean_dec(x_240);
x_243 = lean_mk_string_unchecked("Term", 4, 4);
x_244 = lean_mk_string_unchecked("quotedName", 10, 10);
lean_inc(x_88);
lean_inc(x_9);
x_245 = l_Lean_Name_mkStr4(x_9, x_88, x_243, x_244);
x_246 = lean_mk_string_unchecked("`", 1, 1);
x_247 = lean_mk_string_unchecked(".", 1, 1);
x_248 = l_String_intercalate(x_247, x_242);
lean_dec(x_247);
x_249 = lean_string_append(x_246, x_248);
lean_dec(x_248);
x_250 = lean_box(2);
x_251 = l_Lean_Syntax_mkNameLit(x_249, x_250);
x_252 = lean_unsigned_to_nat(1u);
x_253 = lean_mk_empty_array_with_capacity(x_252);
x_254 = lean_array_push(x_253, x_251);
x_255 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_255, 0, x_250);
lean_ctor_set(x_255, 1, x_245);
lean_ctor_set(x_255, 2, x_254);
x_150 = x_239;
x_151 = x_224;
x_152 = x_231;
x_153 = x_225;
x_154 = x_238;
x_155 = x_228;
x_156 = x_227;
x_157 = x_236;
x_158 = x_255;
goto block_223;
}
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; 
x_256 = lean_ctor_get(x_232, 1);
lean_inc(x_256);
lean_dec(x_232);
x_257 = lean_ctor_get(x_235, 0);
lean_inc(x_257);
lean_dec(x_235);
x_258 = lean_ctor_get(x_230, 0);
lean_inc(x_258);
lean_dec(x_230);
x_259 = l_Lean_TSyntax_getString(x_258);
lean_dec(x_258);
x_260 = lean_box(0);
x_261 = l_Lean_Name_str___override(x_260, x_259);
lean_inc(x_261);
x_262 = l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(x_236, x_261);
if (lean_obj_tag(x_262) == 0)
{
lean_object* x_263; 
x_263 = l_Lean_quoteNameMk(x_261);
x_150 = x_257;
x_151 = x_224;
x_152 = x_231;
x_153 = x_225;
x_154 = x_256;
x_155 = x_228;
x_156 = x_227;
x_157 = x_236;
x_158 = x_263;
goto block_223;
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; 
lean_dec(x_261);
x_264 = lean_ctor_get(x_262, 0);
lean_inc(x_264);
lean_dec(x_262);
x_265 = lean_mk_string_unchecked("Term", 4, 4);
x_266 = lean_mk_string_unchecked("quotedName", 10, 10);
lean_inc(x_88);
lean_inc(x_9);
x_267 = l_Lean_Name_mkStr4(x_9, x_88, x_265, x_266);
x_268 = lean_mk_string_unchecked("`", 1, 1);
x_269 = lean_mk_string_unchecked(".", 1, 1);
x_270 = l_String_intercalate(x_269, x_264);
lean_dec(x_269);
x_271 = lean_string_append(x_268, x_270);
lean_dec(x_270);
x_272 = lean_box(2);
x_273 = l_Lean_Syntax_mkNameLit(x_271, x_272);
x_274 = lean_unsigned_to_nat(1u);
x_275 = lean_mk_empty_array_with_capacity(x_274);
x_276 = lean_array_push(x_275, x_273);
x_277 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_277, 0, x_272);
lean_ctor_set(x_277, 1, x_267);
lean_ctor_set(x_277, 2, x_276);
x_150 = x_257;
x_151 = x_224;
x_152 = x_231;
x_153 = x_225;
x_154 = x_256;
x_155 = x_228;
x_156 = x_227;
x_157 = x_236;
x_158 = x_277;
goto block_223;
}
}
}
else
{
lean_object* x_278; 
lean_dec(x_237);
lean_dec(x_235);
lean_dec(x_231);
lean_dec(x_230);
lean_dec(x_228);
lean_dec(x_227);
lean_dec(x_225);
lean_dec(x_88);
lean_dec(x_9);
x_278 = lean_ctor_get(x_232, 1);
lean_inc(x_278);
lean_dec(x_232);
x_4 = x_224;
x_5 = x_278;
goto block_8;
}
}
else
{
lean_object* x_279; 
lean_dec(x_236);
lean_dec(x_235);
lean_dec(x_233);
lean_dec(x_231);
lean_dec(x_230);
lean_dec(x_228);
lean_dec(x_227);
lean_dec(x_225);
lean_dec(x_88);
lean_dec(x_9);
x_279 = lean_ctor_get(x_232, 1);
lean_inc(x_279);
lean_dec(x_232);
x_4 = x_224;
x_5 = x_279;
goto block_8;
}
}
}
else
{
uint8_t x_280; 
lean_dec(x_231);
lean_dec(x_230);
lean_dec(x_228);
lean_dec(x_227);
lean_dec(x_225);
lean_dec(x_224);
lean_dec(x_88);
lean_dec(x_9);
x_280 = !lean_is_exclusive(x_232);
if (x_280 == 0)
{
return x_232;
}
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; 
x_281 = lean_ctor_get(x_232, 0);
x_282 = lean_ctor_get(x_232, 1);
lean_inc(x_282);
lean_inc(x_281);
lean_dec(x_232);
x_283 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_283, 0, x_281);
lean_ctor_set(x_283, 1, x_282);
return x_283;
}
}
}
block_298:
{
lean_object* x_292; lean_object* x_293; 
x_292 = l_Lean_Syntax_getArg(x_1, x_288);
lean_dec(x_1);
x_293 = l_Lean_Syntax_getOptional_x3f(x_286);
lean_dec(x_286);
if (lean_obj_tag(x_293) == 0)
{
lean_object* x_294; 
x_294 = lean_box(0);
x_224 = x_285;
x_225 = x_291;
x_226 = x_287;
x_227 = x_290;
x_228 = x_289;
x_229 = x_292;
x_230 = x_294;
goto block_284;
}
else
{
uint8_t x_295; 
x_295 = !lean_is_exclusive(x_293);
if (x_295 == 0)
{
x_224 = x_285;
x_225 = x_291;
x_226 = x_287;
x_227 = x_290;
x_228 = x_289;
x_229 = x_292;
x_230 = x_293;
goto block_284;
}
else
{
lean_object* x_296; lean_object* x_297; 
x_296 = lean_ctor_get(x_293, 0);
lean_inc(x_296);
lean_dec(x_293);
x_297 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_297, 0, x_296);
x_224 = x_285;
x_225 = x_291;
x_226 = x_287;
x_227 = x_290;
x_228 = x_289;
x_229 = x_292;
x_230 = x_297;
goto block_284;
}
}
}
block_313:
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; 
x_302 = lean_unsigned_to_nat(2u);
x_303 = l_Lean_Syntax_getArg(x_1, x_302);
x_304 = lean_unsigned_to_nat(3u);
x_305 = l_Lean_Syntax_getArg(x_1, x_304);
x_306 = lean_unsigned_to_nat(4u);
x_307 = l_Lean_Syntax_getArg(x_1, x_306);
x_308 = l_Lean_Syntax_getOptional_x3f(x_307);
lean_dec(x_307);
if (lean_obj_tag(x_308) == 0)
{
lean_object* x_309; 
x_309 = lean_box(0);
x_285 = x_300;
x_286 = x_303;
x_287 = x_301;
x_288 = x_304;
x_289 = x_299;
x_290 = x_305;
x_291 = x_309;
goto block_298;
}
else
{
uint8_t x_310; 
x_310 = !lean_is_exclusive(x_308);
if (x_310 == 0)
{
x_285 = x_300;
x_286 = x_303;
x_287 = x_301;
x_288 = x_304;
x_289 = x_299;
x_290 = x_305;
x_291 = x_308;
goto block_298;
}
else
{
lean_object* x_311; lean_object* x_312; 
x_311 = lean_ctor_get(x_308, 0);
lean_inc(x_311);
lean_dec(x_308);
x_312 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_312, 0, x_311);
x_285 = x_300;
x_286 = x_303;
x_287 = x_301;
x_288 = x_304;
x_289 = x_299;
x_290 = x_305;
x_291 = x_312;
goto block_298;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initFn___lam__0____x40_Lean_Parser_Extra___hyg_1755_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Parenthesizer_skip_parenthesizer___redArg(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initFn___lam__2____x40_Lean_Parser_Extra___hyg_1755_(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initFn___lam__3____x40_Lean_Parser_Extra___hyg_1755_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initFn___lam__8____x40_Lean_Parser_Extra___hyg_1755_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Formatter_fill(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initFn___lam__5____x40_Lean_Parser_Extra___hyg_1755_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Formatter_group(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initFn___lam__7____x40_Lean_Parser_Extra___hyg_1755_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Formatter_pushLine___redArg(x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initFn___lam__6____x40_Lean_Parser_Extra___hyg_1755_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_node(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_1755_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_199; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; uint8_t x_225; lean_object* x_226; lean_object* x_244; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_initFn___lam__0____x40_Lean_Parser_Extra___hyg_1755____boxed), 5, 0);
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_initFn___lam__2____x40_Lean_Parser_Extra___hyg_1755____boxed), 1, 0);
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_initFn___lam__3____x40_Lean_Parser_Extra___hyg_1755_), 6, 0);
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_initFn___lam__8____x40_Lean_Parser_Extra___hyg_1755_), 6, 0);
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_initFn___lam__5____x40_Lean_Parser_Extra___hyg_1755_), 6, 0);
x_7 = lean_alloc_closure((void*)(l_Lean_Parser_initFn___lam__7____x40_Lean_Parser_Extra___hyg_1755____boxed), 5, 0);
x_8 = lean_mk_string_unchecked("patternIgnore", 13, 13);
lean_inc(x_8);
x_9 = l_Lean_Name_mkStr1(x_8);
lean_inc(x_9);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_initFn___lam__6____x40_Lean_Parser_Extra___hyg_1755_), 2, 1);
lean_closure_set(x_10, 0, x_9);
x_11 = lean_mk_string_unchecked("Lean", 4, 4);
x_12 = lean_mk_string_unchecked("Parser", 6, 6);
lean_inc(x_12);
lean_inc(x_11);
x_140 = l_Lean_Name_mkStr3(x_11, x_12, x_8);
x_141 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_141, 0, x_10);
lean_inc(x_140);
x_142 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_142, 0, x_140);
x_143 = lean_box(0);
x_221 = lean_unsigned_to_nat(1u);
x_222 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_222, 0, x_221);
x_223 = lean_box(0);
x_224 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_224, 0, x_143);
lean_ctor_set(x_224, 1, x_222);
x_225 = lean_unbox(x_223);
lean_ctor_set_uint8(x_224, sizeof(void*)*2, x_225);
lean_inc(x_9);
x_244 = l_Lean_Parser_registerAlias(x_9, x_140, x_141, x_142, x_224, x_1);
if (lean_obj_tag(x_244) == 0)
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_245 = lean_ctor_get(x_244, 1);
lean_inc(x_245);
lean_dec(x_244);
x_246 = lean_alloc_closure((void*)(l_Lean_Parser_patternIgnore_formatter), 6, 0);
x_247 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_247, 0, x_246);
lean_inc(x_9);
x_248 = l_Lean_PrettyPrinter_Formatter_registerAlias(x_9, x_247, x_245);
if (lean_obj_tag(x_248) == 0)
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_249 = lean_ctor_get(x_248, 1);
lean_inc(x_249);
lean_dec(x_248);
x_250 = lean_alloc_closure((void*)(l_Lean_Parser_patternIgnore_parenthesizer), 6, 0);
x_251 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_251, 0, x_250);
x_252 = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(x_9, x_251, x_249);
x_226 = x_252;
goto block_243;
}
else
{
lean_dec(x_9);
x_226 = x_248;
goto block_243;
}
}
else
{
lean_dec(x_9);
x_226 = x_244;
goto block_243;
}
block_29:
{
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_mk_string_unchecked("ppHardLineUnlessUngrouped", 25, 25);
lean_inc(x_17);
x_18 = l_Lean_Name_mkStr1(x_17);
x_19 = l_Lean_Name_mkStr3(x_11, x_12, x_17);
lean_inc(x_19);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
lean_inc(x_18);
x_21 = l_Lean_Parser_registerAlias(x_18, x_19, x_14, x_20, x_13, x_16);
lean_dec(x_13);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_alloc_closure((void*)(l_Lean_ppHardLineUnlessUngrouped_formatter___boxed), 5, 0);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
lean_inc(x_18);
x_25 = l_Lean_PrettyPrinter_Formatter_registerAlias(x_18, x_24, x_22);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_2);
x_28 = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(x_18, x_27, x_26);
return x_28;
}
else
{
lean_dec(x_18);
lean_dec(x_2);
return x_25;
}
}
else
{
lean_dec(x_18);
lean_dec(x_2);
return x_21;
}
}
else
{
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_2);
return x_15;
}
}
block_46:
{
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_mk_string_unchecked("ppAllowUngrouped", 16, 16);
lean_inc(x_34);
x_35 = l_Lean_Name_mkStr1(x_34);
lean_inc(x_12);
lean_inc(x_11);
x_36 = l_Lean_Name_mkStr3(x_11, x_12, x_34);
lean_inc(x_36);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
lean_inc(x_31);
lean_inc(x_35);
x_38 = l_Lean_Parser_registerAlias(x_35, x_36, x_31, x_37, x_30, x_33);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_alloc_closure((void*)(l_Lean_ppAllowUngrouped_formatter___boxed), 5, 0);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_40);
lean_inc(x_35);
x_42 = l_Lean_PrettyPrinter_Formatter_registerAlias(x_35, x_41, x_39);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
lean_inc(x_2);
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_2);
x_45 = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(x_35, x_44, x_43);
x_13 = x_30;
x_14 = x_31;
x_15 = x_45;
goto block_29;
}
else
{
lean_dec(x_35);
x_13 = x_30;
x_14 = x_31;
x_15 = x_42;
goto block_29;
}
}
else
{
lean_dec(x_35);
x_13 = x_30;
x_14 = x_31;
x_15 = x_38;
goto block_29;
}
}
else
{
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_2);
return x_32;
}
}
block_65:
{
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
lean_dec(x_50);
x_52 = lean_mk_string_unchecked("ppDedentIfGrouped", 17, 17);
lean_inc(x_52);
x_53 = l_Lean_Name_mkStr1(x_52);
lean_inc(x_12);
lean_inc(x_11);
x_54 = l_Lean_Name_mkStr3(x_11, x_12, x_52);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_3);
lean_inc(x_54);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_54);
lean_inc(x_53);
x_57 = l_Lean_Parser_registerAlias(x_53, x_54, x_55, x_56, x_48, x_51);
lean_dec(x_48);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec(x_57);
x_59 = lean_alloc_closure((void*)(l_Lean_ppDedentIfGrouped_formatter), 6, 0);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_59);
lean_inc(x_53);
x_61 = l_Lean_PrettyPrinter_Formatter_registerAlias(x_53, x_60, x_58);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
lean_dec(x_61);
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_4);
x_64 = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(x_53, x_63, x_62);
x_30 = x_47;
x_31 = x_49;
x_32 = x_64;
goto block_46;
}
else
{
lean_dec(x_53);
lean_dec(x_4);
x_30 = x_47;
x_31 = x_49;
x_32 = x_61;
goto block_46;
}
}
else
{
lean_dec(x_53);
lean_dec(x_4);
x_30 = x_47;
x_31 = x_49;
x_32 = x_57;
goto block_46;
}
}
else
{
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_50;
}
}
block_84:
{
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
lean_dec(x_69);
x_71 = lean_mk_string_unchecked("ppDedent", 8, 8);
lean_inc(x_71);
x_72 = l_Lean_Name_mkStr1(x_71);
lean_inc(x_12);
lean_inc(x_11);
x_73 = l_Lean_Name_mkStr3(x_11, x_12, x_71);
lean_inc(x_3);
x_74 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_74, 0, x_3);
lean_inc(x_73);
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_73);
lean_inc(x_72);
x_76 = l_Lean_Parser_registerAlias(x_72, x_73, x_74, x_75, x_67, x_70);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_77 = lean_ctor_get(x_76, 1);
lean_inc(x_77);
lean_dec(x_76);
x_78 = lean_alloc_closure((void*)(l_Lean_ppDedent_formatter), 6, 0);
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_78);
lean_inc(x_72);
x_80 = l_Lean_PrettyPrinter_Formatter_registerAlias(x_72, x_79, x_77);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
lean_dec(x_80);
lean_inc(x_4);
x_82 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_82, 0, x_4);
x_83 = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(x_72, x_82, x_81);
x_47 = x_66;
x_48 = x_67;
x_49 = x_68;
x_50 = x_83;
goto block_65;
}
else
{
lean_dec(x_72);
x_47 = x_66;
x_48 = x_67;
x_49 = x_68;
x_50 = x_80;
goto block_65;
}
}
else
{
lean_dec(x_72);
x_47 = x_66;
x_48 = x_67;
x_49 = x_68;
x_50 = x_76;
goto block_65;
}
}
else
{
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_69;
}
}
block_103:
{
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_89 = lean_ctor_get(x_88, 1);
lean_inc(x_89);
lean_dec(x_88);
x_90 = lean_mk_string_unchecked("ppIndent", 8, 8);
lean_inc(x_90);
x_91 = l_Lean_Name_mkStr1(x_90);
lean_inc(x_12);
lean_inc(x_11);
x_92 = l_Lean_Name_mkStr3(x_11, x_12, x_90);
lean_inc(x_3);
x_93 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_93, 0, x_3);
lean_inc(x_92);
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_92);
lean_inc(x_91);
x_95 = l_Lean_Parser_registerAlias(x_91, x_92, x_93, x_94, x_86, x_89);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_96 = lean_ctor_get(x_95, 1);
lean_inc(x_96);
lean_dec(x_95);
x_97 = lean_alloc_closure((void*)(l_Lean_ppIndent_formatter), 6, 0);
x_98 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_98, 0, x_97);
lean_inc(x_91);
x_99 = l_Lean_PrettyPrinter_Formatter_registerAlias(x_91, x_98, x_96);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
lean_dec(x_99);
lean_inc(x_4);
x_101 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_101, 0, x_4);
x_102 = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(x_91, x_101, x_100);
x_66 = x_85;
x_67 = x_86;
x_68 = x_87;
x_69 = x_102;
goto block_84;
}
else
{
lean_dec(x_91);
x_66 = x_85;
x_67 = x_86;
x_68 = x_87;
x_69 = x_99;
goto block_84;
}
}
else
{
lean_dec(x_91);
x_66 = x_85;
x_67 = x_86;
x_68 = x_87;
x_69 = x_95;
goto block_84;
}
}
else
{
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_88;
}
}
block_121:
{
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_108 = lean_ctor_get(x_107, 1);
lean_inc(x_108);
lean_dec(x_107);
x_109 = lean_mk_string_unchecked("ppRealFill", 10, 10);
lean_inc(x_109);
x_110 = l_Lean_Name_mkStr1(x_109);
lean_inc(x_12);
lean_inc(x_11);
x_111 = l_Lean_Name_mkStr3(x_11, x_12, x_109);
lean_inc(x_3);
x_112 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_112, 0, x_3);
lean_inc(x_111);
x_113 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_113, 0, x_111);
lean_inc(x_110);
x_114 = l_Lean_Parser_registerAlias(x_110, x_111, x_112, x_113, x_105, x_108);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_114, 1);
lean_inc(x_115);
lean_dec(x_114);
x_116 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_116, 0, x_5);
lean_inc(x_110);
x_117 = l_Lean_PrettyPrinter_Formatter_registerAlias(x_110, x_116, x_115);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_117, 1);
lean_inc(x_118);
lean_dec(x_117);
lean_inc(x_4);
x_119 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_119, 0, x_4);
x_120 = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(x_110, x_119, x_118);
x_85 = x_104;
x_86 = x_105;
x_87 = x_106;
x_88 = x_120;
goto block_103;
}
else
{
lean_dec(x_110);
x_85 = x_104;
x_86 = x_105;
x_87 = x_106;
x_88 = x_117;
goto block_103;
}
}
else
{
lean_dec(x_110);
lean_dec(x_5);
x_85 = x_104;
x_86 = x_105;
x_87 = x_106;
x_88 = x_114;
goto block_103;
}
}
else
{
lean_dec(x_106);
lean_dec(x_105);
lean_dec(x_104);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_107;
}
}
block_139:
{
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_126 = lean_ctor_get(x_125, 1);
lean_inc(x_126);
lean_dec(x_125);
x_127 = lean_mk_string_unchecked("ppRealGroup", 11, 11);
lean_inc(x_127);
x_128 = l_Lean_Name_mkStr1(x_127);
lean_inc(x_12);
lean_inc(x_11);
x_129 = l_Lean_Name_mkStr3(x_11, x_12, x_127);
lean_inc(x_3);
x_130 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_130, 0, x_3);
lean_inc(x_129);
x_131 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_131, 0, x_129);
lean_inc(x_128);
x_132 = l_Lean_Parser_registerAlias(x_128, x_129, x_130, x_131, x_123, x_126);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_132, 1);
lean_inc(x_133);
lean_dec(x_132);
x_134 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_134, 0, x_6);
lean_inc(x_128);
x_135 = l_Lean_PrettyPrinter_Formatter_registerAlias(x_128, x_134, x_133);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_135, 1);
lean_inc(x_136);
lean_dec(x_135);
lean_inc(x_4);
x_137 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_137, 0, x_4);
x_138 = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(x_128, x_137, x_136);
x_104 = x_122;
x_105 = x_123;
x_106 = x_124;
x_107 = x_138;
goto block_121;
}
else
{
lean_dec(x_128);
x_104 = x_122;
x_105 = x_123;
x_106 = x_124;
x_107 = x_135;
goto block_121;
}
}
else
{
lean_dec(x_128);
lean_dec(x_6);
x_104 = x_122;
x_105 = x_123;
x_106 = x_124;
x_107 = x_132;
goto block_121;
}
}
else
{
lean_dec(x_124);
lean_dec(x_123);
lean_dec(x_122);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_125;
}
}
block_165:
{
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; uint8_t x_156; lean_object* x_157; 
x_147 = lean_ctor_get(x_146, 1);
lean_inc(x_147);
lean_dec(x_146);
x_148 = lean_mk_string_unchecked("ppGroup", 7, 7);
lean_inc(x_148);
x_149 = l_Lean_Name_mkStr1(x_148);
lean_inc(x_12);
lean_inc(x_11);
x_150 = l_Lean_Name_mkStr3(x_11, x_12, x_148);
lean_inc(x_3);
x_151 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_151, 0, x_3);
lean_inc(x_150);
x_152 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_152, 0, x_150);
x_153 = lean_box(0);
x_154 = lean_box(0);
x_155 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_155, 0, x_143);
lean_ctor_set(x_155, 1, x_153);
x_156 = lean_unbox(x_154);
lean_ctor_set_uint8(x_155, sizeof(void*)*2, x_156);
lean_inc(x_149);
x_157 = l_Lean_Parser_registerAlias(x_149, x_150, x_151, x_152, x_155, x_147);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_158 = lean_ctor_get(x_157, 1);
lean_inc(x_158);
lean_dec(x_157);
x_159 = lean_alloc_closure((void*)(l_Lean_Parser_ppGroup_formatter), 6, 0);
x_160 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_160, 0, x_159);
lean_inc(x_149);
x_161 = l_Lean_PrettyPrinter_Formatter_registerAlias(x_149, x_160, x_158);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_162 = lean_ctor_get(x_161, 1);
lean_inc(x_162);
lean_dec(x_161);
lean_inc(x_4);
x_163 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_163, 0, x_4);
x_164 = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(x_149, x_163, x_162);
x_122 = x_144;
x_123 = x_155;
x_124 = x_145;
x_125 = x_164;
goto block_139;
}
else
{
lean_dec(x_149);
x_122 = x_144;
x_123 = x_155;
x_124 = x_145;
x_125 = x_161;
goto block_139;
}
}
else
{
lean_dec(x_149);
x_122 = x_144;
x_123 = x_155;
x_124 = x_145;
x_125 = x_157;
goto block_139;
}
}
else
{
lean_dec(x_145);
lean_dec(x_144);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_146;
}
}
block_182:
{
if (lean_obj_tag(x_168) == 0)
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_169 = lean_ctor_get(x_168, 1);
lean_inc(x_169);
lean_dec(x_168);
x_170 = lean_mk_string_unchecked("ppLine", 6, 6);
lean_inc(x_170);
x_171 = l_Lean_Name_mkStr1(x_170);
lean_inc(x_12);
lean_inc(x_11);
x_172 = l_Lean_Name_mkStr3(x_11, x_12, x_170);
lean_inc(x_172);
x_173 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_173, 0, x_172);
lean_inc(x_167);
lean_inc(x_171);
x_174 = l_Lean_Parser_registerAlias(x_171, x_172, x_167, x_173, x_166, x_169);
if (lean_obj_tag(x_174) == 0)
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_175 = lean_ctor_get(x_174, 1);
lean_inc(x_175);
lean_dec(x_174);
x_176 = lean_alloc_closure((void*)(l_Lean_ppLine_formatter___boxed), 5, 0);
x_177 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_177, 0, x_176);
lean_inc(x_171);
x_178 = l_Lean_PrettyPrinter_Formatter_registerAlias(x_171, x_177, x_175);
if (lean_obj_tag(x_178) == 0)
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_179 = lean_ctor_get(x_178, 1);
lean_inc(x_179);
lean_dec(x_178);
lean_inc(x_2);
x_180 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_180, 0, x_2);
x_181 = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(x_171, x_180, x_179);
x_144 = x_166;
x_145 = x_167;
x_146 = x_181;
goto block_165;
}
else
{
lean_dec(x_171);
x_144 = x_166;
x_145 = x_167;
x_146 = x_178;
goto block_165;
}
}
else
{
lean_dec(x_171);
x_144 = x_166;
x_145 = x_167;
x_146 = x_174;
goto block_165;
}
}
else
{
lean_dec(x_167);
lean_dec(x_166);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_168;
}
}
block_198:
{
if (lean_obj_tag(x_185) == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_186 = lean_ctor_get(x_185, 1);
lean_inc(x_186);
lean_dec(x_185);
x_187 = lean_mk_string_unchecked("ppSpace", 7, 7);
lean_inc(x_187);
x_188 = l_Lean_Name_mkStr1(x_187);
lean_inc(x_12);
lean_inc(x_11);
x_189 = l_Lean_Name_mkStr3(x_11, x_12, x_187);
lean_inc(x_189);
x_190 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_190, 0, x_189);
lean_inc(x_184);
lean_inc(x_188);
x_191 = l_Lean_Parser_registerAlias(x_188, x_189, x_184, x_190, x_183, x_186);
if (lean_obj_tag(x_191) == 0)
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_192 = lean_ctor_get(x_191, 1);
lean_inc(x_192);
lean_dec(x_191);
x_193 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_193, 0, x_7);
lean_inc(x_188);
x_194 = l_Lean_PrettyPrinter_Formatter_registerAlias(x_188, x_193, x_192);
if (lean_obj_tag(x_194) == 0)
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_195 = lean_ctor_get(x_194, 1);
lean_inc(x_195);
lean_dec(x_194);
lean_inc(x_2);
x_196 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_196, 0, x_2);
x_197 = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(x_188, x_196, x_195);
x_166 = x_183;
x_167 = x_184;
x_168 = x_197;
goto block_182;
}
else
{
lean_dec(x_188);
x_166 = x_183;
x_167 = x_184;
x_168 = x_194;
goto block_182;
}
}
else
{
lean_dec(x_188);
lean_dec(x_7);
x_166 = x_183;
x_167 = x_184;
x_168 = x_191;
goto block_182;
}
}
else
{
lean_dec(x_184);
lean_dec(x_183);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_185;
}
}
block_220:
{
if (lean_obj_tag(x_199) == 0)
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; uint8_t x_211; lean_object* x_212; 
x_200 = lean_ctor_get(x_199, 1);
lean_inc(x_200);
lean_dec(x_199);
x_201 = lean_mk_string_unchecked("ppHardSpace", 11, 11);
lean_inc(x_201);
x_202 = l_Lean_Name_mkStr1(x_201);
lean_inc(x_12);
lean_inc(x_11);
x_203 = l_Lean_Name_mkStr3(x_11, x_12, x_201);
x_204 = l_Lean_Parser_skip;
x_205 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_205, 0, x_204);
lean_inc(x_203);
x_206 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_206, 0, x_203);
x_207 = lean_unsigned_to_nat(0u);
x_208 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_208, 0, x_207);
x_209 = lean_box(1);
x_210 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_210, 0, x_143);
lean_ctor_set(x_210, 1, x_208);
x_211 = lean_unbox(x_209);
lean_ctor_set_uint8(x_210, sizeof(void*)*2, x_211);
lean_inc(x_205);
lean_inc(x_202);
x_212 = l_Lean_Parser_registerAlias(x_202, x_203, x_205, x_206, x_210, x_200);
if (lean_obj_tag(x_212) == 0)
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_213 = lean_ctor_get(x_212, 1);
lean_inc(x_213);
lean_dec(x_212);
x_214 = lean_alloc_closure((void*)(l_Lean_ppHardSpace_formatter___boxed), 5, 0);
x_215 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_215, 0, x_214);
lean_inc(x_202);
x_216 = l_Lean_PrettyPrinter_Formatter_registerAlias(x_202, x_215, x_213);
if (lean_obj_tag(x_216) == 0)
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_217 = lean_ctor_get(x_216, 1);
lean_inc(x_217);
lean_dec(x_216);
lean_inc(x_2);
x_218 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_218, 0, x_2);
x_219 = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(x_202, x_218, x_217);
x_183 = x_210;
x_184 = x_205;
x_185 = x_219;
goto block_198;
}
else
{
lean_dec(x_202);
x_183 = x_210;
x_184 = x_205;
x_185 = x_216;
goto block_198;
}
}
else
{
lean_dec(x_202);
x_183 = x_210;
x_184 = x_205;
x_185 = x_212;
goto block_198;
}
}
else
{
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_199;
}
}
block_243:
{
if (lean_obj_tag(x_226) == 0)
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_227 = lean_ctor_get(x_226, 1);
lean_inc(x_227);
lean_dec(x_226);
x_228 = lean_mk_string_unchecked("group", 5, 5);
lean_inc(x_228);
x_229 = l_Lean_Name_mkStr1(x_228);
lean_inc(x_229);
x_230 = lean_alloc_closure((void*)(l_Lean_Parser_initFn___lam__6____x40_Lean_Parser_Extra___hyg_1755_), 2, 1);
lean_closure_set(x_230, 0, x_229);
lean_inc(x_12);
lean_inc(x_11);
x_231 = l_Lean_Name_mkStr3(x_11, x_12, x_228);
x_232 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_232, 0, x_230);
lean_inc(x_231);
x_233 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_233, 0, x_231);
lean_inc(x_229);
x_234 = l_Lean_Parser_registerAlias(x_229, x_231, x_232, x_233, x_224, x_227);
lean_dec(x_224);
if (lean_obj_tag(x_234) == 0)
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_235 = lean_ctor_get(x_234, 1);
lean_inc(x_235);
lean_dec(x_234);
x_236 = lean_alloc_closure((void*)(l_Lean_Parser_group_formatter), 6, 0);
x_237 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_237, 0, x_236);
lean_inc(x_229);
x_238 = l_Lean_PrettyPrinter_Formatter_registerAlias(x_229, x_237, x_235);
if (lean_obj_tag(x_238) == 0)
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; 
x_239 = lean_ctor_get(x_238, 1);
lean_inc(x_239);
lean_dec(x_238);
x_240 = lean_alloc_closure((void*)(l_Lean_Parser_group_parenthesizer), 6, 0);
x_241 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_241, 0, x_240);
x_242 = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(x_229, x_241, x_239);
x_199 = x_242;
goto block_220;
}
else
{
lean_dec(x_229);
x_199 = x_238;
goto block_220;
}
}
else
{
lean_dec(x_229);
x_199 = x_234;
goto block_220;
}
}
else
{
lean_dec(x_224);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_226;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initFn___lam__0____x40_Lean_Parser_Extra___hyg_1755____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_initFn___lam__0____x40_Lean_Parser_Extra___hyg_1755_(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initFn___lam__2____x40_Lean_Parser_Extra___hyg_1755____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_initFn___lam__2____x40_Lean_Parser_Extra___hyg_1755_(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initFn___lam__7____x40_Lean_Parser_Extra___hyg_1755____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_initFn___lam__7____x40_Lean_Parser_Extra___hyg_1755_(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* initialize_Lean_Parser_Extension(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_PrettyPrinter_Parenthesizer(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_PrettyPrinter_Formatter(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Parser_Extra(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Parser_Extension(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_PrettyPrinter_Parenthesizer(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_PrettyPrinter_Formatter(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
if (builtin) {res = l___regBuiltin_Lean_Parser_antiquotNestedExpr_formatter__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_antiquotNestedExpr_parenthesizer__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_optional_docString__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_many_docString__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_many1_docString__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_ident_docString__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_ident = _init_l_Lean_Parser_ident();
lean_mark_persistent(l_Lean_Parser_ident);
l_Lean_Parser_identWithPartialTrailingDot = _init_l_Lean_Parser_identWithPartialTrailingDot();
lean_mark_persistent(l_Lean_Parser_identWithPartialTrailingDot);
l_Lean_Parser_rawIdent = _init_l_Lean_Parser_rawIdent();
lean_mark_persistent(l_Lean_Parser_rawIdent);
if (builtin) {res = l___regBuiltin_Lean_Parser_hygieneInfo_docString__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_hygieneInfo = _init_l_Lean_Parser_hygieneInfo();
lean_mark_persistent(l_Lean_Parser_hygieneInfo);
if (builtin) {res = l___regBuiltin_Lean_Parser_numLit_docString__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_numLit = _init_l_Lean_Parser_numLit();
lean_mark_persistent(l_Lean_Parser_numLit);
if (builtin) {res = l___regBuiltin_Lean_Parser_scientificLit_docString__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_scientificLit = _init_l_Lean_Parser_scientificLit();
lean_mark_persistent(l_Lean_Parser_scientificLit);
if (builtin) {res = l___regBuiltin_Lean_Parser_strLit_docString__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_strLit = _init_l_Lean_Parser_strLit();
lean_mark_persistent(l_Lean_Parser_strLit);
if (builtin) {res = l___regBuiltin_Lean_Parser_charLit_docString__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_charLit = _init_l_Lean_Parser_charLit();
lean_mark_persistent(l_Lean_Parser_charLit);
if (builtin) {res = l___regBuiltin_Lean_Parser_nameLit_docString__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_nameLit = _init_l_Lean_Parser_nameLit();
lean_mark_persistent(l_Lean_Parser_nameLit);
if (builtin) {res = l___regBuiltin_Lean_Parser_group_docString__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_many1Indent_docString__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_manyIndent_docString__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_patternIgnore_docString__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_ppHardSpace_docString__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_ppHardSpace = _init_l_Lean_Parser_ppHardSpace();
lean_mark_persistent(l_Lean_Parser_ppHardSpace);
if (builtin) {res = l___regBuiltin_Lean_Parser_ppSpace_docString__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_ppSpace = _init_l_Lean_Parser_ppSpace();
lean_mark_persistent(l_Lean_Parser_ppSpace);
if (builtin) {res = l___regBuiltin_Lean_Parser_ppLine_docString__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_ppLine = _init_l_Lean_Parser_ppLine();
lean_mark_persistent(l_Lean_Parser_ppLine);
if (builtin) {res = l___regBuiltin_Lean_Parser_ppRealFill_docString__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_ppRealGroup_docString__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_ppIndent_docString__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_ppGroup_docString__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_ppDedent_docString__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_ppAllowUngrouped_docString__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_ppAllowUngrouped = _init_l_Lean_Parser_ppAllowUngrouped();
lean_mark_persistent(l_Lean_Parser_ppAllowUngrouped);
if (builtin) {res = l___regBuiltin_Lean_Parser_ppDedentIfGrouped_docString__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_ppHardLineUnlessUngrouped_docString__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_ppHardLineUnlessUngrouped = _init_l_Lean_Parser_ppHardLineUnlessUngrouped();
lean_mark_persistent(l_Lean_Parser_ppHardLineUnlessUngrouped);
l_Lean_Parser_termRegister__parser__alias_x28Kind_x3a_x3d___x29____________ = _init_l_Lean_Parser_termRegister__parser__alias_x28Kind_x3a_x3d___x29____________();
lean_mark_persistent(l_Lean_Parser_termRegister__parser__alias_x28Kind_x3a_x3d___x29____________);
if (builtin) {res = l_Lean_Parser_initFn____x40_Lean_Parser_Extra___hyg_1755_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
