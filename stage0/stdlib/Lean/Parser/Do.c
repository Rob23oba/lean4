// Lean compiler output
// Module: Lean.Parser.Do
// Imports: Lean.Parser.Term
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
LEAN_EXPORT lean_object* l_Lean_Parser_Term_elseIf;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doIf;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_optMetaFalse;
lean_object* l_Lean_Parser_many1_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_liftMethod__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doIfLet_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doTry__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doSeq;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_do__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_letIdDeclNoBinders;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doMatchExpr_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_notFollowedBy_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_optional_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doContinue_declRange__1(lean_object*);
lean_object* l_Lean_Parser_Term_letDecl_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doNested_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doLet_formatter__1(lean_object*);
lean_object* l_Lean_Parser_registerBuiltinParserAttribute(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doCatch;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_termUnless_parenthesizer__1(lean_object*);
lean_object* l_Lean_Parser_Term_matchAlts_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doLetElse_formatter__1(lean_object*);
extern lean_object* l_Lean_Parser_pushNone;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doLetMetaExpr_parenthesizer__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doIfLet;
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkAntiquot_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doSeqItem;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_termReturn_parenthesizer__1(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_termTry_declRange__1(lean_object*);
lean_object* l_Lean_Parser_Term_letPatDecl_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_matchExprAlts_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doBreak_formatter__1(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_orelse_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doUnless_declRange__1(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_fill(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doDebugAssert;
lean_object* l_Lean_Parser_Term_optIdent_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doLetMetaExpr;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doLetArrow_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doFor_declRange__1(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doIf_parenthesizer__1(lean_object*);
lean_object* l_Lean_Parser_Term_haveDecl_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_doElemParser_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_elseIf_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doSeqItem_parenthesizer___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doHave__1(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doDebugAssert_parenthesizer__1(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_many_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doCatchMatch;
lean_object* l_Lean_Parser_leadingNode(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doReassignArrow_formatter__1(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doLetRec_formatter__1(lean_object*);
lean_object* l_Lean_Parser_categoryParser(lean_object*, lean_object*);
lean_object* l_Lean_Parser_termParser_formatter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doCatchMatch_formatter__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doIfCond;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doReturn_docString__1(lean_object*);
lean_object* l_Lean_Parser_group_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doAssert;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doLetArrow;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_termBeforeDo_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_termUnless_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doIfLetBind_formatter__1(lean_object*);
extern lean_object* l_Lean_Parser_Term_matchExprPat;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doUnless_formatter___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doIfLetBind_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_termBeforeDo_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_interpolatedStr(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doDbgTrace_parenthesizer__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doReturn;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doFor__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doBreak;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doReassign;
lean_object* l_Lean_Parser_optional(lean_object*);
lean_object* l_Lean_Parser_termParser_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_nonReservedSymbol(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doReassignArrow_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doReturn_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doLet_declRange__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doCatch_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doMatch_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_termTry_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doNested_declRange__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doSeqIndent;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_leftArrow;
lean_object* l_Lean_Parser_darrow_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_elseIf_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doFinally_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doIfLetPure_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_termReturn;
lean_object* l_Lean_Parser_orelse(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_initFn____x40_Lean_Parser_Do___hyg_228_(lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doPatDecl_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doReassignArrow_parenthesizer__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doContinue_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doSeqIndent_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doLetArrow_declRange__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doExpr_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doLet_parenthesizer__1(lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_notFollowedByRedefinedTermToken_parenthesizer___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doMatchAlts_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_motive_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doReassign_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doIfLetBind_parenthesizer__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doMatch;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doNested_parenthesizer__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doMatchAlts;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doReturn_parenthesizer__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doLetExpr_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doAssert_docString__1(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doLetMetaExpr_formatter__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doNested;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doIfLetPure_formatter__1(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doIfProp_formatter__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doIf_formatter___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doBreak_declRange__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doIfCond_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_termUnless_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doNested_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doContinue__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doIdDecl_formatter___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doIfLetPure_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doLetArrow_formatter__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doBreak_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_termReturn_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_termTry__1(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doContinue_parenthesizer__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doSeqIndent_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_matchAlts_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_letIdDeclNoBinders_parenthesizer__1(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_skip_parenthesizer___redArg(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doLetArrow_parenthesizer__1(lean_object*);
lean_object* l_Lean_Parser_mkAntiquot_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doIf_formatter__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doCatchMatch_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doExpr;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doLetElse_declRange__1(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_do_formatter__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doDebugAssert_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doReassign_parenthesizer__1(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doReassignArrow_declRange__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doTry_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_do;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_termFor_parenthesizer__1(lean_object*);
lean_object* l_Lean_Parser_withPosition(lean_object*);
lean_object* l_Lean_Parser_Term_binderIdent_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doLetRec_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doLetExpr_formatter__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doIdDecl_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doSeqBracketed_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doPatDecl_parenthesizer__1(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doAssert__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_liftMethod;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doNested_formatter__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_termTry;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_termReturn_declRange__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doBreak_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doUnless_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_many1_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doSeq_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doSeqItem_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_motive;
lean_object* l_Lean_Parser_Term_optType_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_doElemParser_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doDebugAssert_formatter__1(lean_object*);
lean_object* l_Lean_Parser_many1Indent_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ppAllowUngrouped_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doUnless_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_matchDiscr_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doFinally_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doLetExpr_parenthesizer__1(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doHave_formatter__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_notFollowedByRedefinedTermToken_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkColGe_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_binderIdent_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_nonReservedSymbol_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doLetMetaExpr__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doLetElse;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doSeqBracketed_formatter__1(lean_object*);
extern lean_object* l_Lean_PrettyPrinter_parenthesizerAttribute;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doHave_declRange__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_optMetaFalse_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_termBeforeDo;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doUnless_parenthesizer__1(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doAssert_declRange__1(lean_object*);
extern lean_object* l_Lean_Parser_Term_generalizingParam;
extern lean_object* l_Lean_Parser_Term_binderIdent;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_letIdDeclNoBinders_parenthesizer___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doTry_parenthesizer__1(lean_object*);
lean_object* l_Lean_ppLine_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doExpr_declRange__1(lean_object*);
extern lean_object* l_Lean_Parser_Term_letDecl;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doPatDecl_formatter__1(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_liftMethod_declRange__1(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_registerAlias(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_sepBy1(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Parser_notFollowedBy(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doReassignArrow;
lean_object* l_Lean_Parser_symbol(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doHave;
lean_object* l_Lean_Parser_withForbidden_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_termFor_declRange__1(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doIf__1(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doLetElse_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doIf_declRange__1(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_notFollowedBy_formatter___redArg(lean_object*);
lean_object* l_Lean_Parser_symbol_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doSeq_docString__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_notFollowedByRedefinedTermToken;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doIf_parenthesizer___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_withResetCache_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doMatchExprAlts_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doIf_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doMatchExprAlts;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doLet_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doPatDecl_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doTry_declRange__1(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doLetElse_parenthesizer__1(lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doLetRec__1(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_termFor_formatter__1(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doDebugAssert__1(lean_object*);
lean_object* l_Lean_Parser_symbol_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_letRecDecls;
lean_object* l_Lean_Parser_withAntiquot(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doIfCond_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_darrow;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doFor_parenthesizer__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doExpr_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_optIdent;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_withPosition_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doMatchExpr_formatter__1(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkColGt_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_termReturn_docString__1(lean_object*);
lean_object* l_Lean_Parser_withPositionAfterLinebreak(lean_object*);
extern lean_object* l_Lean_Parser_Term_matchDiscr;
lean_object* l_Lean_PrettyPrinter_Formatter_pushLine___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_ident_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doExpr_formatter__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doForDecl;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Parser_darrow_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doUnless__1(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doLetArrow__1(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkColGt_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doFinally_formatter__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doLetMetaExpr_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doMatch_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doReturn_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_many_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_termFor__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doSeqItem_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_doElemParser(lean_object*);
lean_object* l_Lean_Parser_Term_ident_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doTry_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_do_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_interpolatedStr_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doIdDecl_formatter__1(lean_object*);
lean_object* l_Lean_Parser_node(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doMatchExpr__1(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doDbgTrace_formatter__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doAssert_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doLetArrow_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doForDecl_parenthesizer__1(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doIdDecl_parenthesizer__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doCatch_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_withForbidden(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doAssert_formatter__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doLetElse_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_letIdDeclNoBinders_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_andthen(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doCatchMatch_parenthesizer__1(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doCatch_formatter__1(lean_object*);
lean_object* l_Lean_Parser_checkColGe(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doIfProp;
lean_object* l_Lean_Parser_atomic(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doIf_formatter___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doIfLet_parenthesizer__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doSeqBracketed_parenthesizer___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doFinally_parenthesizer__1(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doIfLet_formatter__1(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doCatch_parenthesizer__1(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_do_declRange__1(lean_object*);
lean_object* l_Lean_Parser_Term_matchExprPat_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doLetMetaExpr_declRange__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Do___hyg_4_(lean_object*);
lean_object* l_Lean_Parser_many(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doSeqItem_formatter__1(lean_object*);
extern lean_object* l_Lean_Parser_Term_haveDecl;
lean_object* l_Lean_ppDedent_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doLet_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_pushNone_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_letIdDeclNoBinders_formatter__1(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_do_parenthesizer__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doCatchMatch_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doMatchExpr;
LEAN_EXPORT lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Do___hyg_42_(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doContinue_formatter__1(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doReturn_declRange__1(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doReturn_formatter__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doIf_parenthesizer___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_termReturn__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doSeqBracketed;
lean_object* l_Lean_Parser_withPosition_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_leadingNode_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_termUnless__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doHave_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_optional_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_unicodeSymbol_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_sepBy1_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_group(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doDbgTrace_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkLineEq_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doIfProp_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_motive_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_letRecDecls_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doIfLetPure_parenthesizer__1(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_termUnless_declRange__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doIdDecl_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_letDecl_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_withResetCache(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doIdDecl;
lean_object* l_Lean_Parser_withCache(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doReassign_formatter__1(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doSeqItem_parenthesizer__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doHave_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doIfLet_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_atomic_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doAssert_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_matchAlts(lean_object*);
extern lean_object* l_Lean_Parser_skip;
lean_object* l_Lean_Parser_withoutPosition_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_liftMethod_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doLetRec_declRange__1(lean_object*);
lean_object* l_Lean_Parser_unicodeSymbol_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doExpr__1(lean_object*);
lean_object* l_Lean_Parser_Term_matchExprAlts(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doReassign__1(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doFor_formatter__1(lean_object*);
lean_object* l_Lean_Parser_unicodeSymbol(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doReassignArrow_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doSeq_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_registerAlias(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doForDecl_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doContinue;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_optMetaFalse_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_addBuiltinLeadingParser(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doHave_parenthesizer__1(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doMatch_formatter__1(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doReturn__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doIfLetPure;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_notFollowedByRedefinedTermToken_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_haveDecl_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doForDecl_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_many1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_notFollowedByRedefinedTermToken_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_termUnless_formatter__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_leftArrow_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doLetExpr__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_termReturn_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doIfProp_parenthesizer__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doLetExpr_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_letPatDecl_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doIfProp_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doSeqBracketed_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doDbgTrace;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doIfLetBind_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doFor_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doIf_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doMatchAlts_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_checkLineEq(lean_object*);
lean_object* l_Lean_Parser_Term_optType_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doLetRec_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_termParser_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doReassign_declRange__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doIfLetBind;
lean_object* l_Lean_PrettyPrinter_Formatter_andthen_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doNested__1(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkColGe_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_leftArrow_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_termTry_formatter__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doTry;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doDbgTrace_declRange__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_termFor_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doLet;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doDebugAssert_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_termTry_parenthesizer__1(lean_object*);
extern lean_object* l_Lean_Parser_Term_ident;
lean_object* l_Lean_Parser_Term_generalizingParam_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_many1Indent_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doFor_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doDbgTrace_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_matchExprAlts_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doPatDecl;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doMatchExprAlts_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doForDecl_formatter__1(lean_object*);
lean_object* l_Lean_Parser_sepBy1_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doMatch__1(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_termUnless_docString__1(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doTry_formatter__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doContinue_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_notFollowedBy_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doAssert_parenthesizer__1(lean_object*);
lean_object* l_Lean_Parser_mkAntiquot(lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_liftMethod_formatter__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doLetRec;
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doBreak_docString__1(lean_object*);
extern lean_object* l_Lean_PrettyPrinter_formatterAttribute;
lean_object* l_Lean_ppIndent_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doFinally;
lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___Lean_PrettyPrinter_Parenthesizer_visitArgs_spec__1___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_optType;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doFor_docString__1(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_notFollowedBy_parenthesizer___redArg(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doBreak__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doSeqItem_parenthesizer___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_nonReservedSymbol_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_termTry_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_group_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doLetExpr;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doDbgTrace__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_letIdDeclNoBinders_parenthesizer___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doLetExpr_declRange__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_termFor_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doMatchExpr_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_termUnless;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_do_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_categoryParser_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_liftMethod_parenthesizer__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doReassign_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doFor;
LEAN_EXPORT lean_object* l_Lean_Parser_Term_letIdDeclNoBinders_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doIdDecl_parenthesizer___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doDebugAssert_docString__1(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doMatchExpr_parenthesizer__1(lean_object*);
lean_object* l_Lean_Parser_Term_letRecDecls_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_liftMethod_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doLetElse__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doIdDecl_formatter___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_notFollowedByRedefinedTermToken_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_letPatDecl;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doLet__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doUnless;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doDbgTrace_docString__1(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doMatchExpr_declRange__1(lean_object*);
lean_object* l_Lean_Parser_registerBuiltinDynamicParserAttribute(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doSeqBracketed_parenthesizer__1(lean_object*);
lean_object* l_Lean_Parser_withoutPosition(lean_object*);
lean_object* l_Lean_Parser_Term_optIdent_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_generalizingParam_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doReassignArrow__1(lean_object*);
lean_object* l_Lean_Parser_checkColGt(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doBreak_parenthesizer__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_termFor;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doSeqIndent_formatter__1(lean_object*);
lean_object* l_Lean_Parser_Term_matchExprPat_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doLetMetaExpr_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doMatch_parenthesizer__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_doElemParser_formatter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doExpr_parenthesizer__1(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_termReturn_formatter__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_doElemParser_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doUnless_formatter__1(lean_object*);
lean_object* l_Lean_Parser_Term_matchDiscr_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doLetRec_parenthesizer__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Term_notFollowedByRedefinedTermToken_formatter___redArg(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkLineEq_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doContinue_docString__1(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_node_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doMatch_declRange__1(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doSeqIndent_parenthesizer__1(lean_object*);
lean_object* l_Lean_Parser_termParser(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_registerAlias(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Do___hyg_4_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_2 = lean_mk_string_unchecked("builtin_doElem_parser", 21, 21);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Category", 8, 8);
x_7 = lean_mk_string_unchecked("doElem", 6, 6);
lean_inc(x_5);
lean_inc(x_4);
x_8 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_7);
x_9 = lean_box(0);
x_10 = lean_box(0);
lean_inc(x_4);
x_11 = l_Lean_Name_str___override(x_10, x_4);
lean_inc(x_5);
x_12 = l_Lean_Name_str___override(x_11, x_5);
x_13 = lean_mk_string_unchecked("initFn", 6, 6);
x_14 = l_Lean_Name_str___override(x_12, x_13);
x_15 = lean_mk_string_unchecked("_@", 2, 2);
x_16 = l_Lean_Name_str___override(x_14, x_15);
x_17 = l_Lean_Name_str___override(x_16, x_4);
x_18 = l_Lean_Name_str___override(x_17, x_5);
x_19 = lean_mk_string_unchecked("Do", 2, 2);
x_20 = l_Lean_Name_str___override(x_18, x_19);
x_21 = lean_mk_string_unchecked("_hyg", 4, 4);
x_22 = l_Lean_Name_str___override(x_20, x_21);
x_23 = lean_unsigned_to_nat(4u);
x_24 = l_Lean_Name_num___override(x_22, x_23);
x_25 = lean_unbox(x_9);
x_26 = l_Lean_Parser_registerBuiltinParserAttribute(x_3, x_8, x_25, x_24, x_1);
return x_26;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Do___hyg_42_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_2 = lean_mk_string_unchecked("doElem_parser", 13, 13);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_mk_string_unchecked("doElem", 6, 6);
x_5 = l_Lean_Name_mkStr1(x_4);
x_6 = lean_box(0);
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
lean_inc(x_7);
x_8 = l_Lean_Name_str___override(x_6, x_7);
x_9 = lean_mk_string_unchecked("Parser", 6, 6);
lean_inc(x_9);
x_10 = l_Lean_Name_str___override(x_8, x_9);
x_11 = lean_mk_string_unchecked("initFn", 6, 6);
x_12 = l_Lean_Name_str___override(x_10, x_11);
x_13 = lean_mk_string_unchecked("_@", 2, 2);
x_14 = l_Lean_Name_str___override(x_12, x_13);
x_15 = l_Lean_Name_str___override(x_14, x_7);
x_16 = l_Lean_Name_str___override(x_15, x_9);
x_17 = lean_mk_string_unchecked("Do", 2, 2);
x_18 = l_Lean_Name_str___override(x_16, x_17);
x_19 = lean_mk_string_unchecked("_hyg", 4, 4);
x_20 = l_Lean_Name_str___override(x_18, x_19);
x_21 = lean_unsigned_to_nat(42u);
x_22 = l_Lean_Name_num___override(x_20, x_21);
x_23 = l_Lean_Parser_registerBuiltinDynamicParserAttribute(x_3, x_5, x_22, x_1);
return x_23;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_doElemParser(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_mk_string_unchecked("doElem", 6, 6);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = l_Lean_Parser_categoryParser(x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Term_leftArrow() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_mk_string_unchecked("← ", 4, 2);
x_2 = lean_mk_string_unchecked("<- ", 3, 3);
x_3 = l_Lean_Parser_unicodeSymbol(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Term_liftMethod() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Term", 4, 4);
x_4 = lean_mk_string_unchecked("liftMethod", 10, 10);
lean_inc(x_4);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_box(1);
x_7 = lean_box(0);
x_8 = lean_unbox(x_6);
x_9 = lean_unbox(x_7);
lean_inc(x_5);
x_10 = l_Lean_Parser_mkAntiquot(x_4, x_5, x_8, x_9);
lean_dec(x_4);
x_11 = lean_unsigned_to_nat(10u);
x_12 = l_Lean_Parser_Term_leftArrow;
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Lean_Parser_termParser(x_13);
x_15 = l_Lean_Parser_andthen(x_12, x_14);
lean_inc(x_5);
x_16 = l_Lean_Parser_leadingNode(x_5, x_11, x_15);
x_17 = l_Lean_Parser_withAntiquot(x_10, x_16);
x_18 = l_Lean_Parser_withCache(x_5, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_liftMethod__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = lean_mk_string_unchecked("term", 4, 4);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Term", 4, 4);
x_7 = lean_mk_string_unchecked("liftMethod", 10, 10);
x_8 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_7);
x_9 = l_Lean_Parser_Term_liftMethod;
x_10 = lean_unsigned_to_nat(1000u);
x_11 = l_Lean_Parser_addBuiltinLeadingParser(x_3, x_8, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_liftMethod_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Term", 4, 4);
x_5 = lean_mk_string_unchecked("liftMethod", 10, 10);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(20u);
x_8 = lean_unsigned_to_nat(23u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(21u);
x_11 = lean_unsigned_to_nat(25u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_11);
x_14 = lean_unsigned_to_nat(27u);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_unsigned_to_nat(37u);
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
LEAN_EXPORT lean_object* l_Lean_Parser_Term_leftArrow_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_mk_string_unchecked("← ", 4, 2);
x_7 = lean_mk_string_unchecked("<- ", 3, 3);
x_8 = l_Lean_Parser_unicodeSymbol_formatter(x_6, x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_liftMethod_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("Parser", 6, 6);
x_8 = lean_mk_string_unchecked("Term", 4, 4);
x_9 = lean_mk_string_unchecked("liftMethod", 10, 10);
lean_inc(x_9);
x_10 = l_Lean_Name_mkStr4(x_6, x_7, x_8, x_9);
x_11 = lean_box(1);
x_12 = lean_box(0);
lean_inc(x_10);
x_13 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(x_13, 0, x_9);
lean_closure_set(x_13, 1, x_10);
lean_closure_set(x_13, 2, x_11);
lean_closure_set(x_13, 3, x_12);
x_14 = lean_unsigned_to_nat(10u);
x_15 = lean_alloc_closure((void*)(l_Lean_Parser_Term_leftArrow_formatter), 5, 0);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_alloc_closure((void*)(l_Lean_Parser_termParser_formatter___boxed), 6, 1);
lean_closure_set(x_17, 0, x_16);
x_18 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_18, 0, x_15);
lean_closure_set(x_18, 1, x_17);
x_19 = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(x_19, 0, x_10);
lean_closure_set(x_19, 1, x_14);
lean_closure_set(x_19, 2, x_18);
x_20 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_13, x_19, x_1, x_2, x_3, x_4, x_5);
return x_20;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_liftMethod_formatter__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_formatterAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("liftMethod", 10, 10);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("formatter", 9, 9);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Term_liftMethod_formatter), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_leftArrow_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_mk_string_unchecked("← ", 4, 2);
x_7 = lean_mk_string_unchecked("<- ", 3, 3);
x_8 = l_Lean_Parser_unicodeSymbol_parenthesizer(x_6, x_7, x_1, x_2, x_3, x_4, x_5);
lean_dec(x_7);
lean_dec(x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_liftMethod_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("Parser", 6, 6);
x_8 = lean_mk_string_unchecked("Term", 4, 4);
x_9 = lean_mk_string_unchecked("liftMethod", 10, 10);
lean_inc(x_9);
x_10 = l_Lean_Name_mkStr4(x_6, x_7, x_8, x_9);
x_11 = lean_box(1);
x_12 = lean_box(0);
lean_inc(x_10);
x_13 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(x_13, 0, x_9);
lean_closure_set(x_13, 1, x_10);
lean_closure_set(x_13, 2, x_11);
lean_closure_set(x_13, 3, x_12);
x_14 = lean_unsigned_to_nat(10u);
x_15 = lean_alloc_closure((void*)(l_Lean_Parser_Term_leftArrow_parenthesizer), 5, 0);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_alloc_closure((void*)(l_Lean_Parser_termParser_parenthesizer), 6, 1);
lean_closure_set(x_17, 0, x_16);
x_18 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_18, 0, x_15);
lean_closure_set(x_18, 1, x_17);
x_19 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer), 8, 3);
lean_closure_set(x_19, 0, x_10);
lean_closure_set(x_19, 1, x_14);
lean_closure_set(x_19, 2, x_18);
x_20 = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(x_13, x_19, x_1, x_2, x_3, x_4, x_5);
return x_20;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_liftMethod_parenthesizer__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("liftMethod", 10, 10);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("parenthesizer", 13, 13);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Term_liftMethod_parenthesizer), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
static lean_object* _init_l_Lean_Parser_Term_doSeqItem() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Term", 4, 4);
x_4 = lean_mk_string_unchecked("doSeqItem", 9, 9);
lean_inc(x_4);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_box(1);
x_7 = lean_box(0);
x_8 = lean_unbox(x_6);
x_9 = lean_unbox(x_7);
lean_inc(x_5);
x_10 = l_Lean_Parser_mkAntiquot(x_4, x_5, x_8, x_9);
lean_dec(x_4);
x_11 = lean_unsigned_to_nat(1024u);
x_12 = l_Lean_Parser_skip;
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_mk_string_unchecked("doElem", 6, 6);
x_15 = l_Lean_Name_mkStr1(x_14);
x_16 = l_Lean_Parser_categoryParser(x_15, x_13);
x_17 = lean_mk_string_unchecked("; ", 2, 2);
x_18 = l_Lean_Parser_symbol(x_17);
lean_dec(x_17);
x_19 = l_Lean_Parser_optional(x_18);
x_20 = l_Lean_Parser_andthen(x_16, x_19);
x_21 = l_Lean_Parser_andthen(x_12, x_20);
lean_inc(x_5);
x_22 = l_Lean_Parser_leadingNode(x_5, x_11, x_21);
x_23 = l_Lean_Parser_withAntiquot(x_10, x_22);
x_24 = l_Lean_Parser_withCache(x_5, x_23);
return x_24;
}
}
static lean_object* _init_l_Lean_Parser_Term_doSeqIndent() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Term", 4, 4);
x_4 = lean_mk_string_unchecked("doSeqIndent", 11, 11);
lean_inc(x_4);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_box(1);
x_7 = lean_box(0);
x_8 = lean_unbox(x_6);
x_9 = lean_unbox(x_7);
lean_inc(x_5);
x_10 = l_Lean_Parser_mkAntiquot(x_4, x_5, x_8, x_9);
lean_dec(x_4);
x_11 = lean_unsigned_to_nat(1024u);
x_12 = l_Lean_Parser_Term_doSeqItem;
x_13 = lean_mk_string_unchecked("irrelevant", 10, 10);
x_14 = l_Lean_Parser_checkColGe(x_13);
x_15 = l_Lean_Parser_andthen(x_14, x_12);
x_16 = l_Lean_Parser_many1(x_15);
x_17 = l_Lean_Parser_withPosition(x_16);
lean_inc(x_5);
x_18 = l_Lean_Parser_leadingNode(x_5, x_11, x_17);
x_19 = l_Lean_Parser_withAntiquot(x_10, x_18);
x_20 = l_Lean_Parser_withCache(x_5, x_19);
return x_20;
}
}
static lean_object* _init_l_Lean_Parser_Term_doSeqBracketed() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Term", 4, 4);
x_4 = lean_mk_string_unchecked("doSeqBracketed", 14, 14);
lean_inc(x_4);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_box(1);
x_7 = lean_box(0);
x_8 = lean_unbox(x_6);
x_9 = lean_unbox(x_7);
lean_inc(x_5);
x_10 = l_Lean_Parser_mkAntiquot(x_4, x_5, x_8, x_9);
lean_dec(x_4);
x_11 = lean_unsigned_to_nat(1024u);
x_12 = lean_mk_string_unchecked("{", 1, 1);
x_13 = l_Lean_Parser_symbol(x_12);
lean_dec(x_12);
x_14 = l_Lean_Parser_Term_doSeqItem;
x_15 = l_Lean_Parser_many1(x_14);
x_16 = l_Lean_Parser_withoutPosition(x_15);
x_17 = l_Lean_Parser_skip;
x_18 = lean_mk_string_unchecked("}", 1, 1);
x_19 = l_Lean_Parser_symbol(x_18);
lean_dec(x_18);
x_20 = l_Lean_Parser_andthen(x_17, x_19);
x_21 = l_Lean_Parser_andthen(x_16, x_20);
x_22 = l_Lean_Parser_andthen(x_13, x_21);
lean_inc(x_5);
x_23 = l_Lean_Parser_leadingNode(x_5, x_11, x_22);
x_24 = l_Lean_Parser_withAntiquot(x_10, x_23);
x_25 = l_Lean_Parser_withCache(x_5, x_24);
return x_25;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doSeq_docString__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Term", 4, 4);
x_5 = lean_mk_string_unchecked("doSeq", 5, 5);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_mk_string_unchecked("A `doSeq` is a sequence of `doElem`, the main argument after the `do` keyword and other\ndo elements that take blocks. It can either have the form `\"{\" (doElem \";\"\?)* \"}\"` or\n`many1Indent (doElem \";\"\?)`, where `many1Indent` ensures that all the items are at\nthe same or higher indentation level as the first line. ", 313, 313);
x_8 = l_Lean_addBuiltinDocString(x_6, x_7, x_1);
return x_8;
}
}
static lean_object* _init_l_Lean_Parser_Term_doSeq() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_1 = lean_mk_string_unchecked("doSeq", 5, 5);
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Term", 4, 4);
lean_inc(x_1);
x_5 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_1);
x_6 = lean_box(1);
x_7 = lean_unbox(x_6);
x_8 = lean_unbox(x_6);
x_9 = l_Lean_Parser_mkAntiquot(x_1, x_5, x_7, x_8);
lean_dec(x_1);
x_10 = l_Lean_Parser_Term_doSeqBracketed;
x_11 = l_Lean_Parser_Term_doSeqIndent;
x_12 = l_Lean_Parser_orelse(x_10, x_11);
x_13 = l_Lean_Parser_withAntiquot(x_9, x_12);
return x_13;
}
}
static lean_object* _init_l_Lean_Parser_Term_termBeforeDo() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_mk_string_unchecked("do", 2, 2);
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Parser_termParser(x_2);
x_4 = l_Lean_Parser_withForbidden(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_doElemParser_formatter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_mk_string_unchecked("doElem", 6, 6);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = l_Lean_PrettyPrinter_Formatter_categoryParser_formatter(x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_doElemParser_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_doElemParser_formatter___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_doElemParser_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_doElemParser_formatter(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doSeqItem_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("Parser", 6, 6);
x_8 = lean_mk_string_unchecked("Term", 4, 4);
x_9 = lean_mk_string_unchecked("doSeqItem", 9, 9);
lean_inc(x_9);
x_10 = l_Lean_Name_mkStr4(x_6, x_7, x_8, x_9);
x_11 = lean_box(1);
x_12 = lean_box(0);
lean_inc(x_10);
x_13 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(x_13, 0, x_9);
lean_closure_set(x_13, 1, x_10);
lean_closure_set(x_13, 2, x_11);
lean_closure_set(x_13, 3, x_12);
x_14 = lean_unsigned_to_nat(1024u);
x_15 = lean_alloc_closure((void*)(l_Lean_ppLine_formatter___boxed), 5, 0);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_alloc_closure((void*)(l_Lean_Parser_doElemParser_formatter___boxed), 6, 1);
lean_closure_set(x_17, 0, x_16);
x_18 = lean_mk_string_unchecked("; ", 2, 2);
x_19 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter), 6, 1);
lean_closure_set(x_19, 0, x_18);
x_20 = lean_alloc_closure((void*)(l_Lean_Parser_optional_formatter), 6, 1);
lean_closure_set(x_20, 0, x_19);
x_21 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_21, 0, x_17);
lean_closure_set(x_21, 1, x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_22, 0, x_15);
lean_closure_set(x_22, 1, x_21);
x_23 = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(x_23, 0, x_10);
lean_closure_set(x_23, 1, x_14);
lean_closure_set(x_23, 2, x_22);
x_24 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_13, x_23, x_1, x_2, x_3, x_4, x_5);
return x_24;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doSeqItem_formatter__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_formatterAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("doSeqItem", 9, 9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("formatter", 9, 9);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doSeqItem_formatter), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doSeqBracketed_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("Parser", 6, 6);
x_8 = lean_mk_string_unchecked("Term", 4, 4);
x_9 = lean_mk_string_unchecked("doSeqBracketed", 14, 14);
lean_inc(x_9);
x_10 = l_Lean_Name_mkStr4(x_6, x_7, x_8, x_9);
x_11 = lean_box(1);
x_12 = lean_box(0);
lean_inc(x_10);
x_13 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(x_13, 0, x_9);
lean_closure_set(x_13, 1, x_10);
lean_closure_set(x_13, 2, x_11);
lean_closure_set(x_13, 3, x_12);
x_14 = lean_unsigned_to_nat(1024u);
x_15 = lean_mk_string_unchecked("{", 1, 1);
x_16 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter), 6, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doSeqItem_formatter), 5, 0);
x_18 = lean_alloc_closure((void*)(l_Lean_Parser_many1_formatter), 6, 1);
lean_closure_set(x_18, 0, x_17);
x_19 = lean_alloc_closure((void*)(l_Lean_Parser_withoutPosition_formatter), 6, 1);
lean_closure_set(x_19, 0, x_18);
x_20 = lean_alloc_closure((void*)(l_Lean_ppLine_formatter___boxed), 5, 0);
x_21 = lean_mk_string_unchecked("}", 1, 1);
x_22 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter), 6, 1);
lean_closure_set(x_22, 0, x_21);
x_23 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_23, 0, x_20);
lean_closure_set(x_23, 1, x_22);
x_24 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_24, 0, x_19);
lean_closure_set(x_24, 1, x_23);
x_25 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_25, 0, x_16);
lean_closure_set(x_25, 1, x_24);
x_26 = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(x_26, 0, x_10);
lean_closure_set(x_26, 1, x_14);
lean_closure_set(x_26, 2, x_25);
x_27 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_13, x_26, x_1, x_2, x_3, x_4, x_5);
return x_27;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doSeqBracketed_formatter__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_formatterAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("doSeqBracketed", 14, 14);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("formatter", 9, 9);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doSeqBracketed_formatter), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doSeqIndent_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("Parser", 6, 6);
x_8 = lean_mk_string_unchecked("Term", 4, 4);
x_9 = lean_mk_string_unchecked("doSeqIndent", 11, 11);
lean_inc(x_9);
x_10 = l_Lean_Name_mkStr4(x_6, x_7, x_8, x_9);
x_11 = lean_box(1);
x_12 = lean_box(0);
lean_inc(x_10);
x_13 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(x_13, 0, x_9);
lean_closure_set(x_13, 1, x_10);
lean_closure_set(x_13, 2, x_11);
lean_closure_set(x_13, 3, x_12);
x_14 = lean_unsigned_to_nat(1024u);
x_15 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doSeqItem_formatter), 5, 0);
x_16 = lean_alloc_closure((void*)(l_Lean_Parser_many1Indent_formatter), 6, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(x_17, 0, x_10);
lean_closure_set(x_17, 1, x_14);
lean_closure_set(x_17, 2, x_16);
x_18 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_13, x_17, x_1, x_2, x_3, x_4, x_5);
return x_18;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doSeqIndent_formatter__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_formatterAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("doSeqIndent", 11, 11);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("formatter", 9, 9);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doSeqIndent_formatter), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doSeq_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_6 = lean_mk_string_unchecked("doSeq", 5, 5);
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
x_8 = lean_mk_string_unchecked("Parser", 6, 6);
x_9 = lean_mk_string_unchecked("Term", 4, 4);
lean_inc(x_6);
x_10 = l_Lean_Name_mkStr4(x_7, x_8, x_9, x_6);
x_11 = lean_box(1);
x_12 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(x_12, 0, x_6);
lean_closure_set(x_12, 1, x_10);
lean_closure_set(x_12, 2, x_11);
lean_closure_set(x_12, 3, x_11);
x_13 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doSeqBracketed_formatter), 5, 0);
x_14 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doSeqIndent_formatter), 5, 0);
x_15 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter), 7, 2);
lean_closure_set(x_15, 0, x_13);
lean_closure_set(x_15, 1, x_14);
x_16 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_12, x_15, x_1, x_2, x_3, x_4, x_5);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_doElemParser_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_mk_string_unchecked("doElem", 6, 6);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer(x_8, x_1, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doSeqItem_parenthesizer___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Parenthesizer_skip_parenthesizer___redArg(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doSeqItem_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doSeqItem_parenthesizer___lam__0___boxed), 5, 0);
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
x_8 = lean_mk_string_unchecked("Parser", 6, 6);
x_9 = lean_mk_string_unchecked("Term", 4, 4);
x_10 = lean_mk_string_unchecked("doSeqItem", 9, 9);
lean_inc(x_10);
x_11 = l_Lean_Name_mkStr4(x_7, x_8, x_9, x_10);
x_12 = lean_box(1);
x_13 = lean_box(0);
lean_inc(x_11);
x_14 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(x_14, 0, x_10);
lean_closure_set(x_14, 1, x_11);
lean_closure_set(x_14, 2, x_12);
lean_closure_set(x_14, 3, x_13);
x_15 = lean_unsigned_to_nat(1024u);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_alloc_closure((void*)(l_Lean_Parser_doElemParser_parenthesizer), 6, 1);
lean_closure_set(x_17, 0, x_16);
x_18 = lean_mk_string_unchecked("; ", 2, 2);
x_19 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___boxed), 6, 1);
lean_closure_set(x_19, 0, x_18);
x_20 = lean_alloc_closure((void*)(l_Lean_Parser_optional_parenthesizer), 6, 1);
lean_closure_set(x_20, 0, x_19);
x_21 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_21, 0, x_17);
lean_closure_set(x_21, 1, x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_22, 0, x_6);
lean_closure_set(x_22, 1, x_21);
x_23 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer), 8, 3);
lean_closure_set(x_23, 0, x_11);
lean_closure_set(x_23, 1, x_15);
lean_closure_set(x_23, 2, x_22);
x_24 = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(x_14, x_23, x_1, x_2, x_3, x_4, x_5);
return x_24;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doSeqItem_parenthesizer___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_Term_doSeqItem_parenthesizer___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doSeqItem_parenthesizer__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("doSeqItem", 9, 9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("parenthesizer", 13, 13);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doSeqItem_parenthesizer), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doSeqBracketed_parenthesizer___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_many1_parenthesizer(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doSeqBracketed_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doSeqItem_parenthesizer___lam__0___boxed), 5, 0);
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
x_8 = lean_mk_string_unchecked("Parser", 6, 6);
x_9 = lean_mk_string_unchecked("Term", 4, 4);
x_10 = lean_mk_string_unchecked("doSeqBracketed", 14, 14);
lean_inc(x_10);
x_11 = l_Lean_Name_mkStr4(x_7, x_8, x_9, x_10);
x_12 = lean_box(1);
x_13 = lean_box(0);
lean_inc(x_11);
x_14 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(x_14, 0, x_10);
lean_closure_set(x_14, 1, x_11);
lean_closure_set(x_14, 2, x_12);
lean_closure_set(x_14, 3, x_13);
x_15 = lean_unsigned_to_nat(1024u);
x_16 = lean_mk_string_unchecked("{", 1, 1);
x_17 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___boxed), 6, 1);
lean_closure_set(x_17, 0, x_16);
x_18 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doSeqItem_parenthesizer), 5, 0);
x_19 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doSeqBracketed_parenthesizer___lam__1), 6, 1);
lean_closure_set(x_19, 0, x_18);
x_20 = lean_mk_string_unchecked("}", 1, 1);
x_21 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___boxed), 6, 1);
lean_closure_set(x_21, 0, x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_22, 0, x_6);
lean_closure_set(x_22, 1, x_21);
x_23 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_23, 0, x_19);
lean_closure_set(x_23, 1, x_22);
x_24 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_24, 0, x_17);
lean_closure_set(x_24, 1, x_23);
x_25 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer), 8, 3);
lean_closure_set(x_25, 0, x_11);
lean_closure_set(x_25, 1, x_15);
lean_closure_set(x_25, 2, x_24);
x_26 = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(x_14, x_25, x_1, x_2, x_3, x_4, x_5);
return x_26;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doSeqBracketed_parenthesizer__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("doSeqBracketed", 14, 14);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("parenthesizer", 13, 13);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doSeqBracketed_parenthesizer), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doSeqIndent_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("Parser", 6, 6);
x_8 = lean_mk_string_unchecked("Term", 4, 4);
x_9 = lean_mk_string_unchecked("doSeqIndent", 11, 11);
lean_inc(x_9);
x_10 = l_Lean_Name_mkStr4(x_6, x_7, x_8, x_9);
x_11 = lean_box(1);
x_12 = lean_box(0);
lean_inc(x_10);
x_13 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(x_13, 0, x_9);
lean_closure_set(x_13, 1, x_10);
lean_closure_set(x_13, 2, x_11);
lean_closure_set(x_13, 3, x_12);
x_14 = lean_unsigned_to_nat(1024u);
x_15 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doSeqItem_parenthesizer), 5, 0);
x_16 = lean_alloc_closure((void*)(l_Lean_Parser_many1Indent_parenthesizer), 6, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer), 8, 3);
lean_closure_set(x_17, 0, x_10);
lean_closure_set(x_17, 1, x_14);
lean_closure_set(x_17, 2, x_16);
x_18 = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(x_13, x_17, x_1, x_2, x_3, x_4, x_5);
return x_18;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doSeqIndent_parenthesizer__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("doSeqIndent", 11, 11);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("parenthesizer", 13, 13);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doSeqIndent_parenthesizer), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doSeq_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_6 = lean_mk_string_unchecked("doSeq", 5, 5);
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
x_8 = lean_mk_string_unchecked("Parser", 6, 6);
x_9 = lean_mk_string_unchecked("Term", 4, 4);
lean_inc(x_6);
x_10 = l_Lean_Name_mkStr4(x_7, x_8, x_9, x_6);
x_11 = lean_box(1);
x_12 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(x_12, 0, x_6);
lean_closure_set(x_12, 1, x_10);
lean_closure_set(x_12, 2, x_11);
lean_closure_set(x_12, 3, x_11);
x_13 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doSeqBracketed_parenthesizer), 5, 0);
x_14 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doSeqIndent_parenthesizer), 5, 0);
x_15 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer), 7, 2);
lean_closure_set(x_15, 0, x_13);
lean_closure_set(x_15, 1, x_14);
x_16 = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(x_12, x_15, x_1, x_2, x_3, x_4, x_5);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_termBeforeDo_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_termParser_formatter___redArg(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_termBeforeDo_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Lean_Parser_termParser_parenthesizer(x_6, x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_initFn____x40_Lean_Parser_Do___hyg_228_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_35; 
x_2 = lean_mk_string_unchecked("doSeq", 5, 5);
lean_inc(x_2);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Term", 4, 4);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_7 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_2);
x_8 = l_Lean_Parser_Term_doSeq;
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
lean_inc(x_7);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_7);
x_11 = lean_box(0);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_box(1);
x_15 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_13);
x_16 = lean_unbox(x_14);
lean_ctor_set_uint8(x_15, sizeof(void*)*2, x_16);
lean_inc(x_3);
x_35 = l_Lean_Parser_registerAlias(x_3, x_7, x_9, x_10, x_15, x_1);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doSeq_formatter), 5, 0);
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_37);
lean_inc(x_3);
x_39 = l_Lean_PrettyPrinter_Formatter_registerAlias(x_3, x_38, x_36);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
x_41 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doSeq_parenthesizer), 5, 0);
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_41);
x_43 = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(x_3, x_42, x_40);
x_17 = x_43;
goto block_34;
}
else
{
lean_dec(x_3);
x_17 = x_39;
goto block_34;
}
}
else
{
lean_dec(x_3);
x_17 = x_35;
goto block_34;
}
block_34:
{
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_mk_string_unchecked("termBeforeDo", 12, 12);
lean_inc(x_19);
x_20 = l_Lean_Name_mkStr1(x_19);
x_21 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_19);
x_22 = l_Lean_Parser_Term_termBeforeDo;
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_22);
lean_inc(x_21);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_21);
lean_inc(x_20);
x_25 = l_Lean_Parser_registerAlias(x_20, x_21, x_23, x_24, x_15, x_18);
lean_dec(x_15);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_alloc_closure((void*)(l_Lean_Parser_Term_termBeforeDo_formatter), 5, 0);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
lean_inc(x_20);
x_29 = l_Lean_PrettyPrinter_Formatter_registerAlias(x_20, x_28, x_26);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_alloc_closure((void*)(l_Lean_Parser_Term_termBeforeDo_parenthesizer), 5, 0);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(x_20, x_32, x_30);
return x_33;
}
else
{
lean_dec(x_20);
return x_29;
}
}
else
{
lean_dec(x_20);
return x_25;
}
}
else
{
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_17;
}
}
}
}
static lean_object* _init_l_Lean_Parser_Term_notFollowedByRedefinedTermToken() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_1 = lean_mk_string_unchecked("set_option", 10, 10);
x_2 = l_Lean_Parser_symbol(x_1);
lean_dec(x_1);
x_3 = lean_mk_string_unchecked("open", 4, 4);
x_4 = l_Lean_Parser_symbol(x_3);
lean_dec(x_3);
x_5 = lean_mk_string_unchecked("if", 2, 2);
x_6 = l_Lean_Parser_symbol(x_5);
lean_dec(x_5);
x_7 = lean_mk_string_unchecked("match", 5, 5);
x_8 = l_Lean_Parser_symbol(x_7);
lean_dec(x_7);
x_9 = lean_mk_string_unchecked("match_expr", 10, 10);
x_10 = l_Lean_Parser_symbol(x_9);
lean_dec(x_9);
x_11 = lean_mk_string_unchecked("let", 3, 3);
x_12 = l_Lean_Parser_symbol(x_11);
lean_dec(x_11);
x_13 = lean_mk_string_unchecked("let_expr", 8, 8);
x_14 = l_Lean_Parser_symbol(x_13);
lean_dec(x_13);
x_15 = lean_mk_string_unchecked("have", 4, 4);
x_16 = l_Lean_Parser_symbol(x_15);
lean_dec(x_15);
x_17 = lean_mk_string_unchecked("do", 2, 2);
x_18 = l_Lean_Parser_symbol(x_17);
lean_dec(x_17);
x_19 = lean_mk_string_unchecked("dbg_trace", 9, 9);
x_20 = l_Lean_Parser_symbol(x_19);
lean_dec(x_19);
x_21 = lean_mk_string_unchecked("assert!", 7, 7);
x_22 = l_Lean_Parser_symbol(x_21);
lean_dec(x_21);
x_23 = lean_mk_string_unchecked("debug_assert!", 13, 13);
x_24 = l_Lean_Parser_symbol(x_23);
lean_dec(x_23);
x_25 = lean_mk_string_unchecked("for", 3, 3);
x_26 = l_Lean_Parser_symbol(x_25);
lean_dec(x_25);
x_27 = lean_mk_string_unchecked("unless", 6, 6);
x_28 = l_Lean_Parser_symbol(x_27);
lean_dec(x_27);
x_29 = lean_mk_string_unchecked("return", 6, 6);
x_30 = l_Lean_Parser_symbol(x_29);
lean_dec(x_29);
x_31 = lean_mk_string_unchecked("try", 3, 3);
x_32 = l_Lean_Parser_symbol(x_31);
lean_dec(x_31);
x_33 = l_Lean_Parser_orelse(x_30, x_32);
x_34 = l_Lean_Parser_orelse(x_28, x_33);
x_35 = l_Lean_Parser_orelse(x_26, x_34);
x_36 = l_Lean_Parser_orelse(x_24, x_35);
x_37 = l_Lean_Parser_orelse(x_22, x_36);
x_38 = l_Lean_Parser_orelse(x_20, x_37);
x_39 = l_Lean_Parser_orelse(x_18, x_38);
x_40 = l_Lean_Parser_orelse(x_16, x_39);
x_41 = l_Lean_Parser_orelse(x_14, x_40);
x_42 = l_Lean_Parser_orelse(x_12, x_41);
x_43 = l_Lean_Parser_orelse(x_10, x_42);
x_44 = l_Lean_Parser_orelse(x_8, x_43);
x_45 = l_Lean_Parser_orelse(x_6, x_44);
x_46 = l_Lean_Parser_orelse(x_4, x_45);
x_47 = l_Lean_Parser_orelse(x_2, x_46);
x_48 = lean_mk_string_unchecked("token at 'do' element", 21, 21);
x_49 = l_Lean_Parser_notFollowedBy(x_47, x_48);
return x_49;
}
}
static lean_object* _init_l_Lean_Parser_Term_doLet() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Term", 4, 4);
x_4 = lean_mk_string_unchecked("doLet", 5, 5);
lean_inc(x_4);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_box(1);
x_7 = lean_box(0);
x_8 = lean_unbox(x_6);
x_9 = lean_unbox(x_7);
lean_inc(x_5);
x_10 = l_Lean_Parser_mkAntiquot(x_4, x_5, x_8, x_9);
lean_dec(x_4);
x_11 = lean_unsigned_to_nat(1024u);
x_12 = lean_mk_string_unchecked("let ", 4, 4);
x_13 = l_Lean_Parser_symbol(x_12);
lean_dec(x_12);
x_14 = lean_mk_string_unchecked("mut ", 4, 4);
x_15 = l_Lean_Parser_symbol(x_14);
lean_dec(x_14);
x_16 = l_Lean_Parser_optional(x_15);
x_17 = l_Lean_Parser_Term_letDecl;
x_18 = l_Lean_Parser_andthen(x_16, x_17);
x_19 = l_Lean_Parser_andthen(x_13, x_18);
lean_inc(x_5);
x_20 = l_Lean_Parser_leadingNode(x_5, x_11, x_19);
x_21 = l_Lean_Parser_withAntiquot(x_10, x_20);
x_22 = l_Lean_Parser_withCache(x_5, x_21);
return x_22;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doLet__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = lean_mk_string_unchecked("doElem", 6, 6);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Term", 4, 4);
x_7 = lean_mk_string_unchecked("doLet", 5, 5);
x_8 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_7);
x_9 = l_Lean_Parser_Term_doLet;
x_10 = lean_unsigned_to_nat(1000u);
x_11 = l_Lean_Parser_addBuiltinLeadingParser(x_3, x_8, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doLet_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Term", 4, 4);
x_5 = lean_mk_string_unchecked("doLet", 5, 5);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(57u);
x_8 = lean_unsigned_to_nat(25u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(58u);
x_11 = lean_unsigned_to_nat(38u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_11);
x_14 = lean_unsigned_to_nat(29u);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_unsigned_to_nat(34u);
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
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doLet_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("Parser", 6, 6);
x_8 = lean_mk_string_unchecked("Term", 4, 4);
x_9 = lean_mk_string_unchecked("doLet", 5, 5);
lean_inc(x_9);
x_10 = l_Lean_Name_mkStr4(x_6, x_7, x_8, x_9);
x_11 = lean_box(1);
x_12 = lean_box(0);
lean_inc(x_10);
x_13 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(x_13, 0, x_9);
lean_closure_set(x_13, 1, x_10);
lean_closure_set(x_13, 2, x_11);
lean_closure_set(x_13, 3, x_12);
x_14 = lean_unsigned_to_nat(1024u);
x_15 = lean_mk_string_unchecked("let ", 4, 4);
x_16 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter), 6, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = lean_mk_string_unchecked("mut ", 4, 4);
x_18 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter), 6, 1);
lean_closure_set(x_18, 0, x_17);
x_19 = lean_alloc_closure((void*)(l_Lean_Parser_optional_formatter), 6, 1);
lean_closure_set(x_19, 0, x_18);
x_20 = lean_alloc_closure((void*)(l_Lean_Parser_Term_letDecl_formatter), 5, 0);
x_21 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_21, 0, x_19);
lean_closure_set(x_21, 1, x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_22, 0, x_16);
lean_closure_set(x_22, 1, x_21);
x_23 = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(x_23, 0, x_10);
lean_closure_set(x_23, 1, x_14);
lean_closure_set(x_23, 2, x_22);
x_24 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_13, x_23, x_1, x_2, x_3, x_4, x_5);
return x_24;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doLet_formatter__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_formatterAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("doLet", 5, 5);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("formatter", 9, 9);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doLet_formatter), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doLet_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("Parser", 6, 6);
x_8 = lean_mk_string_unchecked("Term", 4, 4);
x_9 = lean_mk_string_unchecked("doLet", 5, 5);
lean_inc(x_9);
x_10 = l_Lean_Name_mkStr4(x_6, x_7, x_8, x_9);
x_11 = lean_box(1);
x_12 = lean_box(0);
lean_inc(x_10);
x_13 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(x_13, 0, x_9);
lean_closure_set(x_13, 1, x_10);
lean_closure_set(x_13, 2, x_11);
lean_closure_set(x_13, 3, x_12);
x_14 = lean_unsigned_to_nat(1024u);
x_15 = lean_mk_string_unchecked("let ", 4, 4);
x_16 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___boxed), 6, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = lean_mk_string_unchecked("mut ", 4, 4);
x_18 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___boxed), 6, 1);
lean_closure_set(x_18, 0, x_17);
x_19 = lean_alloc_closure((void*)(l_Lean_Parser_optional_parenthesizer), 6, 1);
lean_closure_set(x_19, 0, x_18);
x_20 = lean_alloc_closure((void*)(l_Lean_Parser_Term_letDecl_parenthesizer), 5, 0);
x_21 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_21, 0, x_19);
lean_closure_set(x_21, 1, x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_22, 0, x_16);
lean_closure_set(x_22, 1, x_21);
x_23 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer), 8, 3);
lean_closure_set(x_23, 0, x_10);
lean_closure_set(x_23, 1, x_14);
lean_closure_set(x_23, 2, x_22);
x_24 = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(x_13, x_23, x_1, x_2, x_3, x_4, x_5);
return x_24;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doLet_parenthesizer__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("doLet", 5, 5);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("parenthesizer", 13, 13);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doLet_parenthesizer), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
static lean_object* _init_l_Lean_Parser_Term_doLetElse() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Term", 4, 4);
x_4 = lean_mk_string_unchecked("doLetElse", 9, 9);
lean_inc(x_4);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_box(1);
x_7 = lean_box(0);
x_8 = lean_unbox(x_6);
x_9 = lean_unbox(x_7);
lean_inc(x_5);
x_10 = l_Lean_Parser_mkAntiquot(x_4, x_5, x_8, x_9);
lean_dec(x_4);
x_11 = lean_unsigned_to_nat(1024u);
x_12 = lean_mk_string_unchecked("let ", 4, 4);
x_13 = l_Lean_Parser_symbol(x_12);
lean_dec(x_12);
x_14 = lean_mk_string_unchecked("mut ", 4, 4);
x_15 = l_Lean_Parser_symbol(x_14);
lean_dec(x_14);
x_16 = l_Lean_Parser_optional(x_15);
x_17 = lean_unsigned_to_nat(0u);
x_18 = l_Lean_Parser_termParser(x_17);
x_19 = lean_mk_string_unchecked(" := ", 4, 4);
x_20 = l_Lean_Parser_symbol(x_19);
lean_dec(x_19);
x_21 = lean_mk_string_unchecked("checkColGt", 10, 10);
x_22 = l_Lean_Parser_checkColGt(x_21);
x_23 = lean_mk_string_unchecked(" | ", 3, 3);
x_24 = l_Lean_Parser_symbol(x_23);
lean_dec(x_23);
x_25 = l_Lean_Parser_Term_doSeq;
x_26 = l_Lean_Parser_andthen(x_24, x_25);
x_27 = l_Lean_Parser_andthen(x_22, x_26);
lean_inc(x_18);
x_28 = l_Lean_Parser_andthen(x_18, x_27);
x_29 = l_Lean_Parser_andthen(x_20, x_28);
x_30 = l_Lean_Parser_andthen(x_18, x_29);
x_31 = l_Lean_Parser_andthen(x_16, x_30);
x_32 = l_Lean_Parser_andthen(x_13, x_31);
lean_inc(x_5);
x_33 = l_Lean_Parser_leadingNode(x_5, x_11, x_32);
x_34 = l_Lean_Parser_withAntiquot(x_10, x_33);
x_35 = l_Lean_Parser_withCache(x_5, x_34);
return x_35;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doLetElse__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = lean_mk_string_unchecked("doElem", 6, 6);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Term", 4, 4);
x_7 = lean_mk_string_unchecked("doLetElse", 9, 9);
x_8 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_7);
x_9 = l_Lean_Parser_Term_doLetElse;
x_10 = lean_unsigned_to_nat(1000u);
x_11 = l_Lean_Parser_addBuiltinLeadingParser(x_3, x_8, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doLetElse_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Term", 4, 4);
x_5 = lean_mk_string_unchecked("doLetElse", 9, 9);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(59u);
x_8 = lean_unsigned_to_nat(25u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(61u);
x_11 = lean_unsigned_to_nat(30u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_11);
x_14 = lean_unsigned_to_nat(29u);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_unsigned_to_nat(38u);
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
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doLetElse_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("Parser", 6, 6);
x_8 = lean_mk_string_unchecked("Term", 4, 4);
x_9 = lean_mk_string_unchecked("doLetElse", 9, 9);
lean_inc(x_9);
x_10 = l_Lean_Name_mkStr4(x_6, x_7, x_8, x_9);
x_11 = lean_box(1);
x_12 = lean_box(0);
lean_inc(x_10);
x_13 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(x_13, 0, x_9);
lean_closure_set(x_13, 1, x_10);
lean_closure_set(x_13, 2, x_11);
lean_closure_set(x_13, 3, x_12);
x_14 = lean_unsigned_to_nat(1024u);
x_15 = lean_mk_string_unchecked("let ", 4, 4);
x_16 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter), 6, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = lean_mk_string_unchecked("mut ", 4, 4);
x_18 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter), 6, 1);
lean_closure_set(x_18, 0, x_17);
x_19 = lean_alloc_closure((void*)(l_Lean_Parser_optional_formatter), 6, 1);
lean_closure_set(x_19, 0, x_18);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_alloc_closure((void*)(l_Lean_Parser_termParser_formatter___boxed), 6, 1);
lean_closure_set(x_21, 0, x_20);
x_22 = lean_mk_string_unchecked(" := ", 4, 4);
x_23 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter), 6, 1);
lean_closure_set(x_23, 0, x_22);
x_24 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkColGt_formatter___boxed), 5, 0);
x_25 = lean_mk_string_unchecked(" | ", 3, 3);
x_26 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter), 6, 1);
lean_closure_set(x_26, 0, x_25);
x_27 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doSeq_formatter), 5, 0);
x_28 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_28, 0, x_26);
lean_closure_set(x_28, 1, x_27);
x_29 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_29, 0, x_24);
lean_closure_set(x_29, 1, x_28);
lean_inc(x_21);
x_30 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_30, 0, x_21);
lean_closure_set(x_30, 1, x_29);
x_31 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_31, 0, x_23);
lean_closure_set(x_31, 1, x_30);
x_32 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_32, 0, x_21);
lean_closure_set(x_32, 1, x_31);
x_33 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_33, 0, x_19);
lean_closure_set(x_33, 1, x_32);
x_34 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_34, 0, x_16);
lean_closure_set(x_34, 1, x_33);
x_35 = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(x_35, 0, x_10);
lean_closure_set(x_35, 1, x_14);
lean_closure_set(x_35, 2, x_34);
x_36 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_13, x_35, x_1, x_2, x_3, x_4, x_5);
return x_36;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doLetElse_formatter__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_formatterAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("doLetElse", 9, 9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("formatter", 9, 9);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doLetElse_formatter), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doLetElse_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("Parser", 6, 6);
x_8 = lean_mk_string_unchecked("Term", 4, 4);
x_9 = lean_mk_string_unchecked("doLetElse", 9, 9);
lean_inc(x_9);
x_10 = l_Lean_Name_mkStr4(x_6, x_7, x_8, x_9);
x_11 = lean_box(1);
x_12 = lean_box(0);
lean_inc(x_10);
x_13 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(x_13, 0, x_9);
lean_closure_set(x_13, 1, x_10);
lean_closure_set(x_13, 2, x_11);
lean_closure_set(x_13, 3, x_12);
x_14 = lean_unsigned_to_nat(1024u);
x_15 = lean_mk_string_unchecked("let ", 4, 4);
x_16 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___boxed), 6, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = lean_mk_string_unchecked("mut ", 4, 4);
x_18 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___boxed), 6, 1);
lean_closure_set(x_18, 0, x_17);
x_19 = lean_alloc_closure((void*)(l_Lean_Parser_optional_parenthesizer), 6, 1);
lean_closure_set(x_19, 0, x_18);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_alloc_closure((void*)(l_Lean_Parser_termParser_parenthesizer), 6, 1);
lean_closure_set(x_21, 0, x_20);
x_22 = lean_mk_string_unchecked(" := ", 4, 4);
x_23 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___boxed), 6, 1);
lean_closure_set(x_23, 0, x_22);
x_24 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkColGt_parenthesizer___boxed), 5, 0);
x_25 = lean_mk_string_unchecked(" | ", 3, 3);
x_26 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___boxed), 6, 1);
lean_closure_set(x_26, 0, x_25);
x_27 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doSeq_parenthesizer), 5, 0);
x_28 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_28, 0, x_26);
lean_closure_set(x_28, 1, x_27);
x_29 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_29, 0, x_24);
lean_closure_set(x_29, 1, x_28);
lean_inc(x_21);
x_30 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_30, 0, x_21);
lean_closure_set(x_30, 1, x_29);
x_31 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_31, 0, x_23);
lean_closure_set(x_31, 1, x_30);
x_32 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_32, 0, x_21);
lean_closure_set(x_32, 1, x_31);
x_33 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_33, 0, x_19);
lean_closure_set(x_33, 1, x_32);
x_34 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_34, 0, x_16);
lean_closure_set(x_34, 1, x_33);
x_35 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer), 8, 3);
lean_closure_set(x_35, 0, x_10);
lean_closure_set(x_35, 1, x_14);
lean_closure_set(x_35, 2, x_34);
x_36 = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(x_13, x_35, x_1, x_2, x_3, x_4, x_5);
return x_36;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doLetElse_parenthesizer__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("doLetElse", 9, 9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("parenthesizer", 13, 13);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doLetElse_parenthesizer), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
static lean_object* _init_l_Lean_Parser_Term_doLetExpr() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Term", 4, 4);
x_4 = lean_mk_string_unchecked("doLetExpr", 9, 9);
lean_inc(x_4);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_box(1);
x_7 = lean_box(0);
x_8 = lean_unbox(x_6);
x_9 = lean_unbox(x_7);
lean_inc(x_5);
x_10 = l_Lean_Parser_mkAntiquot(x_4, x_5, x_8, x_9);
lean_dec(x_4);
x_11 = lean_unsigned_to_nat(1024u);
x_12 = lean_mk_string_unchecked("let_expr ", 9, 9);
x_13 = l_Lean_Parser_symbol(x_12);
lean_dec(x_12);
x_14 = l_Lean_Parser_Term_matchExprPat;
x_15 = lean_mk_string_unchecked(" := ", 4, 4);
x_16 = l_Lean_Parser_symbol(x_15);
lean_dec(x_15);
x_17 = lean_unsigned_to_nat(0u);
x_18 = l_Lean_Parser_termParser(x_17);
x_19 = lean_mk_string_unchecked("checkColGt", 10, 10);
x_20 = l_Lean_Parser_checkColGt(x_19);
x_21 = lean_mk_string_unchecked(" | ", 3, 3);
x_22 = l_Lean_Parser_symbol(x_21);
lean_dec(x_21);
x_23 = l_Lean_Parser_Term_doSeq;
x_24 = l_Lean_Parser_andthen(x_22, x_23);
x_25 = l_Lean_Parser_andthen(x_20, x_24);
x_26 = l_Lean_Parser_andthen(x_18, x_25);
x_27 = l_Lean_Parser_andthen(x_16, x_26);
x_28 = l_Lean_Parser_andthen(x_14, x_27);
x_29 = l_Lean_Parser_andthen(x_13, x_28);
lean_inc(x_5);
x_30 = l_Lean_Parser_leadingNode(x_5, x_11, x_29);
x_31 = l_Lean_Parser_withAntiquot(x_10, x_30);
x_32 = l_Lean_Parser_withCache(x_5, x_31);
return x_32;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doLetExpr__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = lean_mk_string_unchecked("doElem", 6, 6);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Term", 4, 4);
x_7 = lean_mk_string_unchecked("doLetExpr", 9, 9);
x_8 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_7);
x_9 = l_Lean_Parser_Term_doLetExpr;
x_10 = lean_unsigned_to_nat(1000u);
x_11 = l_Lean_Parser_addBuiltinLeadingParser(x_3, x_8, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doLetExpr_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Term", 4, 4);
x_5 = lean_mk_string_unchecked("doLetExpr", 9, 9);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(63u);
x_8 = lean_unsigned_to_nat(25u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(65u);
x_11 = lean_unsigned_to_nat(30u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_11);
x_14 = lean_unsigned_to_nat(29u);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_unsigned_to_nat(38u);
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
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doLetExpr_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("Parser", 6, 6);
x_8 = lean_mk_string_unchecked("Term", 4, 4);
x_9 = lean_mk_string_unchecked("doLetExpr", 9, 9);
lean_inc(x_9);
x_10 = l_Lean_Name_mkStr4(x_6, x_7, x_8, x_9);
x_11 = lean_box(1);
x_12 = lean_box(0);
lean_inc(x_10);
x_13 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(x_13, 0, x_9);
lean_closure_set(x_13, 1, x_10);
lean_closure_set(x_13, 2, x_11);
lean_closure_set(x_13, 3, x_12);
x_14 = lean_unsigned_to_nat(1024u);
x_15 = lean_mk_string_unchecked("let_expr ", 9, 9);
x_16 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter), 6, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = lean_alloc_closure((void*)(l_Lean_Parser_Term_matchExprPat_formatter), 5, 0);
x_18 = lean_mk_string_unchecked(" := ", 4, 4);
x_19 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter), 6, 1);
lean_closure_set(x_19, 0, x_18);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_alloc_closure((void*)(l_Lean_Parser_termParser_formatter___boxed), 6, 1);
lean_closure_set(x_21, 0, x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkColGt_formatter___boxed), 5, 0);
x_23 = lean_mk_string_unchecked(" | ", 3, 3);
x_24 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter), 6, 1);
lean_closure_set(x_24, 0, x_23);
x_25 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doSeq_formatter), 5, 0);
x_26 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_26, 0, x_24);
lean_closure_set(x_26, 1, x_25);
x_27 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_27, 0, x_22);
lean_closure_set(x_27, 1, x_26);
x_28 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_28, 0, x_21);
lean_closure_set(x_28, 1, x_27);
x_29 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_29, 0, x_19);
lean_closure_set(x_29, 1, x_28);
x_30 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_30, 0, x_17);
lean_closure_set(x_30, 1, x_29);
x_31 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_31, 0, x_16);
lean_closure_set(x_31, 1, x_30);
x_32 = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(x_32, 0, x_10);
lean_closure_set(x_32, 1, x_14);
lean_closure_set(x_32, 2, x_31);
x_33 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_13, x_32, x_1, x_2, x_3, x_4, x_5);
return x_33;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doLetExpr_formatter__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_formatterAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("doLetExpr", 9, 9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("formatter", 9, 9);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doLetExpr_formatter), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doLetExpr_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("Parser", 6, 6);
x_8 = lean_mk_string_unchecked("Term", 4, 4);
x_9 = lean_mk_string_unchecked("doLetExpr", 9, 9);
lean_inc(x_9);
x_10 = l_Lean_Name_mkStr4(x_6, x_7, x_8, x_9);
x_11 = lean_box(1);
x_12 = lean_box(0);
lean_inc(x_10);
x_13 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(x_13, 0, x_9);
lean_closure_set(x_13, 1, x_10);
lean_closure_set(x_13, 2, x_11);
lean_closure_set(x_13, 3, x_12);
x_14 = lean_unsigned_to_nat(1024u);
x_15 = lean_mk_string_unchecked("let_expr ", 9, 9);
x_16 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___boxed), 6, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = lean_alloc_closure((void*)(l_Lean_Parser_Term_matchExprPat_parenthesizer), 5, 0);
x_18 = lean_mk_string_unchecked(" := ", 4, 4);
x_19 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___boxed), 6, 1);
lean_closure_set(x_19, 0, x_18);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_alloc_closure((void*)(l_Lean_Parser_termParser_parenthesizer), 6, 1);
lean_closure_set(x_21, 0, x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkColGt_parenthesizer___boxed), 5, 0);
x_23 = lean_mk_string_unchecked(" | ", 3, 3);
x_24 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___boxed), 6, 1);
lean_closure_set(x_24, 0, x_23);
x_25 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doSeq_parenthesizer), 5, 0);
x_26 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_26, 0, x_24);
lean_closure_set(x_26, 1, x_25);
x_27 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_27, 0, x_22);
lean_closure_set(x_27, 1, x_26);
x_28 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_28, 0, x_21);
lean_closure_set(x_28, 1, x_27);
x_29 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_29, 0, x_19);
lean_closure_set(x_29, 1, x_28);
x_30 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_30, 0, x_17);
lean_closure_set(x_30, 1, x_29);
x_31 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_31, 0, x_16);
lean_closure_set(x_31, 1, x_30);
x_32 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer), 8, 3);
lean_closure_set(x_32, 0, x_10);
lean_closure_set(x_32, 1, x_14);
lean_closure_set(x_32, 2, x_31);
x_33 = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(x_13, x_32, x_1, x_2, x_3, x_4, x_5);
return x_33;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doLetExpr_parenthesizer__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("doLetExpr", 9, 9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("parenthesizer", 13, 13);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doLetExpr_parenthesizer), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
static lean_object* _init_l_Lean_Parser_Term_doLetMetaExpr() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Term", 4, 4);
x_4 = lean_mk_string_unchecked("doLetMetaExpr", 13, 13);
lean_inc(x_4);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_box(1);
x_7 = lean_box(0);
x_8 = lean_unbox(x_6);
x_9 = lean_unbox(x_7);
lean_inc(x_5);
x_10 = l_Lean_Parser_mkAntiquot(x_4, x_5, x_8, x_9);
lean_dec(x_4);
x_11 = lean_unsigned_to_nat(1024u);
x_12 = lean_mk_string_unchecked("let_expr ", 9, 9);
x_13 = l_Lean_Parser_symbol(x_12);
lean_dec(x_12);
x_14 = l_Lean_Parser_Term_matchExprPat;
x_15 = l_Lean_Parser_Term_leftArrow;
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Lean_Parser_termParser(x_16);
x_18 = lean_mk_string_unchecked("checkColGt", 10, 10);
x_19 = l_Lean_Parser_checkColGt(x_18);
x_20 = lean_mk_string_unchecked(" | ", 3, 3);
x_21 = l_Lean_Parser_symbol(x_20);
lean_dec(x_20);
x_22 = l_Lean_Parser_Term_doSeq;
x_23 = l_Lean_Parser_andthen(x_21, x_22);
x_24 = l_Lean_Parser_andthen(x_19, x_23);
x_25 = l_Lean_Parser_andthen(x_17, x_24);
x_26 = l_Lean_Parser_andthen(x_15, x_25);
x_27 = l_Lean_Parser_andthen(x_14, x_26);
x_28 = l_Lean_Parser_andthen(x_13, x_27);
lean_inc(x_5);
x_29 = l_Lean_Parser_leadingNode(x_5, x_11, x_28);
x_30 = l_Lean_Parser_withAntiquot(x_10, x_29);
x_31 = l_Lean_Parser_withCache(x_5, x_30);
return x_31;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doLetMetaExpr__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = lean_mk_string_unchecked("doElem", 6, 6);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Term", 4, 4);
x_7 = lean_mk_string_unchecked("doLetMetaExpr", 13, 13);
x_8 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_7);
x_9 = l_Lean_Parser_Term_doLetMetaExpr;
x_10 = lean_unsigned_to_nat(1000u);
x_11 = l_Lean_Parser_addBuiltinLeadingParser(x_3, x_8, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doLetMetaExpr_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Term", 4, 4);
x_5 = lean_mk_string_unchecked("doLetMetaExpr", 13, 13);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(67u);
x_8 = lean_unsigned_to_nat(25u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(69u);
x_11 = lean_unsigned_to_nat(30u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_11);
x_14 = lean_unsigned_to_nat(29u);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_unsigned_to_nat(42u);
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
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doLetMetaExpr_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("Parser", 6, 6);
x_8 = lean_mk_string_unchecked("Term", 4, 4);
x_9 = lean_mk_string_unchecked("doLetMetaExpr", 13, 13);
lean_inc(x_9);
x_10 = l_Lean_Name_mkStr4(x_6, x_7, x_8, x_9);
x_11 = lean_box(1);
x_12 = lean_box(0);
lean_inc(x_10);
x_13 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(x_13, 0, x_9);
lean_closure_set(x_13, 1, x_10);
lean_closure_set(x_13, 2, x_11);
lean_closure_set(x_13, 3, x_12);
x_14 = lean_unsigned_to_nat(1024u);
x_15 = lean_mk_string_unchecked("let_expr ", 9, 9);
x_16 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter), 6, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = lean_alloc_closure((void*)(l_Lean_Parser_Term_matchExprPat_formatter), 5, 0);
x_18 = lean_alloc_closure((void*)(l_Lean_Parser_Term_leftArrow_formatter), 5, 0);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_alloc_closure((void*)(l_Lean_Parser_termParser_formatter___boxed), 6, 1);
lean_closure_set(x_20, 0, x_19);
x_21 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkColGt_formatter___boxed), 5, 0);
x_22 = lean_mk_string_unchecked(" | ", 3, 3);
x_23 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter), 6, 1);
lean_closure_set(x_23, 0, x_22);
x_24 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doSeq_formatter), 5, 0);
x_25 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_25, 0, x_23);
lean_closure_set(x_25, 1, x_24);
x_26 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_26, 0, x_21);
lean_closure_set(x_26, 1, x_25);
x_27 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_27, 0, x_20);
lean_closure_set(x_27, 1, x_26);
x_28 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_28, 0, x_18);
lean_closure_set(x_28, 1, x_27);
x_29 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_29, 0, x_17);
lean_closure_set(x_29, 1, x_28);
x_30 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_30, 0, x_16);
lean_closure_set(x_30, 1, x_29);
x_31 = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(x_31, 0, x_10);
lean_closure_set(x_31, 1, x_14);
lean_closure_set(x_31, 2, x_30);
x_32 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_13, x_31, x_1, x_2, x_3, x_4, x_5);
return x_32;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doLetMetaExpr_formatter__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_formatterAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("doLetMetaExpr", 13, 13);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("formatter", 9, 9);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doLetMetaExpr_formatter), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doLetMetaExpr_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("Parser", 6, 6);
x_8 = lean_mk_string_unchecked("Term", 4, 4);
x_9 = lean_mk_string_unchecked("doLetMetaExpr", 13, 13);
lean_inc(x_9);
x_10 = l_Lean_Name_mkStr4(x_6, x_7, x_8, x_9);
x_11 = lean_box(1);
x_12 = lean_box(0);
lean_inc(x_10);
x_13 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(x_13, 0, x_9);
lean_closure_set(x_13, 1, x_10);
lean_closure_set(x_13, 2, x_11);
lean_closure_set(x_13, 3, x_12);
x_14 = lean_unsigned_to_nat(1024u);
x_15 = lean_mk_string_unchecked("let_expr ", 9, 9);
x_16 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___boxed), 6, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = lean_alloc_closure((void*)(l_Lean_Parser_Term_matchExprPat_parenthesizer), 5, 0);
x_18 = lean_alloc_closure((void*)(l_Lean_Parser_Term_leftArrow_parenthesizer), 5, 0);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_alloc_closure((void*)(l_Lean_Parser_termParser_parenthesizer), 6, 1);
lean_closure_set(x_20, 0, x_19);
x_21 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkColGt_parenthesizer___boxed), 5, 0);
x_22 = lean_mk_string_unchecked(" | ", 3, 3);
x_23 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___boxed), 6, 1);
lean_closure_set(x_23, 0, x_22);
x_24 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doSeq_parenthesizer), 5, 0);
x_25 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_25, 0, x_23);
lean_closure_set(x_25, 1, x_24);
x_26 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_26, 0, x_21);
lean_closure_set(x_26, 1, x_25);
x_27 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_27, 0, x_20);
lean_closure_set(x_27, 1, x_26);
x_28 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_28, 0, x_18);
lean_closure_set(x_28, 1, x_27);
x_29 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_29, 0, x_17);
lean_closure_set(x_29, 1, x_28);
x_30 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_30, 0, x_16);
lean_closure_set(x_30, 1, x_29);
x_31 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer), 8, 3);
lean_closure_set(x_31, 0, x_10);
lean_closure_set(x_31, 1, x_14);
lean_closure_set(x_31, 2, x_30);
x_32 = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(x_13, x_31, x_1, x_2, x_3, x_4, x_5);
return x_32;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doLetMetaExpr_parenthesizer__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("doLetMetaExpr", 13, 13);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("parenthesizer", 13, 13);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doLetMetaExpr_parenthesizer), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
static lean_object* _init_l_Lean_Parser_Term_doLetRec() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Term", 4, 4);
x_4 = lean_mk_string_unchecked("doLetRec", 8, 8);
lean_inc(x_4);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_box(1);
x_7 = lean_box(0);
x_8 = lean_unbox(x_6);
x_9 = lean_unbox(x_7);
lean_inc(x_5);
x_10 = l_Lean_Parser_mkAntiquot(x_4, x_5, x_8, x_9);
lean_dec(x_4);
x_11 = lean_unsigned_to_nat(1024u);
x_12 = lean_mk_string_unchecked("let ", 4, 4);
x_13 = l_Lean_Parser_symbol(x_12);
lean_dec(x_12);
x_14 = lean_mk_string_unchecked("rec ", 4, 4);
x_15 = lean_unbox(x_7);
x_16 = l_Lean_Parser_nonReservedSymbol(x_14, x_15);
lean_dec(x_14);
x_17 = l_Lean_Parser_andthen(x_13, x_16);
x_18 = lean_mk_string_unchecked("group", 5, 5);
x_19 = l_Lean_Name_mkStr1(x_18);
x_20 = l_Lean_Parser_node(x_19, x_17);
x_21 = l_Lean_Parser_Term_letRecDecls;
x_22 = l_Lean_Parser_andthen(x_20, x_21);
lean_inc(x_5);
x_23 = l_Lean_Parser_leadingNode(x_5, x_11, x_22);
x_24 = l_Lean_Parser_withAntiquot(x_10, x_23);
x_25 = l_Lean_Parser_withCache(x_5, x_24);
return x_25;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doLetRec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = lean_mk_string_unchecked("doElem", 6, 6);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Term", 4, 4);
x_7 = lean_mk_string_unchecked("doLetRec", 8, 8);
x_8 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_7);
x_9 = l_Lean_Parser_Term_doLetRec;
x_10 = lean_unsigned_to_nat(1000u);
x_11 = l_Lean_Parser_addBuiltinLeadingParser(x_3, x_8, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doLetRec_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Term", 4, 4);
x_5 = lean_mk_string_unchecked("doLetRec", 8, 8);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(71u);
x_8 = lean_unsigned_to_nat(25u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(72u);
x_11 = lean_unsigned_to_nat(59u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_11);
x_14 = lean_unsigned_to_nat(29u);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_unsigned_to_nat(37u);
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
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doLetRec_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("Parser", 6, 6);
x_8 = lean_mk_string_unchecked("Term", 4, 4);
x_9 = lean_mk_string_unchecked("doLetRec", 8, 8);
lean_inc(x_9);
x_10 = l_Lean_Name_mkStr4(x_6, x_7, x_8, x_9);
x_11 = lean_box(1);
x_12 = lean_box(0);
lean_inc(x_10);
x_13 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(x_13, 0, x_9);
lean_closure_set(x_13, 1, x_10);
lean_closure_set(x_13, 2, x_11);
lean_closure_set(x_13, 3, x_12);
x_14 = lean_unsigned_to_nat(1024u);
x_15 = lean_mk_string_unchecked("let ", 4, 4);
x_16 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter), 6, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = lean_mk_string_unchecked("rec ", 4, 4);
x_18 = lean_alloc_closure((void*)(l_Lean_Parser_nonReservedSymbol_formatter___boxed), 7, 2);
lean_closure_set(x_18, 0, x_17);
lean_closure_set(x_18, 1, x_12);
x_19 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_19, 0, x_16);
lean_closure_set(x_19, 1, x_18);
x_20 = lean_alloc_closure((void*)(l_Lean_Parser_group_formatter), 6, 1);
lean_closure_set(x_20, 0, x_19);
x_21 = lean_alloc_closure((void*)(l_Lean_Parser_Term_letRecDecls_formatter), 5, 0);
x_22 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_22, 0, x_20);
lean_closure_set(x_22, 1, x_21);
x_23 = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(x_23, 0, x_10);
lean_closure_set(x_23, 1, x_14);
lean_closure_set(x_23, 2, x_22);
x_24 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_13, x_23, x_1, x_2, x_3, x_4, x_5);
return x_24;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doLetRec_formatter__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_formatterAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("doLetRec", 8, 8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("formatter", 9, 9);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doLetRec_formatter), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doLetRec_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("Parser", 6, 6);
x_8 = lean_mk_string_unchecked("Term", 4, 4);
x_9 = lean_mk_string_unchecked("doLetRec", 8, 8);
lean_inc(x_9);
x_10 = l_Lean_Name_mkStr4(x_6, x_7, x_8, x_9);
x_11 = lean_box(1);
x_12 = lean_box(0);
lean_inc(x_10);
x_13 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(x_13, 0, x_9);
lean_closure_set(x_13, 1, x_10);
lean_closure_set(x_13, 2, x_11);
lean_closure_set(x_13, 3, x_12);
x_14 = lean_unsigned_to_nat(1024u);
x_15 = lean_mk_string_unchecked("let ", 4, 4);
x_16 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___boxed), 6, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = lean_mk_string_unchecked("rec ", 4, 4);
x_18 = lean_alloc_closure((void*)(l_Lean_Parser_nonReservedSymbol_parenthesizer___boxed), 7, 2);
lean_closure_set(x_18, 0, x_17);
lean_closure_set(x_18, 1, x_12);
x_19 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_19, 0, x_16);
lean_closure_set(x_19, 1, x_18);
x_20 = lean_alloc_closure((void*)(l_Lean_Parser_group_parenthesizer), 6, 1);
lean_closure_set(x_20, 0, x_19);
x_21 = lean_alloc_closure((void*)(l_Lean_Parser_Term_letRecDecls_parenthesizer), 5, 0);
x_22 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_22, 0, x_20);
lean_closure_set(x_22, 1, x_21);
x_23 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer), 8, 3);
lean_closure_set(x_23, 0, x_10);
lean_closure_set(x_23, 1, x_14);
lean_closure_set(x_23, 2, x_22);
x_24 = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(x_13, x_23, x_1, x_2, x_3, x_4, x_5);
return x_24;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doLetRec_parenthesizer__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("doLetRec", 8, 8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("parenthesizer", 13, 13);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doLetRec_parenthesizer), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
static lean_object* _init_l_Lean_Parser_Term_doIdDecl() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Term", 4, 4);
x_4 = lean_mk_string_unchecked("doIdDecl", 8, 8);
lean_inc(x_4);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_box(1);
x_7 = lean_box(0);
x_8 = lean_unbox(x_6);
x_9 = lean_unbox(x_7);
lean_inc(x_5);
x_10 = l_Lean_Parser_mkAntiquot(x_4, x_5, x_8, x_9);
lean_dec(x_4);
x_11 = lean_unsigned_to_nat(1024u);
x_12 = l_Lean_Parser_Term_ident;
x_13 = l_Lean_Parser_Term_optType;
x_14 = l_Lean_Parser_skip;
x_15 = l_Lean_Parser_Term_leftArrow;
x_16 = l_Lean_Parser_andthen(x_14, x_15);
x_17 = l_Lean_Parser_andthen(x_13, x_16);
x_18 = l_Lean_Parser_andthen(x_12, x_17);
x_19 = l_Lean_Parser_atomic(x_18);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_mk_string_unchecked("doElem", 6, 6);
x_22 = l_Lean_Name_mkStr1(x_21);
x_23 = l_Lean_Parser_categoryParser(x_22, x_20);
x_24 = l_Lean_Parser_andthen(x_19, x_23);
lean_inc(x_5);
x_25 = l_Lean_Parser_leadingNode(x_5, x_11, x_24);
x_26 = l_Lean_Parser_withAntiquot(x_10, x_25);
x_27 = l_Lean_Parser_withCache(x_5, x_26);
return x_27;
}
}
static lean_object* _init_l_Lean_Parser_Term_doPatDecl() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Term", 4, 4);
x_4 = lean_mk_string_unchecked("doPatDecl", 9, 9);
lean_inc(x_4);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_box(1);
x_7 = lean_box(0);
x_8 = lean_unbox(x_6);
x_9 = lean_unbox(x_7);
lean_inc(x_5);
x_10 = l_Lean_Parser_mkAntiquot(x_4, x_5, x_8, x_9);
lean_dec(x_4);
x_11 = lean_unsigned_to_nat(1024u);
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Lean_Parser_termParser(x_12);
x_14 = l_Lean_Parser_skip;
x_15 = l_Lean_Parser_Term_leftArrow;
x_16 = l_Lean_Parser_andthen(x_14, x_15);
x_17 = l_Lean_Parser_andthen(x_13, x_16);
x_18 = l_Lean_Parser_atomic(x_17);
x_19 = lean_mk_string_unchecked("doElem", 6, 6);
x_20 = l_Lean_Name_mkStr1(x_19);
x_21 = l_Lean_Parser_categoryParser(x_20, x_12);
x_22 = lean_mk_string_unchecked("checkColGt", 10, 10);
x_23 = l_Lean_Parser_checkColGt(x_22);
x_24 = lean_mk_string_unchecked(" | ", 3, 3);
x_25 = l_Lean_Parser_symbol(x_24);
lean_dec(x_24);
x_26 = l_Lean_Parser_Term_doSeq;
x_27 = l_Lean_Parser_andthen(x_25, x_26);
x_28 = l_Lean_Parser_andthen(x_23, x_27);
x_29 = l_Lean_Parser_optional(x_28);
x_30 = l_Lean_Parser_andthen(x_21, x_29);
x_31 = l_Lean_Parser_andthen(x_18, x_30);
lean_inc(x_5);
x_32 = l_Lean_Parser_leadingNode(x_5, x_11, x_31);
x_33 = l_Lean_Parser_withAntiquot(x_10, x_32);
x_34 = l_Lean_Parser_withCache(x_5, x_33);
return x_34;
}
}
static lean_object* _init_l_Lean_Parser_Term_doLetArrow() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Term", 4, 4);
x_4 = lean_mk_string_unchecked("doLetArrow", 10, 10);
lean_inc(x_4);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_box(1);
x_7 = lean_box(0);
x_8 = lean_unbox(x_6);
x_9 = lean_unbox(x_7);
lean_inc(x_5);
x_10 = l_Lean_Parser_mkAntiquot(x_4, x_5, x_8, x_9);
lean_dec(x_4);
x_11 = lean_unsigned_to_nat(1024u);
x_12 = lean_mk_string_unchecked("let ", 4, 4);
x_13 = l_Lean_Parser_symbol(x_12);
lean_dec(x_12);
x_14 = lean_mk_string_unchecked("mut ", 4, 4);
x_15 = l_Lean_Parser_symbol(x_14);
lean_dec(x_14);
x_16 = l_Lean_Parser_optional(x_15);
x_17 = l_Lean_Parser_Term_doIdDecl;
x_18 = l_Lean_Parser_Term_doPatDecl;
x_19 = l_Lean_Parser_orelse(x_17, x_18);
x_20 = l_Lean_Parser_andthen(x_16, x_19);
x_21 = l_Lean_Parser_andthen(x_13, x_20);
x_22 = l_Lean_Parser_withPosition(x_21);
lean_inc(x_5);
x_23 = l_Lean_Parser_leadingNode(x_5, x_11, x_22);
x_24 = l_Lean_Parser_withAntiquot(x_10, x_23);
x_25 = l_Lean_Parser_withCache(x_5, x_24);
return x_25;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doLetArrow__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = lean_mk_string_unchecked("doElem", 6, 6);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Term", 4, 4);
x_7 = lean_mk_string_unchecked("doLetArrow", 10, 10);
x_8 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_7);
x_9 = l_Lean_Parser_Term_doLetArrow;
x_10 = lean_unsigned_to_nat(1000u);
x_11 = l_Lean_Parser_addBuiltinLeadingParser(x_3, x_8, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doLetArrow_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Term", 4, 4);
x_5 = lean_mk_string_unchecked("doLetArrow", 10, 10);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(79u);
x_8 = lean_unsigned_to_nat(25u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(80u);
x_11 = lean_unsigned_to_nat(70u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_11);
x_14 = lean_unsigned_to_nat(29u);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_unsigned_to_nat(39u);
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
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doIdDecl_formatter___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Formatter_pushLine___redArg(x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doIdDecl_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doIdDecl_formatter___lam__0___boxed), 5, 0);
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
x_8 = lean_mk_string_unchecked("Parser", 6, 6);
x_9 = lean_mk_string_unchecked("Term", 4, 4);
x_10 = lean_mk_string_unchecked("doIdDecl", 8, 8);
lean_inc(x_10);
x_11 = l_Lean_Name_mkStr4(x_7, x_8, x_9, x_10);
x_12 = lean_box(1);
x_13 = lean_box(0);
lean_inc(x_11);
x_14 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(x_14, 0, x_10);
lean_closure_set(x_14, 1, x_11);
lean_closure_set(x_14, 2, x_12);
lean_closure_set(x_14, 3, x_13);
x_15 = lean_unsigned_to_nat(1024u);
x_16 = lean_alloc_closure((void*)(l_Lean_Parser_Term_ident_formatter), 5, 0);
x_17 = lean_alloc_closure((void*)(l_Lean_Parser_Term_optType_formatter), 5, 0);
x_18 = lean_alloc_closure((void*)(l_Lean_Parser_Term_leftArrow_formatter), 5, 0);
x_19 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_19, 0, x_6);
lean_closure_set(x_19, 1, x_18);
x_20 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_20, 0, x_17);
lean_closure_set(x_20, 1, x_19);
x_21 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_21, 0, x_16);
lean_closure_set(x_21, 1, x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_Parser_atomic_formatter), 6, 1);
lean_closure_set(x_22, 0, x_21);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_alloc_closure((void*)(l_Lean_Parser_doElemParser_formatter___boxed), 6, 1);
lean_closure_set(x_24, 0, x_23);
x_25 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_25, 0, x_22);
lean_closure_set(x_25, 1, x_24);
x_26 = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(x_26, 0, x_11);
lean_closure_set(x_26, 1, x_15);
lean_closure_set(x_26, 2, x_25);
x_27 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_14, x_26, x_1, x_2, x_3, x_4, x_5);
return x_27;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doIdDecl_formatter___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_Term_doIdDecl_formatter___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doIdDecl_formatter__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_formatterAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("doIdDecl", 8, 8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("formatter", 9, 9);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doIdDecl_formatter), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doPatDecl_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doIdDecl_formatter___lam__0___boxed), 5, 0);
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
x_8 = lean_mk_string_unchecked("Parser", 6, 6);
x_9 = lean_mk_string_unchecked("Term", 4, 4);
x_10 = lean_mk_string_unchecked("doPatDecl", 9, 9);
lean_inc(x_10);
x_11 = l_Lean_Name_mkStr4(x_7, x_8, x_9, x_10);
x_12 = lean_box(1);
x_13 = lean_box(0);
lean_inc(x_11);
x_14 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(x_14, 0, x_10);
lean_closure_set(x_14, 1, x_11);
lean_closure_set(x_14, 2, x_12);
lean_closure_set(x_14, 3, x_13);
x_15 = lean_unsigned_to_nat(1024u);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_alloc_closure((void*)(l_Lean_Parser_termParser_formatter___boxed), 6, 1);
lean_closure_set(x_17, 0, x_16);
x_18 = lean_alloc_closure((void*)(l_Lean_Parser_Term_leftArrow_formatter), 5, 0);
x_19 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_19, 0, x_6);
lean_closure_set(x_19, 1, x_18);
x_20 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_20, 0, x_17);
lean_closure_set(x_20, 1, x_19);
x_21 = lean_alloc_closure((void*)(l_Lean_Parser_atomic_formatter), 6, 1);
lean_closure_set(x_21, 0, x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_Parser_doElemParser_formatter___boxed), 6, 1);
lean_closure_set(x_22, 0, x_16);
x_23 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkColGt_formatter___boxed), 5, 0);
x_24 = lean_mk_string_unchecked(" | ", 3, 3);
x_25 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter), 6, 1);
lean_closure_set(x_25, 0, x_24);
x_26 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doSeq_formatter), 5, 0);
x_27 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_27, 0, x_25);
lean_closure_set(x_27, 1, x_26);
x_28 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_28, 0, x_23);
lean_closure_set(x_28, 1, x_27);
x_29 = lean_alloc_closure((void*)(l_Lean_Parser_optional_formatter), 6, 1);
lean_closure_set(x_29, 0, x_28);
x_30 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_30, 0, x_22);
lean_closure_set(x_30, 1, x_29);
x_31 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_31, 0, x_21);
lean_closure_set(x_31, 1, x_30);
x_32 = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(x_32, 0, x_11);
lean_closure_set(x_32, 1, x_15);
lean_closure_set(x_32, 2, x_31);
x_33 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_14, x_32, x_1, x_2, x_3, x_4, x_5);
return x_33;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doPatDecl_formatter__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_formatterAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("doPatDecl", 9, 9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("formatter", 9, 9);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doPatDecl_formatter), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doLetArrow_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("Parser", 6, 6);
x_8 = lean_mk_string_unchecked("Term", 4, 4);
x_9 = lean_mk_string_unchecked("doLetArrow", 10, 10);
lean_inc(x_9);
x_10 = l_Lean_Name_mkStr4(x_6, x_7, x_8, x_9);
x_11 = lean_box(1);
x_12 = lean_box(0);
lean_inc(x_10);
x_13 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(x_13, 0, x_9);
lean_closure_set(x_13, 1, x_10);
lean_closure_set(x_13, 2, x_11);
lean_closure_set(x_13, 3, x_12);
x_14 = lean_unsigned_to_nat(1024u);
x_15 = lean_mk_string_unchecked("let ", 4, 4);
x_16 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter), 6, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = lean_mk_string_unchecked("mut ", 4, 4);
x_18 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter), 6, 1);
lean_closure_set(x_18, 0, x_17);
x_19 = lean_alloc_closure((void*)(l_Lean_Parser_optional_formatter), 6, 1);
lean_closure_set(x_19, 0, x_18);
x_20 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doIdDecl_formatter), 5, 0);
x_21 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doPatDecl_formatter), 5, 0);
x_22 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter), 7, 2);
lean_closure_set(x_22, 0, x_20);
lean_closure_set(x_22, 1, x_21);
x_23 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_23, 0, x_19);
lean_closure_set(x_23, 1, x_22);
x_24 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_24, 0, x_16);
lean_closure_set(x_24, 1, x_23);
x_25 = lean_alloc_closure((void*)(l_Lean_Parser_withPosition_formatter), 6, 1);
lean_closure_set(x_25, 0, x_24);
x_26 = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(x_26, 0, x_10);
lean_closure_set(x_26, 1, x_14);
lean_closure_set(x_26, 2, x_25);
x_27 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_13, x_26, x_1, x_2, x_3, x_4, x_5);
return x_27;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doLetArrow_formatter__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_formatterAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("doLetArrow", 10, 10);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("formatter", 9, 9);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doLetArrow_formatter), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doIdDecl_parenthesizer___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doIdDecl_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doSeqItem_parenthesizer___lam__0___boxed), 5, 0);
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
x_8 = lean_mk_string_unchecked("Parser", 6, 6);
x_9 = lean_mk_string_unchecked("Term", 4, 4);
x_10 = lean_mk_string_unchecked("doIdDecl", 8, 8);
lean_inc(x_10);
x_11 = l_Lean_Name_mkStr4(x_7, x_8, x_9, x_10);
x_12 = lean_box(1);
x_13 = lean_box(0);
lean_inc(x_11);
x_14 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(x_14, 0, x_10);
lean_closure_set(x_14, 1, x_11);
lean_closure_set(x_14, 2, x_12);
lean_closure_set(x_14, 3, x_13);
x_15 = lean_unsigned_to_nat(1024u);
x_16 = lean_alloc_closure((void*)(l_Lean_Parser_Term_ident_parenthesizer), 5, 0);
x_17 = lean_alloc_closure((void*)(l_Lean_Parser_Term_optType_parenthesizer), 5, 0);
x_18 = lean_alloc_closure((void*)(l_Lean_Parser_Term_leftArrow_parenthesizer), 5, 0);
x_19 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_19, 0, x_6);
lean_closure_set(x_19, 1, x_18);
x_20 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_20, 0, x_17);
lean_closure_set(x_20, 1, x_19);
x_21 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doIdDecl_parenthesizer___lam__1), 7, 2);
lean_closure_set(x_21, 0, x_16);
lean_closure_set(x_21, 1, x_20);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_alloc_closure((void*)(l_Lean_Parser_doElemParser_parenthesizer), 6, 1);
lean_closure_set(x_23, 0, x_22);
x_24 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_24, 0, x_21);
lean_closure_set(x_24, 1, x_23);
x_25 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer), 8, 3);
lean_closure_set(x_25, 0, x_11);
lean_closure_set(x_25, 1, x_15);
lean_closure_set(x_25, 2, x_24);
x_26 = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(x_14, x_25, x_1, x_2, x_3, x_4, x_5);
return x_26;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doIdDecl_parenthesizer__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("doIdDecl", 8, 8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("parenthesizer", 13, 13);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doIdDecl_parenthesizer), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doPatDecl_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doSeqItem_parenthesizer___lam__0___boxed), 5, 0);
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
x_8 = lean_mk_string_unchecked("Parser", 6, 6);
x_9 = lean_mk_string_unchecked("Term", 4, 4);
x_10 = lean_mk_string_unchecked("doPatDecl", 9, 9);
lean_inc(x_10);
x_11 = l_Lean_Name_mkStr4(x_7, x_8, x_9, x_10);
x_12 = lean_box(1);
x_13 = lean_box(0);
lean_inc(x_11);
x_14 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(x_14, 0, x_10);
lean_closure_set(x_14, 1, x_11);
lean_closure_set(x_14, 2, x_12);
lean_closure_set(x_14, 3, x_13);
x_15 = lean_unsigned_to_nat(1024u);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_alloc_closure((void*)(l_Lean_Parser_termParser_parenthesizer), 6, 1);
lean_closure_set(x_17, 0, x_16);
x_18 = lean_alloc_closure((void*)(l_Lean_Parser_Term_leftArrow_parenthesizer), 5, 0);
x_19 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_19, 0, x_6);
lean_closure_set(x_19, 1, x_18);
x_20 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doIdDecl_parenthesizer___lam__1), 7, 2);
lean_closure_set(x_20, 0, x_17);
lean_closure_set(x_20, 1, x_19);
x_21 = lean_alloc_closure((void*)(l_Lean_Parser_doElemParser_parenthesizer), 6, 1);
lean_closure_set(x_21, 0, x_16);
x_22 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkColGt_parenthesizer___boxed), 5, 0);
x_23 = lean_mk_string_unchecked(" | ", 3, 3);
x_24 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___boxed), 6, 1);
lean_closure_set(x_24, 0, x_23);
x_25 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doSeq_parenthesizer), 5, 0);
x_26 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_26, 0, x_24);
lean_closure_set(x_26, 1, x_25);
x_27 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_27, 0, x_22);
lean_closure_set(x_27, 1, x_26);
x_28 = lean_alloc_closure((void*)(l_Lean_Parser_optional_parenthesizer), 6, 1);
lean_closure_set(x_28, 0, x_27);
x_29 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_29, 0, x_21);
lean_closure_set(x_29, 1, x_28);
x_30 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_30, 0, x_20);
lean_closure_set(x_30, 1, x_29);
x_31 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer), 8, 3);
lean_closure_set(x_31, 0, x_11);
lean_closure_set(x_31, 1, x_15);
lean_closure_set(x_31, 2, x_30);
x_32 = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(x_14, x_31, x_1, x_2, x_3, x_4, x_5);
return x_32;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doPatDecl_parenthesizer__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("doPatDecl", 9, 9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("parenthesizer", 13, 13);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doPatDecl_parenthesizer), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doLetArrow_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("Parser", 6, 6);
x_8 = lean_mk_string_unchecked("Term", 4, 4);
x_9 = lean_mk_string_unchecked("doLetArrow", 10, 10);
lean_inc(x_9);
x_10 = l_Lean_Name_mkStr4(x_6, x_7, x_8, x_9);
x_11 = lean_box(1);
x_12 = lean_box(0);
lean_inc(x_10);
x_13 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(x_13, 0, x_9);
lean_closure_set(x_13, 1, x_10);
lean_closure_set(x_13, 2, x_11);
lean_closure_set(x_13, 3, x_12);
x_14 = lean_unsigned_to_nat(1024u);
x_15 = lean_mk_string_unchecked("let ", 4, 4);
x_16 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___boxed), 6, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = lean_mk_string_unchecked("mut ", 4, 4);
x_18 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___boxed), 6, 1);
lean_closure_set(x_18, 0, x_17);
x_19 = lean_alloc_closure((void*)(l_Lean_Parser_optional_parenthesizer), 6, 1);
lean_closure_set(x_19, 0, x_18);
x_20 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doIdDecl_parenthesizer), 5, 0);
x_21 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doPatDecl_parenthesizer), 5, 0);
x_22 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer), 7, 2);
lean_closure_set(x_22, 0, x_20);
lean_closure_set(x_22, 1, x_21);
x_23 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_23, 0, x_19);
lean_closure_set(x_23, 1, x_22);
x_24 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_24, 0, x_16);
lean_closure_set(x_24, 1, x_23);
x_25 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_withPosition_parenthesizer), 6, 1);
lean_closure_set(x_25, 0, x_24);
x_26 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer), 8, 3);
lean_closure_set(x_26, 0, x_10);
lean_closure_set(x_26, 1, x_14);
lean_closure_set(x_26, 2, x_25);
x_27 = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(x_13, x_26, x_1, x_2, x_3, x_4, x_5);
return x_27;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doLetArrow_parenthesizer__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("doLetArrow", 10, 10);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("parenthesizer", 13, 13);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doLetArrow_parenthesizer), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
static lean_object* _init_l_Lean_Parser_Term_letIdDeclNoBinders() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Term", 4, 4);
x_4 = lean_mk_string_unchecked("letIdDecl", 9, 9);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = l_Lean_Parser_Term_ident;
x_7 = l_Lean_Parser_pushNone;
x_8 = l_Lean_Parser_Term_optType;
x_9 = lean_mk_string_unchecked(" := ", 4, 4);
x_10 = l_Lean_Parser_symbol(x_9);
lean_dec(x_9);
x_11 = l_Lean_Parser_andthen(x_8, x_10);
x_12 = l_Lean_Parser_andthen(x_7, x_11);
x_13 = l_Lean_Parser_andthen(x_6, x_12);
x_14 = l_Lean_Parser_atomic(x_13);
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Lean_Parser_termParser(x_15);
x_17 = l_Lean_Parser_andthen(x_14, x_16);
x_18 = l_Lean_Parser_node(x_5, x_17);
return x_18;
}
}
static lean_object* _init_l_Lean_Parser_Term_doReassign() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Term", 4, 4);
x_4 = lean_mk_string_unchecked("doReassign", 10, 10);
lean_inc(x_4);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_box(1);
x_7 = lean_box(0);
x_8 = lean_unbox(x_6);
x_9 = lean_unbox(x_7);
lean_inc(x_5);
x_10 = l_Lean_Parser_mkAntiquot(x_4, x_5, x_8, x_9);
lean_dec(x_4);
x_11 = lean_unsigned_to_nat(1024u);
x_12 = l_Lean_Parser_Term_notFollowedByRedefinedTermToken;
x_13 = l_Lean_Parser_Term_letIdDeclNoBinders;
x_14 = l_Lean_Parser_Term_letPatDecl;
x_15 = l_Lean_Parser_orelse(x_13, x_14);
x_16 = l_Lean_Parser_andthen(x_12, x_15);
lean_inc(x_5);
x_17 = l_Lean_Parser_leadingNode(x_5, x_11, x_16);
x_18 = l_Lean_Parser_withAntiquot(x_10, x_17);
x_19 = l_Lean_Parser_withCache(x_5, x_18);
return x_19;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doReassign__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = lean_mk_string_unchecked("doElem", 6, 6);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Term", 4, 4);
x_7 = lean_mk_string_unchecked("doReassign", 10, 10);
x_8 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_7);
x_9 = l_Lean_Parser_Term_doReassign;
x_10 = lean_unsigned_to_nat(1000u);
x_11 = l_Lean_Parser_addBuiltinLeadingParser(x_3, x_8, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doReassign_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Term", 4, 4);
x_5 = lean_mk_string_unchecked("doReassign", 10, 10);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(87u);
x_8 = lean_unsigned_to_nat(25u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(88u);
x_11 = lean_unsigned_to_nat(72u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_11);
x_14 = lean_unsigned_to_nat(29u);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_unsigned_to_nat(39u);
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
LEAN_EXPORT lean_object* l_Lean_Parser_Term_notFollowedByRedefinedTermToken_formatter___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Formatter_notFollowedBy_formatter___redArg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_notFollowedByRedefinedTermToken_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Formatter_notFollowedBy_formatter___redArg(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_notFollowedByRedefinedTermToken_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_Term_notFollowedByRedefinedTermToken_formatter(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_letIdDeclNoBinders_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("Parser", 6, 6);
x_8 = lean_mk_string_unchecked("Term", 4, 4);
x_9 = lean_mk_string_unchecked("letIdDecl", 9, 9);
x_10 = l_Lean_Name_mkStr4(x_6, x_7, x_8, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Parser_Term_ident_formatter), 5, 0);
x_12 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_pushNone_formatter___boxed), 5, 0);
x_13 = lean_alloc_closure((void*)(l_Lean_Parser_Term_optType_formatter), 5, 0);
x_14 = lean_mk_string_unchecked(" := ", 4, 4);
x_15 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter), 6, 1);
lean_closure_set(x_15, 0, x_14);
x_16 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_16, 0, x_13);
lean_closure_set(x_16, 1, x_15);
x_17 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_17, 0, x_12);
lean_closure_set(x_17, 1, x_16);
x_18 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_18, 0, x_11);
lean_closure_set(x_18, 1, x_17);
x_19 = lean_alloc_closure((void*)(l_Lean_Parser_atomic_formatter), 6, 1);
lean_closure_set(x_19, 0, x_18);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_alloc_closure((void*)(l_Lean_Parser_termParser_formatter___boxed), 6, 1);
lean_closure_set(x_21, 0, x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_22, 0, x_19);
lean_closure_set(x_22, 1, x_21);
x_23 = l_Lean_PrettyPrinter_Formatter_node_formatter(x_10, x_22, x_1, x_2, x_3, x_4, x_5);
return x_23;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_letIdDeclNoBinders_formatter__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = l_Lean_PrettyPrinter_formatterAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("letIdDecl", 9, 9);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("letIdDeclNoBinders", 18, 18);
x_9 = lean_mk_string_unchecked("formatter", 9, 9);
x_10 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_8, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Parser_Term_letIdDeclNoBinders_formatter), 5, 0);
x_12 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_10, x_11, x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doReassign_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("Parser", 6, 6);
x_8 = lean_mk_string_unchecked("Term", 4, 4);
x_9 = lean_mk_string_unchecked("doReassign", 10, 10);
lean_inc(x_9);
x_10 = l_Lean_Name_mkStr4(x_6, x_7, x_8, x_9);
x_11 = lean_box(1);
x_12 = lean_box(0);
lean_inc(x_10);
x_13 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(x_13, 0, x_9);
lean_closure_set(x_13, 1, x_10);
lean_closure_set(x_13, 2, x_11);
lean_closure_set(x_13, 3, x_12);
x_14 = lean_unsigned_to_nat(1024u);
x_15 = lean_alloc_closure((void*)(l_Lean_Parser_Term_notFollowedByRedefinedTermToken_formatter___boxed), 5, 0);
x_16 = lean_alloc_closure((void*)(l_Lean_Parser_Term_letIdDeclNoBinders_formatter), 5, 0);
x_17 = lean_alloc_closure((void*)(l_Lean_Parser_Term_letPatDecl_formatter), 5, 0);
x_18 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter), 7, 2);
lean_closure_set(x_18, 0, x_16);
lean_closure_set(x_18, 1, x_17);
x_19 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_19, 0, x_15);
lean_closure_set(x_19, 1, x_18);
x_20 = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(x_20, 0, x_10);
lean_closure_set(x_20, 1, x_14);
lean_closure_set(x_20, 2, x_19);
x_21 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_13, x_20, x_1, x_2, x_3, x_4, x_5);
return x_21;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doReassign_formatter__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_formatterAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("doReassign", 10, 10);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("formatter", 9, 9);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doReassign_formatter), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_notFollowedByRedefinedTermToken_parenthesizer___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Parenthesizer_notFollowedBy_parenthesizer___redArg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_notFollowedByRedefinedTermToken_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Parenthesizer_notFollowedBy_parenthesizer___redArg(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_notFollowedByRedefinedTermToken_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_Term_notFollowedByRedefinedTermToken_parenthesizer(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_letIdDeclNoBinders_parenthesizer___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Syntax_MonadTraverser_goLeft___at___Lean_PrettyPrinter_Parenthesizer_visitArgs_spec__1___redArg(x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_letIdDeclNoBinders_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_Term_letIdDeclNoBinders_parenthesizer___lam__0___boxed), 5, 0);
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
x_8 = lean_mk_string_unchecked("Parser", 6, 6);
x_9 = lean_mk_string_unchecked("Term", 4, 4);
x_10 = lean_mk_string_unchecked("letIdDecl", 9, 9);
x_11 = l_Lean_Name_mkStr4(x_7, x_8, x_9, x_10);
x_12 = lean_alloc_closure((void*)(l_Lean_Parser_Term_ident_parenthesizer), 5, 0);
x_13 = lean_alloc_closure((void*)(l_Lean_Parser_Term_optType_parenthesizer), 5, 0);
x_14 = lean_mk_string_unchecked(" := ", 4, 4);
x_15 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___boxed), 6, 1);
lean_closure_set(x_15, 0, x_14);
x_16 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_16, 0, x_13);
lean_closure_set(x_16, 1, x_15);
x_17 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_17, 0, x_6);
lean_closure_set(x_17, 1, x_16);
x_18 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doIdDecl_parenthesizer___lam__1), 7, 2);
lean_closure_set(x_18, 0, x_12);
lean_closure_set(x_18, 1, x_17);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_alloc_closure((void*)(l_Lean_Parser_termParser_parenthesizer), 6, 1);
lean_closure_set(x_20, 0, x_19);
x_21 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_21, 0, x_18);
lean_closure_set(x_21, 1, x_20);
x_22 = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer(x_11, x_21, x_1, x_2, x_3, x_4, x_5);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_letIdDeclNoBinders_parenthesizer___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_Term_letIdDeclNoBinders_parenthesizer___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_letIdDeclNoBinders_parenthesizer__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("letIdDecl", 9, 9);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("letIdDeclNoBinders", 18, 18);
x_9 = lean_mk_string_unchecked("parenthesizer", 13, 13);
x_10 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_8, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Parser_Term_letIdDeclNoBinders_parenthesizer), 5, 0);
x_12 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_10, x_11, x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doReassign_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("Parser", 6, 6);
x_8 = lean_mk_string_unchecked("Term", 4, 4);
x_9 = lean_mk_string_unchecked("doReassign", 10, 10);
lean_inc(x_9);
x_10 = l_Lean_Name_mkStr4(x_6, x_7, x_8, x_9);
x_11 = lean_box(1);
x_12 = lean_box(0);
lean_inc(x_10);
x_13 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(x_13, 0, x_9);
lean_closure_set(x_13, 1, x_10);
lean_closure_set(x_13, 2, x_11);
lean_closure_set(x_13, 3, x_12);
x_14 = lean_unsigned_to_nat(1024u);
x_15 = lean_alloc_closure((void*)(l_Lean_Parser_Term_notFollowedByRedefinedTermToken_parenthesizer___boxed), 5, 0);
x_16 = lean_alloc_closure((void*)(l_Lean_Parser_Term_letIdDeclNoBinders_parenthesizer), 5, 0);
x_17 = lean_alloc_closure((void*)(l_Lean_Parser_Term_letPatDecl_parenthesizer), 5, 0);
x_18 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer), 7, 2);
lean_closure_set(x_18, 0, x_16);
lean_closure_set(x_18, 1, x_17);
x_19 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_19, 0, x_15);
lean_closure_set(x_19, 1, x_18);
x_20 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer), 8, 3);
lean_closure_set(x_20, 0, x_10);
lean_closure_set(x_20, 1, x_14);
lean_closure_set(x_20, 2, x_19);
x_21 = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(x_13, x_20, x_1, x_2, x_3, x_4, x_5);
return x_21;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doReassign_parenthesizer__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("doReassign", 10, 10);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("parenthesizer", 13, 13);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doReassign_parenthesizer), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
static lean_object* _init_l_Lean_Parser_Term_doReassignArrow() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Term", 4, 4);
x_4 = lean_mk_string_unchecked("doReassignArrow", 15, 15);
lean_inc(x_4);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_box(1);
x_7 = lean_box(0);
x_8 = lean_unbox(x_6);
x_9 = lean_unbox(x_7);
lean_inc(x_5);
x_10 = l_Lean_Parser_mkAntiquot(x_4, x_5, x_8, x_9);
lean_dec(x_4);
x_11 = lean_unsigned_to_nat(1024u);
x_12 = l_Lean_Parser_Term_notFollowedByRedefinedTermToken;
x_13 = l_Lean_Parser_Term_doIdDecl;
x_14 = l_Lean_Parser_Term_doPatDecl;
x_15 = l_Lean_Parser_orelse(x_13, x_14);
x_16 = l_Lean_Parser_andthen(x_12, x_15);
lean_inc(x_5);
x_17 = l_Lean_Parser_leadingNode(x_5, x_11, x_16);
x_18 = l_Lean_Parser_withAntiquot(x_10, x_17);
x_19 = l_Lean_Parser_withCache(x_5, x_18);
return x_19;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doReassignArrow__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = lean_mk_string_unchecked("doElem", 6, 6);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Term", 4, 4);
x_7 = lean_mk_string_unchecked("doReassignArrow", 15, 15);
x_8 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_7);
x_9 = l_Lean_Parser_Term_doReassignArrow;
x_10 = lean_unsigned_to_nat(1000u);
x_11 = l_Lean_Parser_addBuiltinLeadingParser(x_3, x_8, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doReassignArrow_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Term", 4, 4);
x_5 = lean_mk_string_unchecked("doReassignArrow", 15, 15);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(89u);
x_8 = lean_unsigned_to_nat(25u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(90u);
x_11 = lean_unsigned_to_nat(61u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_11);
x_14 = lean_unsigned_to_nat(29u);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_unsigned_to_nat(44u);
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
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doReassignArrow_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("Parser", 6, 6);
x_8 = lean_mk_string_unchecked("Term", 4, 4);
x_9 = lean_mk_string_unchecked("doReassignArrow", 15, 15);
lean_inc(x_9);
x_10 = l_Lean_Name_mkStr4(x_6, x_7, x_8, x_9);
x_11 = lean_box(1);
x_12 = lean_box(0);
lean_inc(x_10);
x_13 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(x_13, 0, x_9);
lean_closure_set(x_13, 1, x_10);
lean_closure_set(x_13, 2, x_11);
lean_closure_set(x_13, 3, x_12);
x_14 = lean_unsigned_to_nat(1024u);
x_15 = lean_alloc_closure((void*)(l_Lean_Parser_Term_notFollowedByRedefinedTermToken_formatter___boxed), 5, 0);
x_16 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doIdDecl_formatter), 5, 0);
x_17 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doPatDecl_formatter), 5, 0);
x_18 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter), 7, 2);
lean_closure_set(x_18, 0, x_16);
lean_closure_set(x_18, 1, x_17);
x_19 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_19, 0, x_15);
lean_closure_set(x_19, 1, x_18);
x_20 = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(x_20, 0, x_10);
lean_closure_set(x_20, 1, x_14);
lean_closure_set(x_20, 2, x_19);
x_21 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_13, x_20, x_1, x_2, x_3, x_4, x_5);
return x_21;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doReassignArrow_formatter__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_formatterAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("doReassignArrow", 15, 15);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("formatter", 9, 9);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doReassignArrow_formatter), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doReassignArrow_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("Parser", 6, 6);
x_8 = lean_mk_string_unchecked("Term", 4, 4);
x_9 = lean_mk_string_unchecked("doReassignArrow", 15, 15);
lean_inc(x_9);
x_10 = l_Lean_Name_mkStr4(x_6, x_7, x_8, x_9);
x_11 = lean_box(1);
x_12 = lean_box(0);
lean_inc(x_10);
x_13 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(x_13, 0, x_9);
lean_closure_set(x_13, 1, x_10);
lean_closure_set(x_13, 2, x_11);
lean_closure_set(x_13, 3, x_12);
x_14 = lean_unsigned_to_nat(1024u);
x_15 = lean_alloc_closure((void*)(l_Lean_Parser_Term_notFollowedByRedefinedTermToken_parenthesizer___boxed), 5, 0);
x_16 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doIdDecl_parenthesizer), 5, 0);
x_17 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doPatDecl_parenthesizer), 5, 0);
x_18 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer), 7, 2);
lean_closure_set(x_18, 0, x_16);
lean_closure_set(x_18, 1, x_17);
x_19 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_19, 0, x_15);
lean_closure_set(x_19, 1, x_18);
x_20 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer), 8, 3);
lean_closure_set(x_20, 0, x_10);
lean_closure_set(x_20, 1, x_14);
lean_closure_set(x_20, 2, x_19);
x_21 = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(x_13, x_20, x_1, x_2, x_3, x_4, x_5);
return x_21;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doReassignArrow_parenthesizer__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("doReassignArrow", 15, 15);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("parenthesizer", 13, 13);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doReassignArrow_parenthesizer), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
static lean_object* _init_l_Lean_Parser_Term_doHave() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Term", 4, 4);
x_4 = lean_mk_string_unchecked("doHave", 6, 6);
lean_inc(x_4);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_box(1);
x_7 = lean_box(0);
x_8 = lean_unbox(x_6);
x_9 = lean_unbox(x_7);
lean_inc(x_5);
x_10 = l_Lean_Parser_mkAntiquot(x_4, x_5, x_8, x_9);
lean_dec(x_4);
x_11 = lean_unsigned_to_nat(1024u);
x_12 = lean_mk_string_unchecked("have", 4, 4);
x_13 = l_Lean_Parser_symbol(x_12);
lean_dec(x_12);
x_14 = l_Lean_Parser_Term_haveDecl;
x_15 = l_Lean_Parser_andthen(x_13, x_14);
lean_inc(x_5);
x_16 = l_Lean_Parser_leadingNode(x_5, x_11, x_15);
x_17 = l_Lean_Parser_withAntiquot(x_10, x_16);
x_18 = l_Lean_Parser_withCache(x_5, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doHave__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = lean_mk_string_unchecked("doElem", 6, 6);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Term", 4, 4);
x_7 = lean_mk_string_unchecked("doHave", 6, 6);
x_8 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_7);
x_9 = l_Lean_Parser_Term_doHave;
x_10 = lean_unsigned_to_nat(1000u);
x_11 = l_Lean_Parser_addBuiltinLeadingParser(x_3, x_8, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doHave_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Term", 4, 4);
x_5 = lean_mk_string_unchecked("doHave", 6, 6);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(91u);
x_8 = lean_unsigned_to_nat(25u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(92u);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_8);
x_12 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_8);
lean_ctor_set(x_12, 2, x_11);
lean_ctor_set(x_12, 3, x_8);
x_13 = lean_unsigned_to_nat(29u);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_unsigned_to_nat(35u);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_7);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_13);
lean_ctor_set(x_17, 2, x_16);
lean_ctor_set(x_17, 3, x_15);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_addBuiltinDeclarationRanges(x_6, x_18, x_1);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doHave_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("Parser", 6, 6);
x_8 = lean_mk_string_unchecked("Term", 4, 4);
x_9 = lean_mk_string_unchecked("doHave", 6, 6);
lean_inc(x_9);
x_10 = l_Lean_Name_mkStr4(x_6, x_7, x_8, x_9);
x_11 = lean_box(1);
x_12 = lean_box(0);
lean_inc(x_10);
x_13 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(x_13, 0, x_9);
lean_closure_set(x_13, 1, x_10);
lean_closure_set(x_13, 2, x_11);
lean_closure_set(x_13, 3, x_12);
x_14 = lean_unsigned_to_nat(1024u);
x_15 = lean_mk_string_unchecked("have", 4, 4);
x_16 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter), 6, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = lean_alloc_closure((void*)(l_Lean_Parser_Term_haveDecl_formatter), 5, 0);
x_18 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_18, 0, x_16);
lean_closure_set(x_18, 1, x_17);
x_19 = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(x_19, 0, x_10);
lean_closure_set(x_19, 1, x_14);
lean_closure_set(x_19, 2, x_18);
x_20 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_13, x_19, x_1, x_2, x_3, x_4, x_5);
return x_20;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doHave_formatter__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_formatterAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("doHave", 6, 6);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("formatter", 9, 9);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doHave_formatter), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doHave_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("Parser", 6, 6);
x_8 = lean_mk_string_unchecked("Term", 4, 4);
x_9 = lean_mk_string_unchecked("doHave", 6, 6);
lean_inc(x_9);
x_10 = l_Lean_Name_mkStr4(x_6, x_7, x_8, x_9);
x_11 = lean_box(1);
x_12 = lean_box(0);
lean_inc(x_10);
x_13 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(x_13, 0, x_9);
lean_closure_set(x_13, 1, x_10);
lean_closure_set(x_13, 2, x_11);
lean_closure_set(x_13, 3, x_12);
x_14 = lean_unsigned_to_nat(1024u);
x_15 = lean_mk_string_unchecked("have", 4, 4);
x_16 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___boxed), 6, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = lean_alloc_closure((void*)(l_Lean_Parser_Term_haveDecl_parenthesizer), 5, 0);
x_18 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_18, 0, x_16);
lean_closure_set(x_18, 1, x_17);
x_19 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer), 8, 3);
lean_closure_set(x_19, 0, x_10);
lean_closure_set(x_19, 1, x_14);
lean_closure_set(x_19, 2, x_18);
x_20 = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(x_13, x_19, x_1, x_2, x_3, x_4, x_5);
return x_20;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doHave_parenthesizer__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("doHave", 6, 6);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("parenthesizer", 13, 13);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doHave_parenthesizer), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
static lean_object* _init_l_Lean_Parser_Term_elseIf() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_1 = lean_mk_string_unchecked("else ", 5, 5);
x_2 = l_Lean_Parser_symbol(x_1);
lean_dec(x_1);
x_3 = lean_mk_string_unchecked("checkLineEq", 11, 11);
x_4 = l_Lean_Parser_checkLineEq(x_3);
x_5 = lean_mk_string_unchecked(" if ", 4, 4);
x_6 = l_Lean_Parser_symbol(x_5);
lean_dec(x_5);
x_7 = l_Lean_Parser_andthen(x_4, x_6);
x_8 = l_Lean_Parser_andthen(x_2, x_7);
x_9 = l_Lean_Parser_withPosition(x_8);
x_10 = lean_mk_string_unchecked("group", 5, 5);
x_11 = l_Lean_Name_mkStr1(x_10);
x_12 = l_Lean_Parser_node(x_11, x_9);
x_13 = l_Lean_Parser_atomic(x_12);
return x_13;
}
}
static lean_object* _init_l_Lean_Parser_Term_doIfLetPure() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Term", 4, 4);
x_4 = lean_mk_string_unchecked("doIfLetPure", 11, 11);
lean_inc(x_4);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_box(1);
x_7 = lean_box(0);
x_8 = lean_unbox(x_6);
x_9 = lean_unbox(x_7);
lean_inc(x_5);
x_10 = l_Lean_Parser_mkAntiquot(x_4, x_5, x_8, x_9);
lean_dec(x_4);
x_11 = lean_unsigned_to_nat(1024u);
x_12 = lean_mk_string_unchecked(" := ", 4, 4);
x_13 = l_Lean_Parser_symbol(x_12);
lean_dec(x_12);
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Lean_Parser_termParser(x_14);
x_16 = l_Lean_Parser_andthen(x_13, x_15);
lean_inc(x_5);
x_17 = l_Lean_Parser_leadingNode(x_5, x_11, x_16);
x_18 = l_Lean_Parser_withAntiquot(x_10, x_17);
x_19 = l_Lean_Parser_withCache(x_5, x_18);
return x_19;
}
}
static lean_object* _init_l_Lean_Parser_Term_doIfLetBind() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Term", 4, 4);
x_4 = lean_mk_string_unchecked("doIfLetBind", 11, 11);
lean_inc(x_4);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_box(1);
x_7 = lean_box(0);
x_8 = lean_unbox(x_6);
x_9 = lean_unbox(x_7);
lean_inc(x_5);
x_10 = l_Lean_Parser_mkAntiquot(x_4, x_5, x_8, x_9);
lean_dec(x_4);
x_11 = lean_unsigned_to_nat(1024u);
x_12 = l_Lean_Parser_Term_leftArrow;
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Lean_Parser_termParser(x_13);
x_15 = l_Lean_Parser_andthen(x_12, x_14);
lean_inc(x_5);
x_16 = l_Lean_Parser_leadingNode(x_5, x_11, x_15);
x_17 = l_Lean_Parser_withAntiquot(x_10, x_16);
x_18 = l_Lean_Parser_withCache(x_5, x_17);
return x_18;
}
}
static lean_object* _init_l_Lean_Parser_Term_doIfLet() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Term", 4, 4);
x_4 = lean_mk_string_unchecked("doIfLet", 7, 7);
lean_inc(x_4);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_box(0);
x_7 = lean_unbox(x_6);
x_8 = lean_unbox(x_6);
lean_inc(x_5);
x_9 = l_Lean_Parser_mkAntiquot(x_4, x_5, x_7, x_8);
lean_dec(x_4);
x_10 = lean_unsigned_to_nat(1024u);
x_11 = lean_mk_string_unchecked("let ", 4, 4);
x_12 = l_Lean_Parser_symbol(x_11);
lean_dec(x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Lean_Parser_termParser(x_13);
x_15 = l_Lean_Parser_Term_doIfLetPure;
x_16 = l_Lean_Parser_Term_doIfLetBind;
x_17 = l_Lean_Parser_orelse(x_15, x_16);
x_18 = l_Lean_Parser_andthen(x_14, x_17);
x_19 = l_Lean_Parser_andthen(x_12, x_18);
lean_inc(x_5);
x_20 = l_Lean_Parser_leadingNode(x_5, x_10, x_19);
x_21 = l_Lean_Parser_withAntiquot(x_9, x_20);
x_22 = l_Lean_Parser_withCache(x_5, x_21);
return x_22;
}
}
static lean_object* _init_l_Lean_Parser_Term_doIfProp() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Term", 4, 4);
x_4 = lean_mk_string_unchecked("doIfProp", 8, 8);
lean_inc(x_4);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_box(0);
x_7 = lean_unbox(x_6);
x_8 = lean_unbox(x_6);
lean_inc(x_5);
x_9 = l_Lean_Parser_mkAntiquot(x_4, x_5, x_7, x_8);
lean_dec(x_4);
x_10 = lean_unsigned_to_nat(1024u);
x_11 = l_Lean_Parser_Term_optIdent;
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Lean_Parser_termParser(x_12);
x_14 = l_Lean_Parser_andthen(x_11, x_13);
lean_inc(x_5);
x_15 = l_Lean_Parser_leadingNode(x_5, x_10, x_14);
x_16 = l_Lean_Parser_withAntiquot(x_9, x_15);
x_17 = l_Lean_Parser_withCache(x_5, x_16);
return x_17;
}
}
static lean_object* _init_l_Lean_Parser_Term_doIfCond() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_1 = lean_mk_string_unchecked("doIfCond", 8, 8);
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Term", 4, 4);
lean_inc(x_1);
x_5 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_1);
x_6 = lean_box(0);
x_7 = lean_box(1);
x_8 = lean_unbox(x_6);
x_9 = lean_unbox(x_7);
x_10 = l_Lean_Parser_mkAntiquot(x_1, x_5, x_8, x_9);
lean_dec(x_1);
x_11 = l_Lean_Parser_Term_doIfLet;
x_12 = l_Lean_Parser_Term_doIfProp;
x_13 = l_Lean_Parser_orelse(x_11, x_12);
x_14 = l_Lean_Parser_withAntiquot(x_10, x_13);
return x_14;
}
}
static lean_object* _init_l_Lean_Parser_Term_doIf() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Term", 4, 4);
x_4 = lean_mk_string_unchecked("doIf", 4, 4);
lean_inc(x_4);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_box(1);
x_7 = lean_box(0);
x_8 = lean_unbox(x_6);
x_9 = lean_unbox(x_7);
lean_inc(x_5);
x_10 = l_Lean_Parser_mkAntiquot(x_4, x_5, x_8, x_9);
lean_dec(x_4);
x_11 = lean_unsigned_to_nat(1024u);
x_12 = lean_mk_string_unchecked("if ", 3, 3);
x_13 = l_Lean_Parser_symbol(x_12);
lean_dec(x_12);
x_14 = l_Lean_Parser_Term_doIfCond;
x_15 = lean_mk_string_unchecked(" then", 5, 5);
x_16 = l_Lean_Parser_symbol(x_15);
lean_dec(x_15);
x_17 = l_Lean_Parser_andthen(x_14, x_16);
x_18 = l_Lean_Parser_andthen(x_13, x_17);
x_19 = l_Lean_Parser_skip;
x_20 = l_Lean_Parser_Term_doSeq;
x_21 = l_Lean_Parser_andthen(x_19, x_20);
x_22 = l_Lean_Parser_andthen(x_18, x_21);
x_23 = lean_mk_string_unchecked("'else if' in 'do' must be indented", 34, 34);
x_24 = l_Lean_Parser_checkColGe(x_23);
x_25 = l_Lean_Parser_Term_elseIf;
x_26 = lean_mk_string_unchecked(" then ", 6, 6);
x_27 = l_Lean_Parser_symbol(x_26);
lean_dec(x_26);
x_28 = l_Lean_Parser_andthen(x_27, x_20);
x_29 = l_Lean_Parser_andthen(x_14, x_28);
x_30 = l_Lean_Parser_andthen(x_25, x_29);
x_31 = l_Lean_Parser_andthen(x_19, x_30);
x_32 = lean_mk_string_unchecked("group", 5, 5);
x_33 = l_Lean_Name_mkStr1(x_32);
x_34 = l_Lean_Parser_node(x_33, x_31);
x_35 = l_Lean_Parser_andthen(x_24, x_34);
x_36 = l_Lean_Parser_many(x_35);
x_37 = lean_mk_string_unchecked("'else' in 'do' must be indented", 31, 31);
x_38 = l_Lean_Parser_checkColGe(x_37);
x_39 = lean_mk_string_unchecked("else ", 5, 5);
x_40 = l_Lean_Parser_symbol(x_39);
lean_dec(x_39);
x_41 = l_Lean_Parser_andthen(x_40, x_20);
x_42 = l_Lean_Parser_andthen(x_19, x_41);
x_43 = l_Lean_Parser_andthen(x_38, x_42);
x_44 = l_Lean_Parser_optional(x_43);
x_45 = l_Lean_Parser_andthen(x_36, x_44);
x_46 = l_Lean_Parser_andthen(x_22, x_45);
x_47 = l_Lean_Parser_withPositionAfterLinebreak(x_46);
x_48 = l_Lean_Parser_withResetCache(x_47);
lean_inc(x_5);
x_49 = l_Lean_Parser_leadingNode(x_5, x_11, x_48);
x_50 = l_Lean_Parser_withAntiquot(x_10, x_49);
x_51 = l_Lean_Parser_withCache(x_5, x_50);
return x_51;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doIf__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = lean_mk_string_unchecked("doElem", 6, 6);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Term", 4, 4);
x_7 = lean_mk_string_unchecked("doIf", 4, 4);
x_8 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_7);
x_9 = l_Lean_Parser_Term_doIf;
x_10 = lean_unsigned_to_nat(1000u);
x_11 = l_Lean_Parser_addBuiltinLeadingParser(x_3, x_8, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doIf_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Term", 4, 4);
x_5 = lean_mk_string_unchecked("doIf", 4, 4);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(136u);
x_8 = lean_unsigned_to_nat(25u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(141u);
x_11 = lean_unsigned_to_nat(54u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_11);
x_14 = lean_unsigned_to_nat(29u);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_unsigned_to_nat(33u);
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
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doIfLetPure_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("Parser", 6, 6);
x_8 = lean_mk_string_unchecked("Term", 4, 4);
x_9 = lean_mk_string_unchecked("doIfLetPure", 11, 11);
lean_inc(x_9);
x_10 = l_Lean_Name_mkStr4(x_6, x_7, x_8, x_9);
x_11 = lean_box(1);
x_12 = lean_box(0);
lean_inc(x_10);
x_13 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(x_13, 0, x_9);
lean_closure_set(x_13, 1, x_10);
lean_closure_set(x_13, 2, x_11);
lean_closure_set(x_13, 3, x_12);
x_14 = lean_unsigned_to_nat(1024u);
x_15 = lean_mk_string_unchecked(" := ", 4, 4);
x_16 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter), 6, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_alloc_closure((void*)(l_Lean_Parser_termParser_formatter___boxed), 6, 1);
lean_closure_set(x_18, 0, x_17);
x_19 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_19, 0, x_16);
lean_closure_set(x_19, 1, x_18);
x_20 = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(x_20, 0, x_10);
lean_closure_set(x_20, 1, x_14);
lean_closure_set(x_20, 2, x_19);
x_21 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_13, x_20, x_1, x_2, x_3, x_4, x_5);
return x_21;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doIfLetPure_formatter__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_formatterAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("doIfLetPure", 11, 11);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("formatter", 9, 9);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doIfLetPure_formatter), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doIfLetBind_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("Parser", 6, 6);
x_8 = lean_mk_string_unchecked("Term", 4, 4);
x_9 = lean_mk_string_unchecked("doIfLetBind", 11, 11);
lean_inc(x_9);
x_10 = l_Lean_Name_mkStr4(x_6, x_7, x_8, x_9);
x_11 = lean_box(1);
x_12 = lean_box(0);
lean_inc(x_10);
x_13 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(x_13, 0, x_9);
lean_closure_set(x_13, 1, x_10);
lean_closure_set(x_13, 2, x_11);
lean_closure_set(x_13, 3, x_12);
x_14 = lean_unsigned_to_nat(1024u);
x_15 = lean_alloc_closure((void*)(l_Lean_Parser_Term_leftArrow_formatter), 5, 0);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_alloc_closure((void*)(l_Lean_Parser_termParser_formatter___boxed), 6, 1);
lean_closure_set(x_17, 0, x_16);
x_18 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_18, 0, x_15);
lean_closure_set(x_18, 1, x_17);
x_19 = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(x_19, 0, x_10);
lean_closure_set(x_19, 1, x_14);
lean_closure_set(x_19, 2, x_18);
x_20 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_13, x_19, x_1, x_2, x_3, x_4, x_5);
return x_20;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doIfLetBind_formatter__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_formatterAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("doIfLetBind", 11, 11);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("formatter", 9, 9);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doIfLetBind_formatter), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doIfLet_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("Parser", 6, 6);
x_8 = lean_mk_string_unchecked("Term", 4, 4);
x_9 = lean_mk_string_unchecked("doIfLet", 7, 7);
lean_inc(x_9);
x_10 = l_Lean_Name_mkStr4(x_6, x_7, x_8, x_9);
x_11 = lean_box(0);
lean_inc(x_10);
x_12 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(x_12, 0, x_9);
lean_closure_set(x_12, 1, x_10);
lean_closure_set(x_12, 2, x_11);
lean_closure_set(x_12, 3, x_11);
x_13 = lean_unsigned_to_nat(1024u);
x_14 = lean_mk_string_unchecked("let ", 4, 4);
x_15 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter), 6, 1);
lean_closure_set(x_15, 0, x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_alloc_closure((void*)(l_Lean_Parser_termParser_formatter___boxed), 6, 1);
lean_closure_set(x_17, 0, x_16);
x_18 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doIfLetPure_formatter), 5, 0);
x_19 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doIfLetBind_formatter), 5, 0);
x_20 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter), 7, 2);
lean_closure_set(x_20, 0, x_18);
lean_closure_set(x_20, 1, x_19);
x_21 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_21, 0, x_17);
lean_closure_set(x_21, 1, x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_22, 0, x_15);
lean_closure_set(x_22, 1, x_21);
x_23 = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(x_23, 0, x_10);
lean_closure_set(x_23, 1, x_13);
lean_closure_set(x_23, 2, x_22);
x_24 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_12, x_23, x_1, x_2, x_3, x_4, x_5);
return x_24;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doIfLet_formatter__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_formatterAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("doIfLet", 7, 7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("formatter", 9, 9);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doIfLet_formatter), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doIfProp_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("Parser", 6, 6);
x_8 = lean_mk_string_unchecked("Term", 4, 4);
x_9 = lean_mk_string_unchecked("doIfProp", 8, 8);
lean_inc(x_9);
x_10 = l_Lean_Name_mkStr4(x_6, x_7, x_8, x_9);
x_11 = lean_box(0);
lean_inc(x_10);
x_12 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(x_12, 0, x_9);
lean_closure_set(x_12, 1, x_10);
lean_closure_set(x_12, 2, x_11);
lean_closure_set(x_12, 3, x_11);
x_13 = lean_unsigned_to_nat(1024u);
x_14 = lean_alloc_closure((void*)(l_Lean_Parser_Term_optIdent_formatter), 5, 0);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_alloc_closure((void*)(l_Lean_Parser_termParser_formatter___boxed), 6, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_17, 0, x_14);
lean_closure_set(x_17, 1, x_16);
x_18 = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(x_18, 0, x_10);
lean_closure_set(x_18, 1, x_13);
lean_closure_set(x_18, 2, x_17);
x_19 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_12, x_18, x_1, x_2, x_3, x_4, x_5);
return x_19;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doIfProp_formatter__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_formatterAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("doIfProp", 8, 8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("formatter", 9, 9);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doIfProp_formatter), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doIfCond_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_6 = lean_mk_string_unchecked("doIfCond", 8, 8);
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
x_8 = lean_mk_string_unchecked("Parser", 6, 6);
x_9 = lean_mk_string_unchecked("Term", 4, 4);
lean_inc(x_6);
x_10 = l_Lean_Name_mkStr4(x_7, x_8, x_9, x_6);
x_11 = lean_box(0);
x_12 = lean_box(1);
x_13 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(x_13, 0, x_6);
lean_closure_set(x_13, 1, x_10);
lean_closure_set(x_13, 2, x_11);
lean_closure_set(x_13, 3, x_12);
x_14 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doIfLet_formatter), 5, 0);
x_15 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doIfProp_formatter), 5, 0);
x_16 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter), 7, 2);
lean_closure_set(x_16, 0, x_14);
lean_closure_set(x_16, 1, x_15);
x_17 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_13, x_16, x_1, x_2, x_3, x_4, x_5);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_elseIf_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = lean_mk_string_unchecked("else ", 5, 5);
x_7 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter), 6, 1);
lean_closure_set(x_7, 0, x_6);
x_8 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkLineEq_formatter___boxed), 5, 0);
x_9 = lean_mk_string_unchecked(" if ", 4, 4);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter), 6, 1);
lean_closure_set(x_10, 0, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_11, 0, x_8);
lean_closure_set(x_11, 1, x_10);
x_12 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_12, 0, x_7);
lean_closure_set(x_12, 1, x_11);
x_13 = lean_alloc_closure((void*)(l_Lean_Parser_withPosition_formatter), 6, 1);
lean_closure_set(x_13, 0, x_12);
x_14 = l_Lean_Parser_group_formatter(x_13, x_1, x_2, x_3, x_4, x_5);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doIf_formatter___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Formatter_fill(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doIf_formatter___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Formatter_group(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doIf_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doIdDecl_formatter___lam__0___boxed), 5, 0);
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
x_8 = lean_mk_string_unchecked("Parser", 6, 6);
x_9 = lean_mk_string_unchecked("Term", 4, 4);
x_10 = lean_mk_string_unchecked("doIf", 4, 4);
lean_inc(x_10);
x_11 = l_Lean_Name_mkStr4(x_7, x_8, x_9, x_10);
x_12 = lean_box(1);
x_13 = lean_box(0);
lean_inc(x_11);
x_14 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(x_14, 0, x_10);
lean_closure_set(x_14, 1, x_11);
lean_closure_set(x_14, 2, x_12);
lean_closure_set(x_14, 3, x_13);
x_15 = lean_unsigned_to_nat(1024u);
x_16 = lean_mk_string_unchecked("if ", 3, 3);
x_17 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter), 6, 1);
lean_closure_set(x_17, 0, x_16);
x_18 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doIfCond_formatter), 5, 0);
x_19 = lean_mk_string_unchecked(" then", 5, 5);
x_20 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter), 6, 1);
lean_closure_set(x_20, 0, x_19);
lean_inc(x_18);
x_21 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_21, 0, x_18);
lean_closure_set(x_21, 1, x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_22, 0, x_17);
lean_closure_set(x_22, 1, x_21);
x_23 = lean_alloc_closure((void*)(l_Lean_ppIndent_formatter), 6, 1);
lean_closure_set(x_23, 0, x_22);
x_24 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doSeq_formatter), 5, 0);
lean_inc(x_24);
lean_inc(x_6);
x_25 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_25, 0, x_6);
lean_closure_set(x_25, 1, x_24);
x_26 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_26, 0, x_23);
lean_closure_set(x_26, 1, x_25);
x_27 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doIf_formatter___lam__1), 6, 1);
lean_closure_set(x_27, 0, x_26);
x_28 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkColGe_formatter___boxed), 5, 0);
x_29 = lean_alloc_closure((void*)(l_Lean_ppDedent_formatter), 6, 1);
lean_closure_set(x_29, 0, x_6);
x_30 = lean_alloc_closure((void*)(l_Lean_Parser_Term_elseIf_formatter), 5, 0);
x_31 = lean_mk_string_unchecked(" then ", 6, 6);
x_32 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter), 6, 1);
lean_closure_set(x_32, 0, x_31);
lean_inc(x_24);
x_33 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_33, 0, x_32);
lean_closure_set(x_33, 1, x_24);
x_34 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_34, 0, x_18);
lean_closure_set(x_34, 1, x_33);
x_35 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_35, 0, x_30);
lean_closure_set(x_35, 1, x_34);
x_36 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doIf_formatter___lam__1), 6, 1);
lean_closure_set(x_36, 0, x_35);
lean_inc(x_29);
x_37 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_37, 0, x_29);
lean_closure_set(x_37, 1, x_36);
x_38 = lean_alloc_closure((void*)(l_Lean_Parser_group_formatter), 6, 1);
lean_closure_set(x_38, 0, x_37);
lean_inc(x_28);
x_39 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_39, 0, x_28);
lean_closure_set(x_39, 1, x_38);
x_40 = lean_alloc_closure((void*)(l_Lean_Parser_many_formatter), 6, 1);
lean_closure_set(x_40, 0, x_39);
x_41 = lean_mk_string_unchecked("else ", 5, 5);
x_42 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter), 6, 1);
lean_closure_set(x_42, 0, x_41);
x_43 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_43, 0, x_42);
lean_closure_set(x_43, 1, x_24);
x_44 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doIf_formatter___lam__1), 6, 1);
lean_closure_set(x_44, 0, x_43);
x_45 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_45, 0, x_29);
lean_closure_set(x_45, 1, x_44);
x_46 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_46, 0, x_28);
lean_closure_set(x_46, 1, x_45);
x_47 = lean_alloc_closure((void*)(l_Lean_Parser_optional_formatter), 6, 1);
lean_closure_set(x_47, 0, x_46);
x_48 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_48, 0, x_40);
lean_closure_set(x_48, 1, x_47);
x_49 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_49, 0, x_27);
lean_closure_set(x_49, 1, x_48);
x_50 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doIf_formatter___lam__3), 6, 1);
lean_closure_set(x_50, 0, x_49);
x_51 = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(x_51, 0, x_11);
lean_closure_set(x_51, 1, x_15);
lean_closure_set(x_51, 2, x_50);
x_52 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_14, x_51, x_1, x_2, x_3, x_4, x_5);
return x_52;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doIf_formatter__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_formatterAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("doIf", 4, 4);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("formatter", 9, 9);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doIf_formatter), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doIfLetPure_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("Parser", 6, 6);
x_8 = lean_mk_string_unchecked("Term", 4, 4);
x_9 = lean_mk_string_unchecked("doIfLetPure", 11, 11);
lean_inc(x_9);
x_10 = l_Lean_Name_mkStr4(x_6, x_7, x_8, x_9);
x_11 = lean_box(1);
x_12 = lean_box(0);
lean_inc(x_10);
x_13 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(x_13, 0, x_9);
lean_closure_set(x_13, 1, x_10);
lean_closure_set(x_13, 2, x_11);
lean_closure_set(x_13, 3, x_12);
x_14 = lean_unsigned_to_nat(1024u);
x_15 = lean_mk_string_unchecked(" := ", 4, 4);
x_16 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___boxed), 6, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_alloc_closure((void*)(l_Lean_Parser_termParser_parenthesizer), 6, 1);
lean_closure_set(x_18, 0, x_17);
x_19 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_19, 0, x_16);
lean_closure_set(x_19, 1, x_18);
x_20 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer), 8, 3);
lean_closure_set(x_20, 0, x_10);
lean_closure_set(x_20, 1, x_14);
lean_closure_set(x_20, 2, x_19);
x_21 = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(x_13, x_20, x_1, x_2, x_3, x_4, x_5);
return x_21;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doIfLetPure_parenthesizer__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("doIfLetPure", 11, 11);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("parenthesizer", 13, 13);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doIfLetPure_parenthesizer), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doIfLetBind_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("Parser", 6, 6);
x_8 = lean_mk_string_unchecked("Term", 4, 4);
x_9 = lean_mk_string_unchecked("doIfLetBind", 11, 11);
lean_inc(x_9);
x_10 = l_Lean_Name_mkStr4(x_6, x_7, x_8, x_9);
x_11 = lean_box(1);
x_12 = lean_box(0);
lean_inc(x_10);
x_13 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(x_13, 0, x_9);
lean_closure_set(x_13, 1, x_10);
lean_closure_set(x_13, 2, x_11);
lean_closure_set(x_13, 3, x_12);
x_14 = lean_unsigned_to_nat(1024u);
x_15 = lean_alloc_closure((void*)(l_Lean_Parser_Term_leftArrow_parenthesizer), 5, 0);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_alloc_closure((void*)(l_Lean_Parser_termParser_parenthesizer), 6, 1);
lean_closure_set(x_17, 0, x_16);
x_18 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_18, 0, x_15);
lean_closure_set(x_18, 1, x_17);
x_19 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer), 8, 3);
lean_closure_set(x_19, 0, x_10);
lean_closure_set(x_19, 1, x_14);
lean_closure_set(x_19, 2, x_18);
x_20 = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(x_13, x_19, x_1, x_2, x_3, x_4, x_5);
return x_20;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doIfLetBind_parenthesizer__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("doIfLetBind", 11, 11);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("parenthesizer", 13, 13);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doIfLetBind_parenthesizer), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doIfLet_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("Parser", 6, 6);
x_8 = lean_mk_string_unchecked("Term", 4, 4);
x_9 = lean_mk_string_unchecked("doIfLet", 7, 7);
lean_inc(x_9);
x_10 = l_Lean_Name_mkStr4(x_6, x_7, x_8, x_9);
x_11 = lean_box(0);
lean_inc(x_10);
x_12 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(x_12, 0, x_9);
lean_closure_set(x_12, 1, x_10);
lean_closure_set(x_12, 2, x_11);
lean_closure_set(x_12, 3, x_11);
x_13 = lean_unsigned_to_nat(1024u);
x_14 = lean_mk_string_unchecked("let ", 4, 4);
x_15 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___boxed), 6, 1);
lean_closure_set(x_15, 0, x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_alloc_closure((void*)(l_Lean_Parser_termParser_parenthesizer), 6, 1);
lean_closure_set(x_17, 0, x_16);
x_18 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doIfLetPure_parenthesizer), 5, 0);
x_19 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doIfLetBind_parenthesizer), 5, 0);
x_20 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer), 7, 2);
lean_closure_set(x_20, 0, x_18);
lean_closure_set(x_20, 1, x_19);
x_21 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_21, 0, x_17);
lean_closure_set(x_21, 1, x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_22, 0, x_15);
lean_closure_set(x_22, 1, x_21);
x_23 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer), 8, 3);
lean_closure_set(x_23, 0, x_10);
lean_closure_set(x_23, 1, x_13);
lean_closure_set(x_23, 2, x_22);
x_24 = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(x_12, x_23, x_1, x_2, x_3, x_4, x_5);
return x_24;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doIfLet_parenthesizer__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("doIfLet", 7, 7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("parenthesizer", 13, 13);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doIfLet_parenthesizer), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doIfProp_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("Parser", 6, 6);
x_8 = lean_mk_string_unchecked("Term", 4, 4);
x_9 = lean_mk_string_unchecked("doIfProp", 8, 8);
lean_inc(x_9);
x_10 = l_Lean_Name_mkStr4(x_6, x_7, x_8, x_9);
x_11 = lean_box(0);
lean_inc(x_10);
x_12 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(x_12, 0, x_9);
lean_closure_set(x_12, 1, x_10);
lean_closure_set(x_12, 2, x_11);
lean_closure_set(x_12, 3, x_11);
x_13 = lean_unsigned_to_nat(1024u);
x_14 = lean_alloc_closure((void*)(l_Lean_Parser_Term_optIdent_parenthesizer), 5, 0);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_alloc_closure((void*)(l_Lean_Parser_termParser_parenthesizer), 6, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_17, 0, x_14);
lean_closure_set(x_17, 1, x_16);
x_18 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer), 8, 3);
lean_closure_set(x_18, 0, x_10);
lean_closure_set(x_18, 1, x_13);
lean_closure_set(x_18, 2, x_17);
x_19 = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(x_12, x_18, x_1, x_2, x_3, x_4, x_5);
return x_19;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doIfProp_parenthesizer__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("doIfProp", 8, 8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("parenthesizer", 13, 13);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doIfProp_parenthesizer), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doIfCond_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_6 = lean_mk_string_unchecked("doIfCond", 8, 8);
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
x_8 = lean_mk_string_unchecked("Parser", 6, 6);
x_9 = lean_mk_string_unchecked("Term", 4, 4);
lean_inc(x_6);
x_10 = l_Lean_Name_mkStr4(x_7, x_8, x_9, x_6);
x_11 = lean_box(0);
x_12 = lean_box(1);
x_13 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(x_13, 0, x_6);
lean_closure_set(x_13, 1, x_10);
lean_closure_set(x_13, 2, x_11);
lean_closure_set(x_13, 3, x_12);
x_14 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doIfLet_parenthesizer), 5, 0);
x_15 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doIfProp_parenthesizer), 5, 0);
x_16 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer), 7, 2);
lean_closure_set(x_16, 0, x_14);
lean_closure_set(x_16, 1, x_15);
x_17 = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(x_13, x_16, x_1, x_2, x_3, x_4, x_5);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_elseIf_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = lean_mk_string_unchecked("else ", 5, 5);
x_7 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___boxed), 6, 1);
lean_closure_set(x_7, 0, x_6);
x_8 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkLineEq_parenthesizer___boxed), 5, 0);
x_9 = lean_mk_string_unchecked(" if ", 4, 4);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___boxed), 6, 1);
lean_closure_set(x_10, 0, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_11, 0, x_8);
lean_closure_set(x_11, 1, x_10);
x_12 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_12, 0, x_7);
lean_closure_set(x_12, 1, x_11);
x_13 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_withPosition_parenthesizer), 6, 1);
lean_closure_set(x_13, 0, x_12);
x_14 = l_Lean_Parser_group_parenthesizer(x_13, x_1, x_2, x_3, x_4, x_5);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doIf_parenthesizer___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doIf_parenthesizer___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Parenthesizer_withPosition_parenthesizer(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doIf_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doSeqItem_parenthesizer___lam__0___boxed), 5, 0);
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
x_8 = lean_mk_string_unchecked("Parser", 6, 6);
x_9 = lean_mk_string_unchecked("Term", 4, 4);
x_10 = lean_mk_string_unchecked("doIf", 4, 4);
lean_inc(x_10);
x_11 = l_Lean_Name_mkStr4(x_7, x_8, x_9, x_10);
x_12 = lean_box(1);
x_13 = lean_box(0);
lean_inc(x_11);
x_14 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(x_14, 0, x_10);
lean_closure_set(x_14, 1, x_11);
lean_closure_set(x_14, 2, x_12);
lean_closure_set(x_14, 3, x_13);
x_15 = lean_unsigned_to_nat(1024u);
x_16 = lean_mk_string_unchecked("if ", 3, 3);
x_17 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___boxed), 6, 1);
lean_closure_set(x_17, 0, x_16);
x_18 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doIfCond_parenthesizer), 5, 0);
x_19 = lean_mk_string_unchecked(" then", 5, 5);
x_20 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___boxed), 6, 1);
lean_closure_set(x_20, 0, x_19);
lean_inc(x_18);
x_21 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_21, 0, x_18);
lean_closure_set(x_21, 1, x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doIdDecl_parenthesizer___lam__1), 7, 2);
lean_closure_set(x_22, 0, x_17);
lean_closure_set(x_22, 1, x_21);
x_23 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doSeq_parenthesizer), 5, 0);
lean_inc(x_23);
lean_inc(x_6);
x_24 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_24, 0, x_6);
lean_closure_set(x_24, 1, x_23);
x_25 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doIf_parenthesizer___lam__3), 7, 2);
lean_closure_set(x_25, 0, x_22);
lean_closure_set(x_25, 1, x_24);
x_26 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkColGe_parenthesizer___boxed), 5, 0);
x_27 = lean_alloc_closure((void*)(l_Lean_Parser_Term_elseIf_parenthesizer), 5, 0);
x_28 = lean_mk_string_unchecked(" then ", 6, 6);
x_29 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___boxed), 6, 1);
lean_closure_set(x_29, 0, x_28);
lean_inc(x_23);
x_30 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_30, 0, x_29);
lean_closure_set(x_30, 1, x_23);
x_31 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_31, 0, x_18);
lean_closure_set(x_31, 1, x_30);
x_32 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doIdDecl_parenthesizer___lam__1), 7, 2);
lean_closure_set(x_32, 0, x_27);
lean_closure_set(x_32, 1, x_31);
lean_inc(x_6);
x_33 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_33, 0, x_6);
lean_closure_set(x_33, 1, x_32);
x_34 = lean_alloc_closure((void*)(l_Lean_Parser_group_parenthesizer), 6, 1);
lean_closure_set(x_34, 0, x_33);
lean_inc(x_26);
x_35 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_35, 0, x_26);
lean_closure_set(x_35, 1, x_34);
x_36 = lean_alloc_closure((void*)(l_Lean_Parser_many_parenthesizer), 6, 1);
lean_closure_set(x_36, 0, x_35);
x_37 = lean_mk_string_unchecked("else ", 5, 5);
x_38 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___boxed), 6, 1);
lean_closure_set(x_38, 0, x_37);
x_39 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doIdDecl_parenthesizer___lam__1), 7, 2);
lean_closure_set(x_39, 0, x_38);
lean_closure_set(x_39, 1, x_23);
x_40 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_40, 0, x_6);
lean_closure_set(x_40, 1, x_39);
x_41 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_41, 0, x_26);
lean_closure_set(x_41, 1, x_40);
x_42 = lean_alloc_closure((void*)(l_Lean_Parser_optional_parenthesizer), 6, 1);
lean_closure_set(x_42, 0, x_41);
x_43 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_43, 0, x_36);
lean_closure_set(x_43, 1, x_42);
x_44 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doIf_parenthesizer___lam__3), 7, 2);
lean_closure_set(x_44, 0, x_25);
lean_closure_set(x_44, 1, x_43);
x_45 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doIf_parenthesizer___lam__4), 6, 1);
lean_closure_set(x_45, 0, x_44);
x_46 = lean_alloc_closure((void*)(l_Lean_Parser_withResetCache_parenthesizer), 6, 1);
lean_closure_set(x_46, 0, x_45);
x_47 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer), 8, 3);
lean_closure_set(x_47, 0, x_11);
lean_closure_set(x_47, 1, x_15);
lean_closure_set(x_47, 2, x_46);
x_48 = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(x_14, x_47, x_1, x_2, x_3, x_4, x_5);
return x_48;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doIf_parenthesizer__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("doIf", 4, 4);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("parenthesizer", 13, 13);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doIf_parenthesizer), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
static lean_object* _init_l_Lean_Parser_Term_doUnless() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Term", 4, 4);
x_4 = lean_mk_string_unchecked("doUnless", 8, 8);
lean_inc(x_4);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_box(1);
x_7 = lean_box(0);
x_8 = lean_unbox(x_6);
x_9 = lean_unbox(x_7);
lean_inc(x_5);
x_10 = l_Lean_Parser_mkAntiquot(x_4, x_5, x_8, x_9);
lean_dec(x_4);
x_11 = lean_unsigned_to_nat(1024u);
x_12 = lean_mk_string_unchecked("unless ", 7, 7);
x_13 = l_Lean_Parser_symbol(x_12);
lean_dec(x_12);
x_14 = lean_mk_string_unchecked("do", 2, 2);
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Lean_Parser_termParser(x_15);
x_17 = l_Lean_Parser_withForbidden(x_14, x_16);
x_18 = lean_mk_string_unchecked(" do ", 4, 4);
x_19 = l_Lean_Parser_symbol(x_18);
lean_dec(x_18);
x_20 = l_Lean_Parser_Term_doSeq;
x_21 = l_Lean_Parser_andthen(x_19, x_20);
x_22 = l_Lean_Parser_andthen(x_17, x_21);
x_23 = l_Lean_Parser_andthen(x_13, x_22);
lean_inc(x_5);
x_24 = l_Lean_Parser_leadingNode(x_5, x_11, x_23);
x_25 = l_Lean_Parser_withAntiquot(x_10, x_24);
x_26 = l_Lean_Parser_withCache(x_5, x_25);
return x_26;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doUnless__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = lean_mk_string_unchecked("doElem", 6, 6);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Term", 4, 4);
x_7 = lean_mk_string_unchecked("doUnless", 8, 8);
x_8 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_7);
x_9 = l_Lean_Parser_Term_doUnless;
x_10 = lean_unsigned_to_nat(1000u);
x_11 = l_Lean_Parser_addBuiltinLeadingParser(x_3, x_8, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doUnless_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Term", 4, 4);
x_5 = lean_mk_string_unchecked("doUnless", 8, 8);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(142u);
x_8 = lean_unsigned_to_nat(25u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(143u);
x_11 = lean_unsigned_to_nat(63u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_11);
x_14 = lean_unsigned_to_nat(29u);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_unsigned_to_nat(37u);
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
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doUnless_formatter___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_termParser_formatter___redArg(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doUnless_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doUnless_formatter___lam__0), 5, 0);
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
x_8 = lean_mk_string_unchecked("Parser", 6, 6);
x_9 = lean_mk_string_unchecked("Term", 4, 4);
x_10 = lean_mk_string_unchecked("doUnless", 8, 8);
lean_inc(x_10);
x_11 = l_Lean_Name_mkStr4(x_7, x_8, x_9, x_10);
x_12 = lean_box(1);
x_13 = lean_box(0);
lean_inc(x_11);
x_14 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(x_14, 0, x_10);
lean_closure_set(x_14, 1, x_11);
lean_closure_set(x_14, 2, x_12);
lean_closure_set(x_14, 3, x_13);
x_15 = lean_unsigned_to_nat(1024u);
x_16 = lean_mk_string_unchecked("unless ", 7, 7);
x_17 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter), 6, 1);
lean_closure_set(x_17, 0, x_16);
x_18 = lean_mk_string_unchecked(" do ", 4, 4);
x_19 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter), 6, 1);
lean_closure_set(x_19, 0, x_18);
x_20 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doSeq_formatter), 5, 0);
x_21 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_21, 0, x_19);
lean_closure_set(x_21, 1, x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_22, 0, x_6);
lean_closure_set(x_22, 1, x_21);
x_23 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_23, 0, x_17);
lean_closure_set(x_23, 1, x_22);
x_24 = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(x_24, 0, x_11);
lean_closure_set(x_24, 1, x_15);
lean_closure_set(x_24, 2, x_23);
x_25 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_14, x_24, x_1, x_2, x_3, x_4, x_5);
return x_25;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doUnless_formatter__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_formatterAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("doUnless", 8, 8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("formatter", 9, 9);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doUnless_formatter), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doUnless_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("Parser", 6, 6);
x_8 = lean_mk_string_unchecked("Term", 4, 4);
x_9 = lean_mk_string_unchecked("doUnless", 8, 8);
lean_inc(x_9);
x_10 = l_Lean_Name_mkStr4(x_6, x_7, x_8, x_9);
x_11 = lean_box(1);
x_12 = lean_box(0);
lean_inc(x_10);
x_13 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(x_13, 0, x_9);
lean_closure_set(x_13, 1, x_10);
lean_closure_set(x_13, 2, x_11);
lean_closure_set(x_13, 3, x_12);
x_14 = lean_unsigned_to_nat(1024u);
x_15 = lean_mk_string_unchecked("unless ", 7, 7);
x_16 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___boxed), 6, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = lean_mk_string_unchecked("do", 2, 2);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_alloc_closure((void*)(l_Lean_Parser_termParser_parenthesizer), 6, 1);
lean_closure_set(x_19, 0, x_18);
x_20 = lean_alloc_closure((void*)(l_Lean_Parser_withForbidden_parenthesizer___boxed), 7, 2);
lean_closure_set(x_20, 0, x_17);
lean_closure_set(x_20, 1, x_19);
x_21 = lean_mk_string_unchecked(" do ", 4, 4);
x_22 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___boxed), 6, 1);
lean_closure_set(x_22, 0, x_21);
x_23 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doSeq_parenthesizer), 5, 0);
x_24 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_24, 0, x_22);
lean_closure_set(x_24, 1, x_23);
x_25 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_25, 0, x_20);
lean_closure_set(x_25, 1, x_24);
x_26 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_26, 0, x_16);
lean_closure_set(x_26, 1, x_25);
x_27 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer), 8, 3);
lean_closure_set(x_27, 0, x_10);
lean_closure_set(x_27, 1, x_14);
lean_closure_set(x_27, 2, x_26);
x_28 = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(x_13, x_27, x_1, x_2, x_3, x_4, x_5);
return x_28;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doUnless_parenthesizer__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("doUnless", 8, 8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("parenthesizer", 13, 13);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doUnless_parenthesizer), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
static lean_object* _init_l_Lean_Parser_Term_doForDecl() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Term", 4, 4);
x_4 = lean_mk_string_unchecked("doForDecl", 9, 9);
lean_inc(x_4);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_box(1);
x_7 = lean_box(0);
x_8 = lean_unbox(x_6);
x_9 = lean_unbox(x_7);
lean_inc(x_5);
x_10 = l_Lean_Parser_mkAntiquot(x_4, x_5, x_8, x_9);
lean_dec(x_4);
x_11 = lean_unsigned_to_nat(1024u);
x_12 = l_Lean_Parser_Term_ident;
x_13 = lean_mk_string_unchecked(" : ", 3, 3);
x_14 = l_Lean_Parser_symbol(x_13);
lean_dec(x_13);
x_15 = l_Lean_Parser_andthen(x_12, x_14);
x_16 = l_Lean_Parser_atomic(x_15);
x_17 = l_Lean_Parser_optional(x_16);
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Lean_Parser_termParser(x_18);
x_20 = lean_mk_string_unchecked(" in ", 4, 4);
x_21 = l_Lean_Parser_symbol(x_20);
lean_dec(x_20);
x_22 = lean_mk_string_unchecked("do", 2, 2);
lean_inc(x_19);
x_23 = l_Lean_Parser_withForbidden(x_22, x_19);
x_24 = l_Lean_Parser_andthen(x_21, x_23);
x_25 = l_Lean_Parser_andthen(x_19, x_24);
x_26 = l_Lean_Parser_andthen(x_17, x_25);
lean_inc(x_5);
x_27 = l_Lean_Parser_leadingNode(x_5, x_11, x_26);
x_28 = l_Lean_Parser_withAntiquot(x_10, x_27);
x_29 = l_Lean_Parser_withCache(x_5, x_28);
return x_29;
}
}
static lean_object* _init_l_Lean_Parser_Term_doFor() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Term", 4, 4);
x_4 = lean_mk_string_unchecked("doFor", 5, 5);
lean_inc(x_4);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_box(1);
x_7 = lean_box(0);
x_8 = lean_unbox(x_6);
x_9 = lean_unbox(x_7);
lean_inc(x_5);
x_10 = l_Lean_Parser_mkAntiquot(x_4, x_5, x_8, x_9);
lean_dec(x_4);
x_11 = lean_unsigned_to_nat(1024u);
x_12 = lean_mk_string_unchecked("for ", 4, 4);
x_13 = l_Lean_Parser_symbol(x_12);
lean_dec(x_12);
x_14 = l_Lean_Parser_Term_doForDecl;
x_15 = lean_mk_string_unchecked(", ", 2, 2);
x_16 = l_Lean_Parser_symbol(x_15);
x_17 = lean_unbox(x_7);
x_18 = l_Lean_Parser_sepBy1(x_14, x_15, x_16, x_17);
lean_dec(x_15);
x_19 = lean_mk_string_unchecked("do ", 3, 3);
x_20 = l_Lean_Parser_symbol(x_19);
lean_dec(x_19);
x_21 = l_Lean_Parser_Term_doSeq;
x_22 = l_Lean_Parser_andthen(x_20, x_21);
x_23 = l_Lean_Parser_andthen(x_18, x_22);
x_24 = l_Lean_Parser_andthen(x_13, x_23);
lean_inc(x_5);
x_25 = l_Lean_Parser_leadingNode(x_5, x_11, x_24);
x_26 = l_Lean_Parser_withAntiquot(x_10, x_25);
x_27 = l_Lean_Parser_withCache(x_5, x_26);
return x_27;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doFor__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = lean_mk_string_unchecked("doElem", 6, 6);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Term", 4, 4);
x_7 = lean_mk_string_unchecked("doFor", 5, 5);
x_8 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_7);
x_9 = l_Lean_Parser_Term_doFor;
x_10 = lean_unsigned_to_nat(1000u);
x_11 = l_Lean_Parser_addBuiltinLeadingParser(x_3, x_8, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doFor_docString__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Term", 4, 4);
x_5 = lean_mk_string_unchecked("doFor", 5, 5);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_mk_string_unchecked("`for x in e do s`  iterates over `e` assuming `e`'s type has an instance of the `ForIn` typeclass.\n`break` and `continue` are supported inside `for` loops.\n`for x in e, x2 in e2, ... do s` iterates of the given collections in parallel,\nuntil at least one of them is exhausted.\nThe types of `e2` etc. must implement the `ToStream` typeclass.\n", 341, 341);
x_8 = l_Lean_addBuiltinDocString(x_6, x_7, x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doFor_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Term", 4, 4);
x_5 = lean_mk_string_unchecked("doFor", 5, 5);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(153u);
x_8 = lean_unsigned_to_nat(25u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(154u);
x_11 = lean_unsigned_to_nat(51u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_11);
x_14 = lean_unsigned_to_nat(29u);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_unsigned_to_nat(34u);
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
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doForDecl_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doUnless_formatter___lam__0), 5, 0);
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
x_8 = lean_mk_string_unchecked("Parser", 6, 6);
x_9 = lean_mk_string_unchecked("Term", 4, 4);
x_10 = lean_mk_string_unchecked("doForDecl", 9, 9);
lean_inc(x_10);
x_11 = l_Lean_Name_mkStr4(x_7, x_8, x_9, x_10);
x_12 = lean_box(1);
x_13 = lean_box(0);
lean_inc(x_11);
x_14 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(x_14, 0, x_10);
lean_closure_set(x_14, 1, x_11);
lean_closure_set(x_14, 2, x_12);
lean_closure_set(x_14, 3, x_13);
x_15 = lean_unsigned_to_nat(1024u);
x_16 = lean_alloc_closure((void*)(l_Lean_Parser_Term_ident_formatter), 5, 0);
x_17 = lean_mk_string_unchecked(" : ", 3, 3);
x_18 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter), 6, 1);
lean_closure_set(x_18, 0, x_17);
x_19 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_19, 0, x_16);
lean_closure_set(x_19, 1, x_18);
x_20 = lean_alloc_closure((void*)(l_Lean_Parser_atomic_formatter), 6, 1);
lean_closure_set(x_20, 0, x_19);
x_21 = lean_alloc_closure((void*)(l_Lean_Parser_optional_formatter), 6, 1);
lean_closure_set(x_21, 0, x_20);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_alloc_closure((void*)(l_Lean_Parser_termParser_formatter___boxed), 6, 1);
lean_closure_set(x_23, 0, x_22);
x_24 = lean_mk_string_unchecked(" in ", 4, 4);
x_25 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter), 6, 1);
lean_closure_set(x_25, 0, x_24);
x_26 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_26, 0, x_25);
lean_closure_set(x_26, 1, x_6);
x_27 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_27, 0, x_23);
lean_closure_set(x_27, 1, x_26);
x_28 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_28, 0, x_21);
lean_closure_set(x_28, 1, x_27);
x_29 = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(x_29, 0, x_11);
lean_closure_set(x_29, 1, x_15);
lean_closure_set(x_29, 2, x_28);
x_30 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_14, x_29, x_1, x_2, x_3, x_4, x_5);
return x_30;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doForDecl_formatter__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_formatterAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("doForDecl", 9, 9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("formatter", 9, 9);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doForDecl_formatter), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doFor_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("Parser", 6, 6);
x_8 = lean_mk_string_unchecked("Term", 4, 4);
x_9 = lean_mk_string_unchecked("doFor", 5, 5);
lean_inc(x_9);
x_10 = l_Lean_Name_mkStr4(x_6, x_7, x_8, x_9);
x_11 = lean_box(1);
x_12 = lean_box(0);
lean_inc(x_10);
x_13 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(x_13, 0, x_9);
lean_closure_set(x_13, 1, x_10);
lean_closure_set(x_13, 2, x_11);
lean_closure_set(x_13, 3, x_12);
x_14 = lean_unsigned_to_nat(1024u);
x_15 = lean_mk_string_unchecked("for ", 4, 4);
x_16 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter), 6, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doForDecl_formatter), 5, 0);
x_18 = lean_mk_string_unchecked(", ", 2, 2);
lean_inc(x_18);
x_19 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter), 6, 1);
lean_closure_set(x_19, 0, x_18);
x_20 = lean_alloc_closure((void*)(l_Lean_Parser_sepBy1_formatter___boxed), 9, 4);
lean_closure_set(x_20, 0, x_17);
lean_closure_set(x_20, 1, x_18);
lean_closure_set(x_20, 2, x_19);
lean_closure_set(x_20, 3, x_12);
x_21 = lean_mk_string_unchecked("do ", 3, 3);
x_22 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter), 6, 1);
lean_closure_set(x_22, 0, x_21);
x_23 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doSeq_formatter), 5, 0);
x_24 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_24, 0, x_22);
lean_closure_set(x_24, 1, x_23);
x_25 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_25, 0, x_20);
lean_closure_set(x_25, 1, x_24);
x_26 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_26, 0, x_16);
lean_closure_set(x_26, 1, x_25);
x_27 = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(x_27, 0, x_10);
lean_closure_set(x_27, 1, x_14);
lean_closure_set(x_27, 2, x_26);
x_28 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_13, x_27, x_1, x_2, x_3, x_4, x_5);
return x_28;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doFor_formatter__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_formatterAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("doFor", 5, 5);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("formatter", 9, 9);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doFor_formatter), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doForDecl_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("Parser", 6, 6);
x_8 = lean_mk_string_unchecked("Term", 4, 4);
x_9 = lean_mk_string_unchecked("doForDecl", 9, 9);
lean_inc(x_9);
x_10 = l_Lean_Name_mkStr4(x_6, x_7, x_8, x_9);
x_11 = lean_box(1);
x_12 = lean_box(0);
lean_inc(x_10);
x_13 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(x_13, 0, x_9);
lean_closure_set(x_13, 1, x_10);
lean_closure_set(x_13, 2, x_11);
lean_closure_set(x_13, 3, x_12);
x_14 = lean_unsigned_to_nat(1024u);
x_15 = lean_alloc_closure((void*)(l_Lean_Parser_Term_ident_parenthesizer), 5, 0);
x_16 = lean_mk_string_unchecked(" : ", 3, 3);
x_17 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___boxed), 6, 1);
lean_closure_set(x_17, 0, x_16);
x_18 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doIdDecl_parenthesizer___lam__1), 7, 2);
lean_closure_set(x_18, 0, x_15);
lean_closure_set(x_18, 1, x_17);
x_19 = lean_alloc_closure((void*)(l_Lean_Parser_optional_parenthesizer), 6, 1);
lean_closure_set(x_19, 0, x_18);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_alloc_closure((void*)(l_Lean_Parser_termParser_parenthesizer), 6, 1);
lean_closure_set(x_21, 0, x_20);
x_22 = lean_mk_string_unchecked(" in ", 4, 4);
x_23 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___boxed), 6, 1);
lean_closure_set(x_23, 0, x_22);
x_24 = lean_mk_string_unchecked("do", 2, 2);
lean_inc(x_21);
x_25 = lean_alloc_closure((void*)(l_Lean_Parser_withForbidden_parenthesizer___boxed), 7, 2);
lean_closure_set(x_25, 0, x_24);
lean_closure_set(x_25, 1, x_21);
x_26 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_26, 0, x_23);
lean_closure_set(x_26, 1, x_25);
x_27 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_27, 0, x_21);
lean_closure_set(x_27, 1, x_26);
x_28 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_28, 0, x_19);
lean_closure_set(x_28, 1, x_27);
x_29 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer), 8, 3);
lean_closure_set(x_29, 0, x_10);
lean_closure_set(x_29, 1, x_14);
lean_closure_set(x_29, 2, x_28);
x_30 = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(x_13, x_29, x_1, x_2, x_3, x_4, x_5);
return x_30;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doForDecl_parenthesizer__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("doForDecl", 9, 9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("parenthesizer", 13, 13);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doForDecl_parenthesizer), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doFor_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("Parser", 6, 6);
x_8 = lean_mk_string_unchecked("Term", 4, 4);
x_9 = lean_mk_string_unchecked("doFor", 5, 5);
lean_inc(x_9);
x_10 = l_Lean_Name_mkStr4(x_6, x_7, x_8, x_9);
x_11 = lean_box(1);
x_12 = lean_box(0);
lean_inc(x_10);
x_13 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(x_13, 0, x_9);
lean_closure_set(x_13, 1, x_10);
lean_closure_set(x_13, 2, x_11);
lean_closure_set(x_13, 3, x_12);
x_14 = lean_unsigned_to_nat(1024u);
x_15 = lean_mk_string_unchecked("for ", 4, 4);
x_16 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___boxed), 6, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doForDecl_parenthesizer), 5, 0);
x_18 = lean_mk_string_unchecked(", ", 2, 2);
lean_inc(x_18);
x_19 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___boxed), 6, 1);
lean_closure_set(x_19, 0, x_18);
x_20 = lean_alloc_closure((void*)(l_Lean_Parser_sepBy1_parenthesizer___boxed), 9, 4);
lean_closure_set(x_20, 0, x_17);
lean_closure_set(x_20, 1, x_18);
lean_closure_set(x_20, 2, x_19);
lean_closure_set(x_20, 3, x_12);
x_21 = lean_mk_string_unchecked("do ", 3, 3);
x_22 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___boxed), 6, 1);
lean_closure_set(x_22, 0, x_21);
x_23 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doSeq_parenthesizer), 5, 0);
x_24 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_24, 0, x_22);
lean_closure_set(x_24, 1, x_23);
x_25 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_25, 0, x_20);
lean_closure_set(x_25, 1, x_24);
x_26 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_26, 0, x_16);
lean_closure_set(x_26, 1, x_25);
x_27 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer), 8, 3);
lean_closure_set(x_27, 0, x_10);
lean_closure_set(x_27, 1, x_14);
lean_closure_set(x_27, 2, x_26);
x_28 = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(x_13, x_27, x_1, x_2, x_3, x_4, x_5);
return x_28;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doFor_parenthesizer__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("doFor", 5, 5);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("parenthesizer", 13, 13);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doFor_parenthesizer), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
static lean_object* _init_l_Lean_Parser_Term_doMatchAlts() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Term_doSeq;
x_2 = l_Lean_Parser_Term_matchAlts(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Term_doMatch() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Term", 4, 4);
x_4 = lean_mk_string_unchecked("doMatch", 7, 7);
lean_inc(x_4);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_box(1);
x_7 = lean_box(0);
x_8 = lean_unbox(x_6);
x_9 = lean_unbox(x_7);
lean_inc(x_5);
x_10 = l_Lean_Parser_mkAntiquot(x_4, x_5, x_8, x_9);
lean_dec(x_4);
x_11 = lean_unsigned_to_nat(1022u);
x_12 = lean_mk_string_unchecked("match ", 6, 6);
x_13 = l_Lean_Parser_symbol(x_12);
lean_dec(x_12);
x_14 = l_Lean_Parser_Term_generalizingParam;
x_15 = l_Lean_Parser_optional(x_14);
x_16 = l_Lean_Parser_Term_motive;
x_17 = l_Lean_Parser_optional(x_16);
x_18 = l_Lean_Parser_Term_matchDiscr;
x_19 = lean_mk_string_unchecked(", ", 2, 2);
x_20 = l_Lean_Parser_symbol(x_19);
x_21 = lean_unbox(x_7);
x_22 = l_Lean_Parser_sepBy1(x_18, x_19, x_20, x_21);
lean_dec(x_19);
x_23 = lean_mk_string_unchecked(" with", 5, 5);
x_24 = l_Lean_Parser_symbol(x_23);
lean_dec(x_23);
x_25 = l_Lean_Parser_Term_doMatchAlts;
x_26 = l_Lean_Parser_andthen(x_24, x_25);
x_27 = l_Lean_Parser_andthen(x_22, x_26);
x_28 = l_Lean_Parser_andthen(x_17, x_27);
x_29 = l_Lean_Parser_andthen(x_15, x_28);
x_30 = l_Lean_Parser_andthen(x_13, x_29);
lean_inc(x_5);
x_31 = l_Lean_Parser_leadingNode(x_5, x_11, x_30);
x_32 = l_Lean_Parser_withAntiquot(x_10, x_31);
x_33 = l_Lean_Parser_withCache(x_5, x_32);
return x_33;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doMatch__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = lean_mk_string_unchecked("doElem", 6, 6);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Term", 4, 4);
x_7 = lean_mk_string_unchecked("doMatch", 7, 7);
x_8 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_7);
x_9 = l_Lean_Parser_Term_doMatch;
x_10 = lean_unsigned_to_nat(1000u);
x_11 = l_Lean_Parser_addBuiltinLeadingParser(x_3, x_8, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doMatch_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Term", 4, 4);
x_5 = lean_mk_string_unchecked("doMatch", 7, 7);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(157u);
x_8 = lean_unsigned_to_nat(25u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(159u);
x_11 = lean_unsigned_to_nat(50u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_11);
x_14 = lean_unsigned_to_nat(29u);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_unsigned_to_nat(36u);
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
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doMatchAlts_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doSeq_formatter), 5, 0);
x_7 = lean_alloc_closure((void*)(l_Lean_Parser_Term_matchAlts_formatter), 6, 1);
lean_closure_set(x_7, 0, x_6);
x_8 = l_Lean_ppDedent_formatter(x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doMatch_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("Parser", 6, 6);
x_8 = lean_mk_string_unchecked("Term", 4, 4);
x_9 = lean_mk_string_unchecked("doMatch", 7, 7);
lean_inc(x_9);
x_10 = l_Lean_Name_mkStr4(x_6, x_7, x_8, x_9);
x_11 = lean_box(1);
x_12 = lean_box(0);
lean_inc(x_10);
x_13 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(x_13, 0, x_9);
lean_closure_set(x_13, 1, x_10);
lean_closure_set(x_13, 2, x_11);
lean_closure_set(x_13, 3, x_12);
x_14 = lean_unsigned_to_nat(1022u);
x_15 = lean_mk_string_unchecked("match ", 6, 6);
x_16 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter), 6, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = lean_alloc_closure((void*)(l_Lean_Parser_Term_generalizingParam_formatter), 5, 0);
x_18 = lean_alloc_closure((void*)(l_Lean_Parser_optional_formatter), 6, 1);
lean_closure_set(x_18, 0, x_17);
x_19 = lean_alloc_closure((void*)(l_Lean_Parser_Term_motive_formatter), 5, 0);
x_20 = lean_alloc_closure((void*)(l_Lean_Parser_optional_formatter), 6, 1);
lean_closure_set(x_20, 0, x_19);
x_21 = lean_alloc_closure((void*)(l_Lean_Parser_Term_matchDiscr_formatter), 5, 0);
x_22 = lean_mk_string_unchecked(", ", 2, 2);
lean_inc(x_22);
x_23 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter), 6, 1);
lean_closure_set(x_23, 0, x_22);
x_24 = lean_alloc_closure((void*)(l_Lean_Parser_sepBy1_formatter___boxed), 9, 4);
lean_closure_set(x_24, 0, x_21);
lean_closure_set(x_24, 1, x_22);
lean_closure_set(x_24, 2, x_23);
lean_closure_set(x_24, 3, x_12);
x_25 = lean_mk_string_unchecked(" with", 5, 5);
x_26 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter), 6, 1);
lean_closure_set(x_26, 0, x_25);
x_27 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doMatchAlts_formatter), 5, 0);
x_28 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_28, 0, x_26);
lean_closure_set(x_28, 1, x_27);
x_29 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_29, 0, x_24);
lean_closure_set(x_29, 1, x_28);
x_30 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_30, 0, x_20);
lean_closure_set(x_30, 1, x_29);
x_31 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_31, 0, x_18);
lean_closure_set(x_31, 1, x_30);
x_32 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_32, 0, x_16);
lean_closure_set(x_32, 1, x_31);
x_33 = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(x_33, 0, x_10);
lean_closure_set(x_33, 1, x_14);
lean_closure_set(x_33, 2, x_32);
x_34 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_13, x_33, x_1, x_2, x_3, x_4, x_5);
return x_34;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doMatch_formatter__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_formatterAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("doMatch", 7, 7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("formatter", 9, 9);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doMatch_formatter), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doMatchAlts_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doSeq_parenthesizer), 5, 0);
x_7 = l_Lean_Parser_Term_matchAlts_parenthesizer(x_6, x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doMatch_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("Parser", 6, 6);
x_8 = lean_mk_string_unchecked("Term", 4, 4);
x_9 = lean_mk_string_unchecked("doMatch", 7, 7);
lean_inc(x_9);
x_10 = l_Lean_Name_mkStr4(x_6, x_7, x_8, x_9);
x_11 = lean_box(1);
x_12 = lean_box(0);
lean_inc(x_10);
x_13 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(x_13, 0, x_9);
lean_closure_set(x_13, 1, x_10);
lean_closure_set(x_13, 2, x_11);
lean_closure_set(x_13, 3, x_12);
x_14 = lean_unsigned_to_nat(1022u);
x_15 = lean_mk_string_unchecked("match ", 6, 6);
x_16 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___boxed), 6, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = lean_alloc_closure((void*)(l_Lean_Parser_Term_generalizingParam_parenthesizer), 5, 0);
x_18 = lean_alloc_closure((void*)(l_Lean_Parser_optional_parenthesizer), 6, 1);
lean_closure_set(x_18, 0, x_17);
x_19 = lean_alloc_closure((void*)(l_Lean_Parser_Term_motive_parenthesizer), 5, 0);
x_20 = lean_alloc_closure((void*)(l_Lean_Parser_optional_parenthesizer), 6, 1);
lean_closure_set(x_20, 0, x_19);
x_21 = lean_alloc_closure((void*)(l_Lean_Parser_Term_matchDiscr_parenthesizer), 5, 0);
x_22 = lean_mk_string_unchecked(", ", 2, 2);
lean_inc(x_22);
x_23 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___boxed), 6, 1);
lean_closure_set(x_23, 0, x_22);
x_24 = lean_alloc_closure((void*)(l_Lean_Parser_sepBy1_parenthesizer___boxed), 9, 4);
lean_closure_set(x_24, 0, x_21);
lean_closure_set(x_24, 1, x_22);
lean_closure_set(x_24, 2, x_23);
lean_closure_set(x_24, 3, x_12);
x_25 = lean_mk_string_unchecked(" with", 5, 5);
x_26 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___boxed), 6, 1);
lean_closure_set(x_26, 0, x_25);
x_27 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doMatchAlts_parenthesizer), 5, 0);
x_28 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_28, 0, x_26);
lean_closure_set(x_28, 1, x_27);
x_29 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_29, 0, x_24);
lean_closure_set(x_29, 1, x_28);
x_30 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_30, 0, x_20);
lean_closure_set(x_30, 1, x_29);
x_31 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_31, 0, x_18);
lean_closure_set(x_31, 1, x_30);
x_32 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_32, 0, x_16);
lean_closure_set(x_32, 1, x_31);
x_33 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer), 8, 3);
lean_closure_set(x_33, 0, x_10);
lean_closure_set(x_33, 1, x_14);
lean_closure_set(x_33, 2, x_32);
x_34 = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(x_13, x_33, x_1, x_2, x_3, x_4, x_5);
return x_34;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doMatch_parenthesizer__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("doMatch", 7, 7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("parenthesizer", 13, 13);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doMatch_parenthesizer), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
static lean_object* _init_l_Lean_Parser_Term_doMatchExprAlts() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Term_doSeq;
x_2 = l_Lean_Parser_Term_matchExprAlts(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Term_optMetaFalse() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_1 = lean_mk_string_unchecked("(", 1, 1);
x_2 = l_Lean_Parser_symbol(x_1);
lean_dec(x_1);
x_3 = lean_mk_string_unchecked("meta", 4, 4);
x_4 = lean_box(0);
x_5 = lean_unbox(x_4);
x_6 = l_Lean_Parser_nonReservedSymbol(x_3, x_5);
lean_dec(x_3);
x_7 = lean_mk_string_unchecked(" := ", 4, 4);
x_8 = l_Lean_Parser_symbol(x_7);
lean_dec(x_7);
x_9 = lean_mk_string_unchecked("false", 5, 5);
x_10 = lean_unbox(x_4);
x_11 = l_Lean_Parser_nonReservedSymbol(x_9, x_10);
lean_dec(x_9);
x_12 = lean_mk_string_unchecked(") ", 2, 2);
x_13 = l_Lean_Parser_symbol(x_12);
lean_dec(x_12);
x_14 = l_Lean_Parser_andthen(x_11, x_13);
x_15 = l_Lean_Parser_andthen(x_8, x_14);
x_16 = l_Lean_Parser_andthen(x_6, x_15);
x_17 = l_Lean_Parser_andthen(x_2, x_16);
x_18 = l_Lean_Parser_atomic(x_17);
x_19 = l_Lean_Parser_optional(x_18);
return x_19;
}
}
static lean_object* _init_l_Lean_Parser_Term_doMatchExpr() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Term", 4, 4);
x_4 = lean_mk_string_unchecked("doMatchExpr", 11, 11);
lean_inc(x_4);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_box(1);
x_7 = lean_box(0);
x_8 = lean_unbox(x_6);
x_9 = lean_unbox(x_7);
lean_inc(x_5);
x_10 = l_Lean_Parser_mkAntiquot(x_4, x_5, x_8, x_9);
lean_dec(x_4);
x_11 = lean_unsigned_to_nat(1022u);
x_12 = lean_mk_string_unchecked("match_expr ", 11, 11);
x_13 = l_Lean_Parser_symbol(x_12);
lean_dec(x_12);
x_14 = l_Lean_Parser_Term_optMetaFalse;
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Lean_Parser_termParser(x_15);
x_17 = lean_mk_string_unchecked(" with", 5, 5);
x_18 = l_Lean_Parser_symbol(x_17);
lean_dec(x_17);
x_19 = l_Lean_Parser_Term_doMatchExprAlts;
x_20 = l_Lean_Parser_andthen(x_18, x_19);
x_21 = l_Lean_Parser_andthen(x_16, x_20);
x_22 = l_Lean_Parser_andthen(x_14, x_21);
x_23 = l_Lean_Parser_andthen(x_13, x_22);
lean_inc(x_5);
x_24 = l_Lean_Parser_leadingNode(x_5, x_11, x_23);
x_25 = l_Lean_Parser_withAntiquot(x_10, x_24);
x_26 = l_Lean_Parser_withCache(x_5, x_25);
return x_26;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doMatchExpr__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = lean_mk_string_unchecked("doElem", 6, 6);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Term", 4, 4);
x_7 = lean_mk_string_unchecked("doMatchExpr", 11, 11);
x_8 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_7);
x_9 = l_Lean_Parser_Term_doMatchExpr;
x_10 = lean_unsigned_to_nat(1000u);
x_11 = l_Lean_Parser_addBuiltinLeadingParser(x_3, x_8, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doMatchExpr_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Term", 4, 4);
x_5 = lean_mk_string_unchecked("doMatchExpr", 11, 11);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(164u);
x_8 = lean_unsigned_to_nat(25u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(165u);
x_11 = lean_unsigned_to_nat(75u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_11);
x_14 = lean_unsigned_to_nat(29u);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_unsigned_to_nat(40u);
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
LEAN_EXPORT lean_object* l_Lean_Parser_Term_optMetaFalse_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_6 = lean_mk_string_unchecked("(", 1, 1);
x_7 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter), 6, 1);
lean_closure_set(x_7, 0, x_6);
x_8 = lean_mk_string_unchecked("meta", 4, 4);
x_9 = lean_box(0);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_nonReservedSymbol_formatter___boxed), 7, 2);
lean_closure_set(x_10, 0, x_8);
lean_closure_set(x_10, 1, x_9);
x_11 = lean_mk_string_unchecked(" := ", 4, 4);
x_12 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter), 6, 1);
lean_closure_set(x_12, 0, x_11);
x_13 = lean_mk_string_unchecked("false", 5, 5);
x_14 = lean_alloc_closure((void*)(l_Lean_Parser_nonReservedSymbol_formatter___boxed), 7, 2);
lean_closure_set(x_14, 0, x_13);
lean_closure_set(x_14, 1, x_9);
x_15 = lean_mk_string_unchecked(") ", 2, 2);
x_16 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter), 6, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_17, 0, x_14);
lean_closure_set(x_17, 1, x_16);
x_18 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_18, 0, x_12);
lean_closure_set(x_18, 1, x_17);
x_19 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_19, 0, x_10);
lean_closure_set(x_19, 1, x_18);
x_20 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_20, 0, x_7);
lean_closure_set(x_20, 1, x_19);
x_21 = lean_alloc_closure((void*)(l_Lean_Parser_atomic_formatter), 6, 1);
lean_closure_set(x_21, 0, x_20);
x_22 = l_Lean_Parser_optional_formatter(x_21, x_1, x_2, x_3, x_4, x_5);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doMatchExprAlts_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doSeq_formatter), 5, 0);
x_7 = lean_alloc_closure((void*)(l_Lean_Parser_Term_matchExprAlts_formatter), 6, 1);
lean_closure_set(x_7, 0, x_6);
x_8 = l_Lean_ppDedent_formatter(x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doMatchExpr_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("Parser", 6, 6);
x_8 = lean_mk_string_unchecked("Term", 4, 4);
x_9 = lean_mk_string_unchecked("doMatchExpr", 11, 11);
lean_inc(x_9);
x_10 = l_Lean_Name_mkStr4(x_6, x_7, x_8, x_9);
x_11 = lean_box(1);
x_12 = lean_box(0);
lean_inc(x_10);
x_13 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(x_13, 0, x_9);
lean_closure_set(x_13, 1, x_10);
lean_closure_set(x_13, 2, x_11);
lean_closure_set(x_13, 3, x_12);
x_14 = lean_unsigned_to_nat(1022u);
x_15 = lean_mk_string_unchecked("match_expr ", 11, 11);
x_16 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter), 6, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = lean_alloc_closure((void*)(l_Lean_Parser_Term_optMetaFalse_formatter), 5, 0);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_alloc_closure((void*)(l_Lean_Parser_termParser_formatter___boxed), 6, 1);
lean_closure_set(x_19, 0, x_18);
x_20 = lean_mk_string_unchecked(" with", 5, 5);
x_21 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter), 6, 1);
lean_closure_set(x_21, 0, x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doMatchExprAlts_formatter), 5, 0);
x_23 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_23, 0, x_21);
lean_closure_set(x_23, 1, x_22);
x_24 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_24, 0, x_19);
lean_closure_set(x_24, 1, x_23);
x_25 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_25, 0, x_17);
lean_closure_set(x_25, 1, x_24);
x_26 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_26, 0, x_16);
lean_closure_set(x_26, 1, x_25);
x_27 = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(x_27, 0, x_10);
lean_closure_set(x_27, 1, x_14);
lean_closure_set(x_27, 2, x_26);
x_28 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_13, x_27, x_1, x_2, x_3, x_4, x_5);
return x_28;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doMatchExpr_formatter__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_formatterAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("doMatchExpr", 11, 11);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("formatter", 9, 9);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doMatchExpr_formatter), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_optMetaFalse_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_6 = lean_mk_string_unchecked("(", 1, 1);
x_7 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___boxed), 6, 1);
lean_closure_set(x_7, 0, x_6);
x_8 = lean_mk_string_unchecked("meta", 4, 4);
x_9 = lean_box(0);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_nonReservedSymbol_parenthesizer___boxed), 7, 2);
lean_closure_set(x_10, 0, x_8);
lean_closure_set(x_10, 1, x_9);
x_11 = lean_mk_string_unchecked(" := ", 4, 4);
x_12 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___boxed), 6, 1);
lean_closure_set(x_12, 0, x_11);
x_13 = lean_mk_string_unchecked("false", 5, 5);
x_14 = lean_alloc_closure((void*)(l_Lean_Parser_nonReservedSymbol_parenthesizer___boxed), 7, 2);
lean_closure_set(x_14, 0, x_13);
lean_closure_set(x_14, 1, x_9);
x_15 = lean_mk_string_unchecked(") ", 2, 2);
x_16 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___boxed), 6, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_17, 0, x_14);
lean_closure_set(x_17, 1, x_16);
x_18 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_18, 0, x_12);
lean_closure_set(x_18, 1, x_17);
x_19 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_19, 0, x_10);
lean_closure_set(x_19, 1, x_18);
x_20 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doIdDecl_parenthesizer___lam__1), 7, 2);
lean_closure_set(x_20, 0, x_7);
lean_closure_set(x_20, 1, x_19);
x_21 = l_Lean_Parser_optional_parenthesizer(x_20, x_1, x_2, x_3, x_4, x_5);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doMatchExprAlts_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doSeq_parenthesizer), 5, 0);
x_7 = l_Lean_Parser_Term_matchExprAlts_parenthesizer(x_6, x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doMatchExpr_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("Parser", 6, 6);
x_8 = lean_mk_string_unchecked("Term", 4, 4);
x_9 = lean_mk_string_unchecked("doMatchExpr", 11, 11);
lean_inc(x_9);
x_10 = l_Lean_Name_mkStr4(x_6, x_7, x_8, x_9);
x_11 = lean_box(1);
x_12 = lean_box(0);
lean_inc(x_10);
x_13 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(x_13, 0, x_9);
lean_closure_set(x_13, 1, x_10);
lean_closure_set(x_13, 2, x_11);
lean_closure_set(x_13, 3, x_12);
x_14 = lean_unsigned_to_nat(1022u);
x_15 = lean_mk_string_unchecked("match_expr ", 11, 11);
x_16 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___boxed), 6, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = lean_alloc_closure((void*)(l_Lean_Parser_Term_optMetaFalse_parenthesizer), 5, 0);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_alloc_closure((void*)(l_Lean_Parser_termParser_parenthesizer), 6, 1);
lean_closure_set(x_19, 0, x_18);
x_20 = lean_mk_string_unchecked(" with", 5, 5);
x_21 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___boxed), 6, 1);
lean_closure_set(x_21, 0, x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doMatchExprAlts_parenthesizer), 5, 0);
x_23 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_23, 0, x_21);
lean_closure_set(x_23, 1, x_22);
x_24 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_24, 0, x_19);
lean_closure_set(x_24, 1, x_23);
x_25 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_25, 0, x_17);
lean_closure_set(x_25, 1, x_24);
x_26 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_26, 0, x_16);
lean_closure_set(x_26, 1, x_25);
x_27 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer), 8, 3);
lean_closure_set(x_27, 0, x_10);
lean_closure_set(x_27, 1, x_14);
lean_closure_set(x_27, 2, x_26);
x_28 = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(x_13, x_27, x_1, x_2, x_3, x_4, x_5);
return x_28;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doMatchExpr_parenthesizer__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("doMatchExpr", 11, 11);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("parenthesizer", 13, 13);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doMatchExpr_parenthesizer), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
static lean_object* _init_l_Lean_Parser_Term_doCatch() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Term", 4, 4);
x_4 = lean_mk_string_unchecked("doCatch", 7, 7);
lean_inc(x_4);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_box(1);
x_7 = lean_box(0);
x_8 = lean_unbox(x_6);
x_9 = lean_unbox(x_7);
lean_inc(x_5);
x_10 = l_Lean_Parser_mkAntiquot(x_4, x_5, x_8, x_9);
lean_dec(x_4);
x_11 = lean_unsigned_to_nat(1024u);
x_12 = l_Lean_Parser_skip;
x_13 = lean_mk_string_unchecked("catch ", 6, 6);
x_14 = l_Lean_Parser_symbol(x_13);
lean_dec(x_13);
x_15 = l_Lean_Parser_Term_binderIdent;
x_16 = l_Lean_Parser_andthen(x_14, x_15);
x_17 = l_Lean_Parser_atomic(x_16);
x_18 = lean_mk_string_unchecked(" : ", 3, 3);
x_19 = l_Lean_Parser_symbol(x_18);
lean_dec(x_18);
x_20 = lean_unsigned_to_nat(0u);
x_21 = l_Lean_Parser_termParser(x_20);
x_22 = l_Lean_Parser_andthen(x_19, x_21);
x_23 = l_Lean_Parser_optional(x_22);
x_24 = l_Lean_Parser_darrow;
x_25 = l_Lean_Parser_Term_doSeq;
x_26 = l_Lean_Parser_andthen(x_24, x_25);
x_27 = l_Lean_Parser_andthen(x_23, x_26);
x_28 = l_Lean_Parser_andthen(x_17, x_27);
x_29 = l_Lean_Parser_andthen(x_12, x_28);
lean_inc(x_5);
x_30 = l_Lean_Parser_leadingNode(x_5, x_11, x_29);
x_31 = l_Lean_Parser_withAntiquot(x_10, x_30);
x_32 = l_Lean_Parser_withCache(x_5, x_31);
return x_32;
}
}
static lean_object* _init_l_Lean_Parser_Term_doCatchMatch() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Term", 4, 4);
x_4 = lean_mk_string_unchecked("doCatchMatch", 12, 12);
lean_inc(x_4);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_box(1);
x_7 = lean_box(0);
x_8 = lean_unbox(x_6);
x_9 = lean_unbox(x_7);
lean_inc(x_5);
x_10 = l_Lean_Parser_mkAntiquot(x_4, x_5, x_8, x_9);
lean_dec(x_4);
x_11 = lean_unsigned_to_nat(1024u);
x_12 = l_Lean_Parser_skip;
x_13 = lean_mk_string_unchecked("catch ", 6, 6);
x_14 = l_Lean_Parser_symbol(x_13);
lean_dec(x_13);
x_15 = l_Lean_Parser_Term_doMatchAlts;
x_16 = l_Lean_Parser_andthen(x_14, x_15);
x_17 = l_Lean_Parser_andthen(x_12, x_16);
lean_inc(x_5);
x_18 = l_Lean_Parser_leadingNode(x_5, x_11, x_17);
x_19 = l_Lean_Parser_withAntiquot(x_10, x_18);
x_20 = l_Lean_Parser_withCache(x_5, x_19);
return x_20;
}
}
static lean_object* _init_l_Lean_Parser_Term_doFinally() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Term", 4, 4);
x_4 = lean_mk_string_unchecked("doFinally", 9, 9);
lean_inc(x_4);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_box(1);
x_7 = lean_box(0);
x_8 = lean_unbox(x_6);
x_9 = lean_unbox(x_7);
lean_inc(x_5);
x_10 = l_Lean_Parser_mkAntiquot(x_4, x_5, x_8, x_9);
lean_dec(x_4);
x_11 = lean_unsigned_to_nat(1024u);
x_12 = l_Lean_Parser_skip;
x_13 = lean_mk_string_unchecked("finally ", 8, 8);
x_14 = l_Lean_Parser_symbol(x_13);
lean_dec(x_13);
x_15 = l_Lean_Parser_Term_doSeq;
x_16 = l_Lean_Parser_andthen(x_14, x_15);
x_17 = l_Lean_Parser_andthen(x_12, x_16);
lean_inc(x_5);
x_18 = l_Lean_Parser_leadingNode(x_5, x_11, x_17);
x_19 = l_Lean_Parser_withAntiquot(x_10, x_18);
x_20 = l_Lean_Parser_withCache(x_5, x_19);
return x_20;
}
}
static lean_object* _init_l_Lean_Parser_Term_doTry() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Term", 4, 4);
x_4 = lean_mk_string_unchecked("doTry", 5, 5);
lean_inc(x_4);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_box(1);
x_7 = lean_box(0);
x_8 = lean_unbox(x_6);
x_9 = lean_unbox(x_7);
lean_inc(x_5);
x_10 = l_Lean_Parser_mkAntiquot(x_4, x_5, x_8, x_9);
lean_dec(x_4);
x_11 = lean_unsigned_to_nat(1024u);
x_12 = lean_mk_string_unchecked("try ", 4, 4);
x_13 = l_Lean_Parser_symbol(x_12);
lean_dec(x_12);
x_14 = l_Lean_Parser_Term_doSeq;
x_15 = l_Lean_Parser_Term_doCatch;
x_16 = l_Lean_Parser_Term_doCatchMatch;
x_17 = l_Lean_Parser_orelse(x_15, x_16);
x_18 = l_Lean_Parser_many(x_17);
x_19 = l_Lean_Parser_Term_doFinally;
x_20 = l_Lean_Parser_optional(x_19);
x_21 = l_Lean_Parser_andthen(x_18, x_20);
x_22 = l_Lean_Parser_andthen(x_14, x_21);
x_23 = l_Lean_Parser_andthen(x_13, x_22);
lean_inc(x_5);
x_24 = l_Lean_Parser_leadingNode(x_5, x_11, x_23);
x_25 = l_Lean_Parser_withAntiquot(x_10, x_24);
x_26 = l_Lean_Parser_withCache(x_5, x_25);
return x_26;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doTry__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = lean_mk_string_unchecked("doElem", 6, 6);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Term", 4, 4);
x_7 = lean_mk_string_unchecked("doTry", 5, 5);
x_8 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_7);
x_9 = l_Lean_Parser_Term_doTry;
x_10 = lean_unsigned_to_nat(1000u);
x_11 = l_Lean_Parser_addBuiltinLeadingParser(x_3, x_8, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doTry_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Term", 4, 4);
x_5 = lean_mk_string_unchecked("doTry", 5, 5);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(173u);
x_8 = lean_unsigned_to_nat(25u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(174u);
x_11 = lean_unsigned_to_nat(74u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_11);
x_14 = lean_unsigned_to_nat(29u);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_unsigned_to_nat(34u);
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
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doCatch_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("Parser", 6, 6);
x_8 = lean_mk_string_unchecked("Term", 4, 4);
x_9 = lean_mk_string_unchecked("doCatch", 7, 7);
lean_inc(x_9);
x_10 = l_Lean_Name_mkStr4(x_6, x_7, x_8, x_9);
x_11 = lean_box(1);
x_12 = lean_box(0);
lean_inc(x_10);
x_13 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(x_13, 0, x_9);
lean_closure_set(x_13, 1, x_10);
lean_closure_set(x_13, 2, x_11);
lean_closure_set(x_13, 3, x_12);
x_14 = lean_unsigned_to_nat(1024u);
x_15 = lean_alloc_closure((void*)(l_Lean_ppLine_formatter___boxed), 5, 0);
x_16 = lean_alloc_closure((void*)(l_Lean_ppDedent_formatter), 6, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = lean_mk_string_unchecked("catch ", 6, 6);
x_18 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter), 6, 1);
lean_closure_set(x_18, 0, x_17);
x_19 = lean_alloc_closure((void*)(l_Lean_Parser_Term_binderIdent_formatter), 5, 0);
x_20 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_20, 0, x_18);
lean_closure_set(x_20, 1, x_19);
x_21 = lean_alloc_closure((void*)(l_Lean_Parser_atomic_formatter), 6, 1);
lean_closure_set(x_21, 0, x_20);
x_22 = lean_mk_string_unchecked(" : ", 3, 3);
x_23 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter), 6, 1);
lean_closure_set(x_23, 0, x_22);
x_24 = lean_unsigned_to_nat(0u);
x_25 = lean_alloc_closure((void*)(l_Lean_Parser_termParser_formatter___boxed), 6, 1);
lean_closure_set(x_25, 0, x_24);
x_26 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_26, 0, x_23);
lean_closure_set(x_26, 1, x_25);
x_27 = lean_alloc_closure((void*)(l_Lean_Parser_optional_formatter), 6, 1);
lean_closure_set(x_27, 0, x_26);
x_28 = lean_alloc_closure((void*)(l_Lean_Parser_darrow_formatter), 5, 0);
x_29 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doSeq_formatter), 5, 0);
x_30 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_30, 0, x_28);
lean_closure_set(x_30, 1, x_29);
x_31 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_31, 0, x_27);
lean_closure_set(x_31, 1, x_30);
x_32 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_32, 0, x_21);
lean_closure_set(x_32, 1, x_31);
x_33 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_33, 0, x_16);
lean_closure_set(x_33, 1, x_32);
x_34 = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(x_34, 0, x_10);
lean_closure_set(x_34, 1, x_14);
lean_closure_set(x_34, 2, x_33);
x_35 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_13, x_34, x_1, x_2, x_3, x_4, x_5);
return x_35;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doCatch_formatter__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_formatterAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("doCatch", 7, 7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("formatter", 9, 9);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doCatch_formatter), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doCatchMatch_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("Parser", 6, 6);
x_8 = lean_mk_string_unchecked("Term", 4, 4);
x_9 = lean_mk_string_unchecked("doCatchMatch", 12, 12);
lean_inc(x_9);
x_10 = l_Lean_Name_mkStr4(x_6, x_7, x_8, x_9);
x_11 = lean_box(1);
x_12 = lean_box(0);
lean_inc(x_10);
x_13 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(x_13, 0, x_9);
lean_closure_set(x_13, 1, x_10);
lean_closure_set(x_13, 2, x_11);
lean_closure_set(x_13, 3, x_12);
x_14 = lean_unsigned_to_nat(1024u);
x_15 = lean_alloc_closure((void*)(l_Lean_ppLine_formatter___boxed), 5, 0);
x_16 = lean_alloc_closure((void*)(l_Lean_ppDedent_formatter), 6, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = lean_mk_string_unchecked("catch ", 6, 6);
x_18 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter), 6, 1);
lean_closure_set(x_18, 0, x_17);
x_19 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doMatchAlts_formatter), 5, 0);
x_20 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_20, 0, x_18);
lean_closure_set(x_20, 1, x_19);
x_21 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_21, 0, x_16);
lean_closure_set(x_21, 1, x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(x_22, 0, x_10);
lean_closure_set(x_22, 1, x_14);
lean_closure_set(x_22, 2, x_21);
x_23 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_13, x_22, x_1, x_2, x_3, x_4, x_5);
return x_23;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doCatchMatch_formatter__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_formatterAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("doCatchMatch", 12, 12);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("formatter", 9, 9);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doCatchMatch_formatter), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doFinally_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("Parser", 6, 6);
x_8 = lean_mk_string_unchecked("Term", 4, 4);
x_9 = lean_mk_string_unchecked("doFinally", 9, 9);
lean_inc(x_9);
x_10 = l_Lean_Name_mkStr4(x_6, x_7, x_8, x_9);
x_11 = lean_box(1);
x_12 = lean_box(0);
lean_inc(x_10);
x_13 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(x_13, 0, x_9);
lean_closure_set(x_13, 1, x_10);
lean_closure_set(x_13, 2, x_11);
lean_closure_set(x_13, 3, x_12);
x_14 = lean_unsigned_to_nat(1024u);
x_15 = lean_alloc_closure((void*)(l_Lean_ppLine_formatter___boxed), 5, 0);
x_16 = lean_alloc_closure((void*)(l_Lean_ppDedent_formatter), 6, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = lean_mk_string_unchecked("finally ", 8, 8);
x_18 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter), 6, 1);
lean_closure_set(x_18, 0, x_17);
x_19 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doSeq_formatter), 5, 0);
x_20 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_20, 0, x_18);
lean_closure_set(x_20, 1, x_19);
x_21 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_21, 0, x_16);
lean_closure_set(x_21, 1, x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(x_22, 0, x_10);
lean_closure_set(x_22, 1, x_14);
lean_closure_set(x_22, 2, x_21);
x_23 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_13, x_22, x_1, x_2, x_3, x_4, x_5);
return x_23;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doFinally_formatter__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_formatterAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("doFinally", 9, 9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("formatter", 9, 9);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doFinally_formatter), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doTry_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("Parser", 6, 6);
x_8 = lean_mk_string_unchecked("Term", 4, 4);
x_9 = lean_mk_string_unchecked("doTry", 5, 5);
lean_inc(x_9);
x_10 = l_Lean_Name_mkStr4(x_6, x_7, x_8, x_9);
x_11 = lean_box(1);
x_12 = lean_box(0);
lean_inc(x_10);
x_13 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(x_13, 0, x_9);
lean_closure_set(x_13, 1, x_10);
lean_closure_set(x_13, 2, x_11);
lean_closure_set(x_13, 3, x_12);
x_14 = lean_unsigned_to_nat(1024u);
x_15 = lean_mk_string_unchecked("try ", 4, 4);
x_16 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter), 6, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doSeq_formatter), 5, 0);
x_18 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doCatch_formatter), 5, 0);
x_19 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doCatchMatch_formatter), 5, 0);
x_20 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter), 7, 2);
lean_closure_set(x_20, 0, x_18);
lean_closure_set(x_20, 1, x_19);
x_21 = lean_alloc_closure((void*)(l_Lean_Parser_many_formatter), 6, 1);
lean_closure_set(x_21, 0, x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doFinally_formatter), 5, 0);
x_23 = lean_alloc_closure((void*)(l_Lean_Parser_optional_formatter), 6, 1);
lean_closure_set(x_23, 0, x_22);
x_24 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_24, 0, x_21);
lean_closure_set(x_24, 1, x_23);
x_25 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_25, 0, x_17);
lean_closure_set(x_25, 1, x_24);
x_26 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_26, 0, x_16);
lean_closure_set(x_26, 1, x_25);
x_27 = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(x_27, 0, x_10);
lean_closure_set(x_27, 1, x_14);
lean_closure_set(x_27, 2, x_26);
x_28 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_13, x_27, x_1, x_2, x_3, x_4, x_5);
return x_28;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doTry_formatter__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_formatterAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("doTry", 5, 5);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("formatter", 9, 9);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doTry_formatter), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doCatch_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doSeqItem_parenthesizer___lam__0___boxed), 5, 0);
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
x_8 = lean_mk_string_unchecked("Parser", 6, 6);
x_9 = lean_mk_string_unchecked("Term", 4, 4);
x_10 = lean_mk_string_unchecked("doCatch", 7, 7);
lean_inc(x_10);
x_11 = l_Lean_Name_mkStr4(x_7, x_8, x_9, x_10);
x_12 = lean_box(1);
x_13 = lean_box(0);
lean_inc(x_11);
x_14 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(x_14, 0, x_10);
lean_closure_set(x_14, 1, x_11);
lean_closure_set(x_14, 2, x_12);
lean_closure_set(x_14, 3, x_13);
x_15 = lean_unsigned_to_nat(1024u);
x_16 = lean_mk_string_unchecked("catch ", 6, 6);
x_17 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___boxed), 6, 1);
lean_closure_set(x_17, 0, x_16);
x_18 = lean_alloc_closure((void*)(l_Lean_Parser_Term_binderIdent_parenthesizer), 5, 0);
x_19 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doIdDecl_parenthesizer___lam__1), 7, 2);
lean_closure_set(x_19, 0, x_17);
lean_closure_set(x_19, 1, x_18);
x_20 = lean_mk_string_unchecked(" : ", 3, 3);
x_21 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___boxed), 6, 1);
lean_closure_set(x_21, 0, x_20);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_alloc_closure((void*)(l_Lean_Parser_termParser_parenthesizer), 6, 1);
lean_closure_set(x_23, 0, x_22);
x_24 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_24, 0, x_21);
lean_closure_set(x_24, 1, x_23);
x_25 = lean_alloc_closure((void*)(l_Lean_Parser_optional_parenthesizer), 6, 1);
lean_closure_set(x_25, 0, x_24);
x_26 = lean_alloc_closure((void*)(l_Lean_Parser_darrow_parenthesizer), 5, 0);
x_27 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doSeq_parenthesizer), 5, 0);
x_28 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_28, 0, x_26);
lean_closure_set(x_28, 1, x_27);
x_29 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_29, 0, x_25);
lean_closure_set(x_29, 1, x_28);
x_30 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_30, 0, x_19);
lean_closure_set(x_30, 1, x_29);
x_31 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_31, 0, x_6);
lean_closure_set(x_31, 1, x_30);
x_32 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer), 8, 3);
lean_closure_set(x_32, 0, x_11);
lean_closure_set(x_32, 1, x_15);
lean_closure_set(x_32, 2, x_31);
x_33 = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(x_14, x_32, x_1, x_2, x_3, x_4, x_5);
return x_33;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doCatch_parenthesizer__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("doCatch", 7, 7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("parenthesizer", 13, 13);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doCatch_parenthesizer), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doCatchMatch_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doSeqItem_parenthesizer___lam__0___boxed), 5, 0);
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
x_8 = lean_mk_string_unchecked("Parser", 6, 6);
x_9 = lean_mk_string_unchecked("Term", 4, 4);
x_10 = lean_mk_string_unchecked("doCatchMatch", 12, 12);
lean_inc(x_10);
x_11 = l_Lean_Name_mkStr4(x_7, x_8, x_9, x_10);
x_12 = lean_box(1);
x_13 = lean_box(0);
lean_inc(x_11);
x_14 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(x_14, 0, x_10);
lean_closure_set(x_14, 1, x_11);
lean_closure_set(x_14, 2, x_12);
lean_closure_set(x_14, 3, x_13);
x_15 = lean_unsigned_to_nat(1024u);
x_16 = lean_mk_string_unchecked("catch ", 6, 6);
x_17 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___boxed), 6, 1);
lean_closure_set(x_17, 0, x_16);
x_18 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doMatchAlts_parenthesizer), 5, 0);
x_19 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_19, 0, x_17);
lean_closure_set(x_19, 1, x_18);
x_20 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_20, 0, x_6);
lean_closure_set(x_20, 1, x_19);
x_21 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer), 8, 3);
lean_closure_set(x_21, 0, x_11);
lean_closure_set(x_21, 1, x_15);
lean_closure_set(x_21, 2, x_20);
x_22 = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(x_14, x_21, x_1, x_2, x_3, x_4, x_5);
return x_22;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doCatchMatch_parenthesizer__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("doCatchMatch", 12, 12);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("parenthesizer", 13, 13);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doCatchMatch_parenthesizer), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doFinally_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doSeqItem_parenthesizer___lam__0___boxed), 5, 0);
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
x_8 = lean_mk_string_unchecked("Parser", 6, 6);
x_9 = lean_mk_string_unchecked("Term", 4, 4);
x_10 = lean_mk_string_unchecked("doFinally", 9, 9);
lean_inc(x_10);
x_11 = l_Lean_Name_mkStr4(x_7, x_8, x_9, x_10);
x_12 = lean_box(1);
x_13 = lean_box(0);
lean_inc(x_11);
x_14 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(x_14, 0, x_10);
lean_closure_set(x_14, 1, x_11);
lean_closure_set(x_14, 2, x_12);
lean_closure_set(x_14, 3, x_13);
x_15 = lean_unsigned_to_nat(1024u);
x_16 = lean_mk_string_unchecked("finally ", 8, 8);
x_17 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___boxed), 6, 1);
lean_closure_set(x_17, 0, x_16);
x_18 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doSeq_parenthesizer), 5, 0);
x_19 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_19, 0, x_17);
lean_closure_set(x_19, 1, x_18);
x_20 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_20, 0, x_6);
lean_closure_set(x_20, 1, x_19);
x_21 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer), 8, 3);
lean_closure_set(x_21, 0, x_11);
lean_closure_set(x_21, 1, x_15);
lean_closure_set(x_21, 2, x_20);
x_22 = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(x_14, x_21, x_1, x_2, x_3, x_4, x_5);
return x_22;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doFinally_parenthesizer__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("doFinally", 9, 9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("parenthesizer", 13, 13);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doFinally_parenthesizer), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doTry_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("Parser", 6, 6);
x_8 = lean_mk_string_unchecked("Term", 4, 4);
x_9 = lean_mk_string_unchecked("doTry", 5, 5);
lean_inc(x_9);
x_10 = l_Lean_Name_mkStr4(x_6, x_7, x_8, x_9);
x_11 = lean_box(1);
x_12 = lean_box(0);
lean_inc(x_10);
x_13 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(x_13, 0, x_9);
lean_closure_set(x_13, 1, x_10);
lean_closure_set(x_13, 2, x_11);
lean_closure_set(x_13, 3, x_12);
x_14 = lean_unsigned_to_nat(1024u);
x_15 = lean_mk_string_unchecked("try ", 4, 4);
x_16 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___boxed), 6, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doSeq_parenthesizer), 5, 0);
x_18 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doCatch_parenthesizer), 5, 0);
x_19 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doCatchMatch_parenthesizer), 5, 0);
x_20 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer), 7, 2);
lean_closure_set(x_20, 0, x_18);
lean_closure_set(x_20, 1, x_19);
x_21 = lean_alloc_closure((void*)(l_Lean_Parser_many_parenthesizer), 6, 1);
lean_closure_set(x_21, 0, x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doFinally_parenthesizer), 5, 0);
x_23 = lean_alloc_closure((void*)(l_Lean_Parser_optional_parenthesizer), 6, 1);
lean_closure_set(x_23, 0, x_22);
x_24 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_24, 0, x_21);
lean_closure_set(x_24, 1, x_23);
x_25 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_25, 0, x_17);
lean_closure_set(x_25, 1, x_24);
x_26 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_26, 0, x_16);
lean_closure_set(x_26, 1, x_25);
x_27 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer), 8, 3);
lean_closure_set(x_27, 0, x_10);
lean_closure_set(x_27, 1, x_14);
lean_closure_set(x_27, 2, x_26);
x_28 = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(x_13, x_27, x_1, x_2, x_3, x_4, x_5);
return x_28;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doTry_parenthesizer__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("doTry", 5, 5);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("parenthesizer", 13, 13);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doTry_parenthesizer), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
static lean_object* _init_l_Lean_Parser_Term_doBreak() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Term", 4, 4);
x_4 = lean_mk_string_unchecked("doBreak", 7, 7);
lean_inc(x_4);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_box(1);
x_7 = lean_box(0);
x_8 = lean_unbox(x_6);
x_9 = lean_unbox(x_7);
lean_inc(x_5);
x_10 = l_Lean_Parser_mkAntiquot(x_4, x_5, x_8, x_9);
lean_dec(x_4);
x_11 = lean_unsigned_to_nat(1024u);
x_12 = lean_mk_string_unchecked("break", 5, 5);
x_13 = l_Lean_Parser_symbol(x_12);
lean_dec(x_12);
lean_inc(x_5);
x_14 = l_Lean_Parser_leadingNode(x_5, x_11, x_13);
x_15 = l_Lean_Parser_withAntiquot(x_10, x_14);
x_16 = l_Lean_Parser_withCache(x_5, x_15);
return x_16;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doBreak__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = lean_mk_string_unchecked("doElem", 6, 6);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Term", 4, 4);
x_7 = lean_mk_string_unchecked("doBreak", 7, 7);
x_8 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_7);
x_9 = l_Lean_Parser_Term_doBreak;
x_10 = lean_unsigned_to_nat(1000u);
x_11 = l_Lean_Parser_addBuiltinLeadingParser(x_3, x_8, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doBreak_docString__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Term", 4, 4);
x_5 = lean_mk_string_unchecked("doBreak", 7, 7);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_mk_string_unchecked("`break` exits the surrounding `for` loop. ", 42, 42);
x_8 = l_Lean_addBuiltinDocString(x_6, x_7, x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doBreak_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Term", 4, 4);
x_5 = lean_mk_string_unchecked("doBreak", 7, 7);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(177u);
x_8 = lean_unsigned_to_nat(25u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(66u);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_8);
lean_ctor_set(x_12, 2, x_11);
lean_ctor_set(x_12, 3, x_10);
x_13 = lean_unsigned_to_nat(29u);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_unsigned_to_nat(36u);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_7);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_13);
lean_ctor_set(x_17, 2, x_16);
lean_ctor_set(x_17, 3, x_15);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_addBuiltinDeclarationRanges(x_6, x_18, x_1);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doBreak_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("Parser", 6, 6);
x_8 = lean_mk_string_unchecked("Term", 4, 4);
x_9 = lean_mk_string_unchecked("doBreak", 7, 7);
lean_inc(x_9);
x_10 = l_Lean_Name_mkStr4(x_6, x_7, x_8, x_9);
x_11 = lean_box(1);
x_12 = lean_box(0);
lean_inc(x_10);
x_13 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(x_13, 0, x_9);
lean_closure_set(x_13, 1, x_10);
lean_closure_set(x_13, 2, x_11);
lean_closure_set(x_13, 3, x_12);
x_14 = lean_unsigned_to_nat(1024u);
x_15 = lean_mk_string_unchecked("break", 5, 5);
x_16 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter), 6, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(x_17, 0, x_10);
lean_closure_set(x_17, 1, x_14);
lean_closure_set(x_17, 2, x_16);
x_18 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_13, x_17, x_1, x_2, x_3, x_4, x_5);
return x_18;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doBreak_formatter__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_formatterAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("doBreak", 7, 7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("formatter", 9, 9);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doBreak_formatter), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doBreak_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("Parser", 6, 6);
x_8 = lean_mk_string_unchecked("Term", 4, 4);
x_9 = lean_mk_string_unchecked("doBreak", 7, 7);
lean_inc(x_9);
x_10 = l_Lean_Name_mkStr4(x_6, x_7, x_8, x_9);
x_11 = lean_box(1);
x_12 = lean_box(0);
lean_inc(x_10);
x_13 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(x_13, 0, x_9);
lean_closure_set(x_13, 1, x_10);
lean_closure_set(x_13, 2, x_11);
lean_closure_set(x_13, 3, x_12);
x_14 = lean_unsigned_to_nat(1024u);
x_15 = lean_mk_string_unchecked("break", 5, 5);
x_16 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___boxed), 6, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer), 8, 3);
lean_closure_set(x_17, 0, x_10);
lean_closure_set(x_17, 1, x_14);
lean_closure_set(x_17, 2, x_16);
x_18 = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(x_13, x_17, x_1, x_2, x_3, x_4, x_5);
return x_18;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doBreak_parenthesizer__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("doBreak", 7, 7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("parenthesizer", 13, 13);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doBreak_parenthesizer), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
static lean_object* _init_l_Lean_Parser_Term_doContinue() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Term", 4, 4);
x_4 = lean_mk_string_unchecked("doContinue", 10, 10);
lean_inc(x_4);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_box(1);
x_7 = lean_box(0);
x_8 = lean_unbox(x_6);
x_9 = lean_unbox(x_7);
lean_inc(x_5);
x_10 = l_Lean_Parser_mkAntiquot(x_4, x_5, x_8, x_9);
lean_dec(x_4);
x_11 = lean_unsigned_to_nat(1024u);
x_12 = lean_mk_string_unchecked("continue", 8, 8);
x_13 = l_Lean_Parser_symbol(x_12);
lean_dec(x_12);
lean_inc(x_5);
x_14 = l_Lean_Parser_leadingNode(x_5, x_11, x_13);
x_15 = l_Lean_Parser_withAntiquot(x_10, x_14);
x_16 = l_Lean_Parser_withCache(x_5, x_15);
return x_16;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doContinue__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = lean_mk_string_unchecked("doElem", 6, 6);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Term", 4, 4);
x_7 = lean_mk_string_unchecked("doContinue", 10, 10);
x_8 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_7);
x_9 = l_Lean_Parser_Term_doContinue;
x_10 = lean_unsigned_to_nat(1000u);
x_11 = l_Lean_Parser_addBuiltinLeadingParser(x_3, x_8, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doContinue_docString__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Term", 4, 4);
x_5 = lean_mk_string_unchecked("doContinue", 10, 10);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_mk_string_unchecked("`continue` skips to the next iteration of the surrounding `for` loop. ", 70, 70);
x_8 = l_Lean_addBuiltinDocString(x_6, x_7, x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doContinue_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Term", 4, 4);
x_5 = lean_mk_string_unchecked("doContinue", 10, 10);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(179u);
x_8 = lean_unsigned_to_nat(25u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(69u);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_8);
lean_ctor_set(x_12, 2, x_11);
lean_ctor_set(x_12, 3, x_10);
x_13 = lean_unsigned_to_nat(29u);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_unsigned_to_nat(39u);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_7);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_13);
lean_ctor_set(x_17, 2, x_16);
lean_ctor_set(x_17, 3, x_15);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_addBuiltinDeclarationRanges(x_6, x_18, x_1);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doContinue_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("Parser", 6, 6);
x_8 = lean_mk_string_unchecked("Term", 4, 4);
x_9 = lean_mk_string_unchecked("doContinue", 10, 10);
lean_inc(x_9);
x_10 = l_Lean_Name_mkStr4(x_6, x_7, x_8, x_9);
x_11 = lean_box(1);
x_12 = lean_box(0);
lean_inc(x_10);
x_13 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(x_13, 0, x_9);
lean_closure_set(x_13, 1, x_10);
lean_closure_set(x_13, 2, x_11);
lean_closure_set(x_13, 3, x_12);
x_14 = lean_unsigned_to_nat(1024u);
x_15 = lean_mk_string_unchecked("continue", 8, 8);
x_16 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter), 6, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(x_17, 0, x_10);
lean_closure_set(x_17, 1, x_14);
lean_closure_set(x_17, 2, x_16);
x_18 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_13, x_17, x_1, x_2, x_3, x_4, x_5);
return x_18;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doContinue_formatter__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_formatterAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("doContinue", 10, 10);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("formatter", 9, 9);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doContinue_formatter), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doContinue_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("Parser", 6, 6);
x_8 = lean_mk_string_unchecked("Term", 4, 4);
x_9 = lean_mk_string_unchecked("doContinue", 10, 10);
lean_inc(x_9);
x_10 = l_Lean_Name_mkStr4(x_6, x_7, x_8, x_9);
x_11 = lean_box(1);
x_12 = lean_box(0);
lean_inc(x_10);
x_13 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(x_13, 0, x_9);
lean_closure_set(x_13, 1, x_10);
lean_closure_set(x_13, 2, x_11);
lean_closure_set(x_13, 3, x_12);
x_14 = lean_unsigned_to_nat(1024u);
x_15 = lean_mk_string_unchecked("continue", 8, 8);
x_16 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___boxed), 6, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer), 8, 3);
lean_closure_set(x_17, 0, x_10);
lean_closure_set(x_17, 1, x_14);
lean_closure_set(x_17, 2, x_16);
x_18 = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(x_13, x_17, x_1, x_2, x_3, x_4, x_5);
return x_18;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doContinue_parenthesizer__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("doContinue", 10, 10);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("parenthesizer", 13, 13);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doContinue_parenthesizer), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
static lean_object* _init_l_Lean_Parser_Term_doReturn() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Term", 4, 4);
x_4 = lean_mk_string_unchecked("doReturn", 8, 8);
lean_inc(x_4);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_box(1);
x_7 = lean_box(0);
x_8 = lean_unbox(x_6);
x_9 = lean_unbox(x_7);
lean_inc(x_5);
x_10 = l_Lean_Parser_mkAntiquot(x_4, x_5, x_8, x_9);
lean_dec(x_4);
x_11 = lean_unsigned_to_nat(1022u);
x_12 = lean_mk_string_unchecked("return", 6, 6);
x_13 = l_Lean_Parser_symbol(x_12);
lean_dec(x_12);
x_14 = l_Lean_Parser_skip;
x_15 = lean_mk_string_unchecked("checkLineEq", 11, 11);
x_16 = l_Lean_Parser_checkLineEq(x_15);
x_17 = lean_unsigned_to_nat(0u);
x_18 = l_Lean_Parser_termParser(x_17);
x_19 = l_Lean_Parser_andthen(x_16, x_18);
x_20 = l_Lean_Parser_andthen(x_14, x_19);
x_21 = l_Lean_Parser_optional(x_20);
x_22 = l_Lean_Parser_andthen(x_13, x_21);
x_23 = l_Lean_Parser_withPosition(x_22);
lean_inc(x_5);
x_24 = l_Lean_Parser_leadingNode(x_5, x_11, x_23);
x_25 = l_Lean_Parser_withAntiquot(x_10, x_24);
x_26 = l_Lean_Parser_withCache(x_5, x_25);
return x_26;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doReturn__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = lean_mk_string_unchecked("doElem", 6, 6);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Term", 4, 4);
x_7 = lean_mk_string_unchecked("doReturn", 8, 8);
x_8 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_7);
x_9 = l_Lean_Parser_Term_doReturn;
x_10 = lean_unsigned_to_nat(1000u);
x_11 = l_Lean_Parser_addBuiltinLeadingParser(x_3, x_8, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doReturn_docString__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Term", 4, 4);
x_5 = lean_mk_string_unchecked("doReturn", 8, 8);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_mk_string_unchecked("`return e` inside of a `do` block makes the surrounding block evaluate to `pure e`,\nskipping any further statements.\nNote that uses of the `do` keyword in other syntax like in `for _ in _ do`\ndo not constitute a surrounding block in this sense;\nin supported editors, the corresponding `do` keyword of the surrounding block\nis highlighted when hovering over `return`.\n\n`return` not followed by a term starting on the same line is equivalent to `return ()`.\n", 456, 456);
x_8 = l_Lean_addBuiltinDocString(x_6, x_7, x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doReturn_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Term", 4, 4);
x_5 = lean_mk_string_unchecked("doReturn", 8, 8);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(190u);
x_8 = lean_unsigned_to_nat(25u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(191u);
x_11 = lean_unsigned_to_nat(76u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_11);
x_14 = lean_unsigned_to_nat(29u);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_unsigned_to_nat(37u);
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
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doReturn_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doIdDecl_formatter___lam__0___boxed), 5, 0);
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
x_8 = lean_mk_string_unchecked("Parser", 6, 6);
x_9 = lean_mk_string_unchecked("Term", 4, 4);
x_10 = lean_mk_string_unchecked("doReturn", 8, 8);
lean_inc(x_10);
x_11 = l_Lean_Name_mkStr4(x_7, x_8, x_9, x_10);
x_12 = lean_box(1);
x_13 = lean_box(0);
lean_inc(x_11);
x_14 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(x_14, 0, x_10);
lean_closure_set(x_14, 1, x_11);
lean_closure_set(x_14, 2, x_12);
lean_closure_set(x_14, 3, x_13);
x_15 = lean_unsigned_to_nat(1022u);
x_16 = lean_mk_string_unchecked("return", 6, 6);
x_17 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter), 6, 1);
lean_closure_set(x_17, 0, x_16);
x_18 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkLineEq_formatter___boxed), 5, 0);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_alloc_closure((void*)(l_Lean_Parser_termParser_formatter___boxed), 6, 1);
lean_closure_set(x_20, 0, x_19);
x_21 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_21, 0, x_18);
lean_closure_set(x_21, 1, x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_22, 0, x_6);
lean_closure_set(x_22, 1, x_21);
x_23 = lean_alloc_closure((void*)(l_Lean_Parser_optional_formatter), 6, 1);
lean_closure_set(x_23, 0, x_22);
x_24 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_24, 0, x_17);
lean_closure_set(x_24, 1, x_23);
x_25 = lean_alloc_closure((void*)(l_Lean_Parser_withPosition_formatter), 6, 1);
lean_closure_set(x_25, 0, x_24);
x_26 = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(x_26, 0, x_11);
lean_closure_set(x_26, 1, x_15);
lean_closure_set(x_26, 2, x_25);
x_27 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_14, x_26, x_1, x_2, x_3, x_4, x_5);
return x_27;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doReturn_formatter__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_formatterAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("doReturn", 8, 8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("formatter", 9, 9);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doReturn_formatter), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doReturn_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doSeqItem_parenthesizer___lam__0___boxed), 5, 0);
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
x_8 = lean_mk_string_unchecked("Parser", 6, 6);
x_9 = lean_mk_string_unchecked("Term", 4, 4);
x_10 = lean_mk_string_unchecked("doReturn", 8, 8);
lean_inc(x_10);
x_11 = l_Lean_Name_mkStr4(x_7, x_8, x_9, x_10);
x_12 = lean_box(1);
x_13 = lean_box(0);
lean_inc(x_11);
x_14 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(x_14, 0, x_10);
lean_closure_set(x_14, 1, x_11);
lean_closure_set(x_14, 2, x_12);
lean_closure_set(x_14, 3, x_13);
x_15 = lean_unsigned_to_nat(1022u);
x_16 = lean_mk_string_unchecked("return", 6, 6);
x_17 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___boxed), 6, 1);
lean_closure_set(x_17, 0, x_16);
x_18 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkLineEq_parenthesizer___boxed), 5, 0);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_alloc_closure((void*)(l_Lean_Parser_termParser_parenthesizer), 6, 1);
lean_closure_set(x_20, 0, x_19);
x_21 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_21, 0, x_18);
lean_closure_set(x_21, 1, x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_22, 0, x_6);
lean_closure_set(x_22, 1, x_21);
x_23 = lean_alloc_closure((void*)(l_Lean_Parser_optional_parenthesizer), 6, 1);
lean_closure_set(x_23, 0, x_22);
x_24 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_24, 0, x_17);
lean_closure_set(x_24, 1, x_23);
x_25 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_withPosition_parenthesizer), 6, 1);
lean_closure_set(x_25, 0, x_24);
x_26 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer), 8, 3);
lean_closure_set(x_26, 0, x_11);
lean_closure_set(x_26, 1, x_15);
lean_closure_set(x_26, 2, x_25);
x_27 = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(x_14, x_26, x_1, x_2, x_3, x_4, x_5);
return x_27;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doReturn_parenthesizer__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("doReturn", 8, 8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("parenthesizer", 13, 13);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doReturn_parenthesizer), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
static lean_object* _init_l_Lean_Parser_Term_doDbgTrace() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Term", 4, 4);
x_4 = lean_mk_string_unchecked("doDbgTrace", 10, 10);
lean_inc(x_4);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_box(1);
x_7 = lean_box(0);
x_8 = lean_unbox(x_6);
x_9 = lean_unbox(x_7);
lean_inc(x_5);
x_10 = l_Lean_Parser_mkAntiquot(x_4, x_5, x_8, x_9);
lean_dec(x_4);
x_11 = lean_unsigned_to_nat(1022u);
x_12 = lean_mk_string_unchecked("dbg_trace ", 10, 10);
x_13 = l_Lean_Parser_symbol(x_12);
lean_dec(x_12);
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Lean_Parser_termParser(x_14);
lean_inc(x_15);
x_16 = l_Lean_Parser_interpolatedStr(x_15);
x_17 = l_Lean_Parser_orelse(x_16, x_15);
x_18 = l_Lean_Parser_andthen(x_13, x_17);
lean_inc(x_5);
x_19 = l_Lean_Parser_leadingNode(x_5, x_11, x_18);
x_20 = l_Lean_Parser_withAntiquot(x_10, x_19);
x_21 = l_Lean_Parser_withCache(x_5, x_20);
return x_21;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doDbgTrace__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = lean_mk_string_unchecked("doElem", 6, 6);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Term", 4, 4);
x_7 = lean_mk_string_unchecked("doDbgTrace", 10, 10);
x_8 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_7);
x_9 = l_Lean_Parser_Term_doDbgTrace;
x_10 = lean_unsigned_to_nat(1000u);
x_11 = l_Lean_Parser_addBuiltinLeadingParser(x_3, x_8, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doDbgTrace_docString__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Term", 4, 4);
x_5 = lean_mk_string_unchecked("doDbgTrace", 10, 10);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_mk_string_unchecked("`dbg_trace e` prints `e` (which can be an interpolated string literal) to stderr.\nIt should only be used for debugging.\n", 120, 120);
x_8 = l_Lean_addBuiltinDocString(x_6, x_7, x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doDbgTrace_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Term", 4, 4);
x_5 = lean_mk_string_unchecked("doDbgTrace", 10, 10);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(196u);
x_8 = lean_unsigned_to_nat(25u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(197u);
x_11 = lean_unsigned_to_nat(63u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_11);
x_14 = lean_unsigned_to_nat(29u);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_unsigned_to_nat(39u);
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
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doDbgTrace_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("Parser", 6, 6);
x_8 = lean_mk_string_unchecked("Term", 4, 4);
x_9 = lean_mk_string_unchecked("doDbgTrace", 10, 10);
lean_inc(x_9);
x_10 = l_Lean_Name_mkStr4(x_6, x_7, x_8, x_9);
x_11 = lean_box(1);
x_12 = lean_box(0);
lean_inc(x_10);
x_13 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(x_13, 0, x_9);
lean_closure_set(x_13, 1, x_10);
lean_closure_set(x_13, 2, x_11);
lean_closure_set(x_13, 3, x_12);
x_14 = lean_unsigned_to_nat(1022u);
x_15 = lean_mk_string_unchecked("dbg_trace ", 10, 10);
x_16 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter), 6, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_alloc_closure((void*)(l_Lean_Parser_termParser_formatter___boxed), 6, 1);
lean_closure_set(x_18, 0, x_17);
lean_inc(x_18);
x_19 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter), 6, 1);
lean_closure_set(x_19, 0, x_18);
x_20 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter), 7, 2);
lean_closure_set(x_20, 0, x_19);
lean_closure_set(x_20, 1, x_18);
x_21 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_21, 0, x_16);
lean_closure_set(x_21, 1, x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(x_22, 0, x_10);
lean_closure_set(x_22, 1, x_14);
lean_closure_set(x_22, 2, x_21);
x_23 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_13, x_22, x_1, x_2, x_3, x_4, x_5);
return x_23;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doDbgTrace_formatter__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_formatterAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("doDbgTrace", 10, 10);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("formatter", 9, 9);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doDbgTrace_formatter), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doDbgTrace_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("Parser", 6, 6);
x_8 = lean_mk_string_unchecked("Term", 4, 4);
x_9 = lean_mk_string_unchecked("doDbgTrace", 10, 10);
lean_inc(x_9);
x_10 = l_Lean_Name_mkStr4(x_6, x_7, x_8, x_9);
x_11 = lean_box(1);
x_12 = lean_box(0);
lean_inc(x_10);
x_13 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(x_13, 0, x_9);
lean_closure_set(x_13, 1, x_10);
lean_closure_set(x_13, 2, x_11);
lean_closure_set(x_13, 3, x_12);
x_14 = lean_unsigned_to_nat(1022u);
x_15 = lean_mk_string_unchecked("dbg_trace ", 10, 10);
x_16 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___boxed), 6, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_alloc_closure((void*)(l_Lean_Parser_termParser_parenthesizer), 6, 1);
lean_closure_set(x_18, 0, x_17);
lean_inc(x_18);
x_19 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_interpolatedStr_parenthesizer), 6, 1);
lean_closure_set(x_19, 0, x_18);
x_20 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer), 7, 2);
lean_closure_set(x_20, 0, x_19);
lean_closure_set(x_20, 1, x_18);
x_21 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_21, 0, x_16);
lean_closure_set(x_21, 1, x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer), 8, 3);
lean_closure_set(x_22, 0, x_10);
lean_closure_set(x_22, 1, x_14);
lean_closure_set(x_22, 2, x_21);
x_23 = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(x_13, x_22, x_1, x_2, x_3, x_4, x_5);
return x_23;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doDbgTrace_parenthesizer__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("doDbgTrace", 10, 10);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("parenthesizer", 13, 13);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doDbgTrace_parenthesizer), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
static lean_object* _init_l_Lean_Parser_Term_doAssert() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Term", 4, 4);
x_4 = lean_mk_string_unchecked("doAssert", 8, 8);
lean_inc(x_4);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_box(1);
x_7 = lean_box(0);
x_8 = lean_unbox(x_6);
x_9 = lean_unbox(x_7);
lean_inc(x_5);
x_10 = l_Lean_Parser_mkAntiquot(x_4, x_5, x_8, x_9);
lean_dec(x_4);
x_11 = lean_unsigned_to_nat(1022u);
x_12 = lean_mk_string_unchecked("assert! ", 8, 8);
x_13 = l_Lean_Parser_symbol(x_12);
lean_dec(x_12);
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Lean_Parser_termParser(x_14);
x_16 = l_Lean_Parser_andthen(x_13, x_15);
lean_inc(x_5);
x_17 = l_Lean_Parser_leadingNode(x_5, x_11, x_16);
x_18 = l_Lean_Parser_withAntiquot(x_10, x_17);
x_19 = l_Lean_Parser_withCache(x_5, x_18);
return x_19;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doAssert__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = lean_mk_string_unchecked("doElem", 6, 6);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Term", 4, 4);
x_7 = lean_mk_string_unchecked("doAssert", 8, 8);
x_8 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_7);
x_9 = l_Lean_Parser_Term_doAssert;
x_10 = lean_unsigned_to_nat(1000u);
x_11 = l_Lean_Parser_addBuiltinLeadingParser(x_3, x_8, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doAssert_docString__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Term", 4, 4);
x_5 = lean_mk_string_unchecked("doAssert", 8, 8);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_mk_string_unchecked("`assert! cond` panics if `cond` evaluates to `false`.\n", 54, 54);
x_8 = l_Lean_addBuiltinDocString(x_6, x_7, x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doAssert_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Term", 4, 4);
x_5 = lean_mk_string_unchecked("doAssert", 8, 8);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(201u);
x_8 = lean_unsigned_to_nat(25u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(202u);
x_11 = lean_unsigned_to_nat(26u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_11);
x_14 = lean_unsigned_to_nat(29u);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_unsigned_to_nat(37u);
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
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doAssert_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("Parser", 6, 6);
x_8 = lean_mk_string_unchecked("Term", 4, 4);
x_9 = lean_mk_string_unchecked("doAssert", 8, 8);
lean_inc(x_9);
x_10 = l_Lean_Name_mkStr4(x_6, x_7, x_8, x_9);
x_11 = lean_box(1);
x_12 = lean_box(0);
lean_inc(x_10);
x_13 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(x_13, 0, x_9);
lean_closure_set(x_13, 1, x_10);
lean_closure_set(x_13, 2, x_11);
lean_closure_set(x_13, 3, x_12);
x_14 = lean_unsigned_to_nat(1022u);
x_15 = lean_mk_string_unchecked("assert! ", 8, 8);
x_16 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter), 6, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_alloc_closure((void*)(l_Lean_Parser_termParser_formatter___boxed), 6, 1);
lean_closure_set(x_18, 0, x_17);
x_19 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_19, 0, x_16);
lean_closure_set(x_19, 1, x_18);
x_20 = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(x_20, 0, x_10);
lean_closure_set(x_20, 1, x_14);
lean_closure_set(x_20, 2, x_19);
x_21 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_13, x_20, x_1, x_2, x_3, x_4, x_5);
return x_21;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doAssert_formatter__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_formatterAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("doAssert", 8, 8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("formatter", 9, 9);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doAssert_formatter), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doAssert_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("Parser", 6, 6);
x_8 = lean_mk_string_unchecked("Term", 4, 4);
x_9 = lean_mk_string_unchecked("doAssert", 8, 8);
lean_inc(x_9);
x_10 = l_Lean_Name_mkStr4(x_6, x_7, x_8, x_9);
x_11 = lean_box(1);
x_12 = lean_box(0);
lean_inc(x_10);
x_13 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(x_13, 0, x_9);
lean_closure_set(x_13, 1, x_10);
lean_closure_set(x_13, 2, x_11);
lean_closure_set(x_13, 3, x_12);
x_14 = lean_unsigned_to_nat(1022u);
x_15 = lean_mk_string_unchecked("assert! ", 8, 8);
x_16 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___boxed), 6, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_alloc_closure((void*)(l_Lean_Parser_termParser_parenthesizer), 6, 1);
lean_closure_set(x_18, 0, x_17);
x_19 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_19, 0, x_16);
lean_closure_set(x_19, 1, x_18);
x_20 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer), 8, 3);
lean_closure_set(x_20, 0, x_10);
lean_closure_set(x_20, 1, x_14);
lean_closure_set(x_20, 2, x_19);
x_21 = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(x_13, x_20, x_1, x_2, x_3, x_4, x_5);
return x_21;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doAssert_parenthesizer__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("doAssert", 8, 8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("parenthesizer", 13, 13);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doAssert_parenthesizer), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
static lean_object* _init_l_Lean_Parser_Term_doDebugAssert() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Term", 4, 4);
x_4 = lean_mk_string_unchecked("doDebugAssert", 13, 13);
lean_inc(x_4);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_box(1);
x_7 = lean_box(0);
x_8 = lean_unbox(x_6);
x_9 = lean_unbox(x_7);
lean_inc(x_5);
x_10 = l_Lean_Parser_mkAntiquot(x_4, x_5, x_8, x_9);
lean_dec(x_4);
x_11 = lean_unsigned_to_nat(1022u);
x_12 = lean_mk_string_unchecked("debug_assert! ", 14, 14);
x_13 = l_Lean_Parser_symbol(x_12);
lean_dec(x_12);
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Lean_Parser_termParser(x_14);
x_16 = l_Lean_Parser_andthen(x_13, x_15);
lean_inc(x_5);
x_17 = l_Lean_Parser_leadingNode(x_5, x_11, x_16);
x_18 = l_Lean_Parser_withAntiquot(x_10, x_17);
x_19 = l_Lean_Parser_withCache(x_5, x_18);
return x_19;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doDebugAssert__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = lean_mk_string_unchecked("doElem", 6, 6);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Term", 4, 4);
x_7 = lean_mk_string_unchecked("doDebugAssert", 13, 13);
x_8 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_7);
x_9 = l_Lean_Parser_Term_doDebugAssert;
x_10 = lean_unsigned_to_nat(1000u);
x_11 = l_Lean_Parser_addBuiltinLeadingParser(x_3, x_8, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doDebugAssert_docString__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Term", 4, 4);
x_5 = lean_mk_string_unchecked("doDebugAssert", 13, 13);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_mk_string_unchecked("`debug_assert! cond` panics if `cond` evaluates to `false` and the executing code has been built\nwith debug assertions enabled (see the `debugAssertions` option).\n", 163, 163);
x_8 = l_Lean_addBuiltinDocString(x_6, x_7, x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doDebugAssert_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("Parser", 6, 6);
x_8 = lean_mk_string_unchecked("Term", 4, 4);
x_9 = lean_mk_string_unchecked("doDebugAssert", 13, 13);
lean_inc(x_9);
x_10 = l_Lean_Name_mkStr4(x_6, x_7, x_8, x_9);
x_11 = lean_box(1);
x_12 = lean_box(0);
lean_inc(x_10);
x_13 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(x_13, 0, x_9);
lean_closure_set(x_13, 1, x_10);
lean_closure_set(x_13, 2, x_11);
lean_closure_set(x_13, 3, x_12);
x_14 = lean_unsigned_to_nat(1022u);
x_15 = lean_mk_string_unchecked("debug_assert! ", 14, 14);
x_16 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter), 6, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_alloc_closure((void*)(l_Lean_Parser_termParser_formatter___boxed), 6, 1);
lean_closure_set(x_18, 0, x_17);
x_19 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_19, 0, x_16);
lean_closure_set(x_19, 1, x_18);
x_20 = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(x_20, 0, x_10);
lean_closure_set(x_20, 1, x_14);
lean_closure_set(x_20, 2, x_19);
x_21 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_13, x_20, x_1, x_2, x_3, x_4, x_5);
return x_21;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doDebugAssert_formatter__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_formatterAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("doDebugAssert", 13, 13);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("formatter", 9, 9);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doDebugAssert_formatter), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doDebugAssert_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("Parser", 6, 6);
x_8 = lean_mk_string_unchecked("Term", 4, 4);
x_9 = lean_mk_string_unchecked("doDebugAssert", 13, 13);
lean_inc(x_9);
x_10 = l_Lean_Name_mkStr4(x_6, x_7, x_8, x_9);
x_11 = lean_box(1);
x_12 = lean_box(0);
lean_inc(x_10);
x_13 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(x_13, 0, x_9);
lean_closure_set(x_13, 1, x_10);
lean_closure_set(x_13, 2, x_11);
lean_closure_set(x_13, 3, x_12);
x_14 = lean_unsigned_to_nat(1022u);
x_15 = lean_mk_string_unchecked("debug_assert! ", 14, 14);
x_16 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___boxed), 6, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_alloc_closure((void*)(l_Lean_Parser_termParser_parenthesizer), 6, 1);
lean_closure_set(x_18, 0, x_17);
x_19 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_19, 0, x_16);
lean_closure_set(x_19, 1, x_18);
x_20 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer), 8, 3);
lean_closure_set(x_20, 0, x_10);
lean_closure_set(x_20, 1, x_14);
lean_closure_set(x_20, 2, x_19);
x_21 = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(x_13, x_20, x_1, x_2, x_3, x_4, x_5);
return x_21;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doDebugAssert_parenthesizer__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("doDebugAssert", 13, 13);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("parenthesizer", 13, 13);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doDebugAssert_parenthesizer), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
static lean_object* _init_l_Lean_Parser_Term_doExpr() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Term", 4, 4);
x_4 = lean_mk_string_unchecked("doExpr", 6, 6);
lean_inc(x_4);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_box(1);
x_7 = lean_box(0);
x_8 = lean_unbox(x_6);
x_9 = lean_unbox(x_7);
lean_inc(x_5);
x_10 = l_Lean_Parser_mkAntiquot(x_4, x_5, x_8, x_9);
lean_dec(x_4);
x_11 = lean_unsigned_to_nat(1024u);
x_12 = l_Lean_Parser_Term_notFollowedByRedefinedTermToken;
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Lean_Parser_termParser(x_13);
x_15 = lean_mk_string_unchecked(":=", 2, 2);
x_16 = l_Lean_Parser_symbol(x_15);
lean_dec(x_15);
x_17 = l_Lean_Parser_Term_leftArrow;
x_18 = l_Lean_Parser_orelse(x_16, x_17);
x_19 = lean_mk_string_unchecked("unexpected token after 'expr' in 'do' block", 43, 43);
x_20 = l_Lean_Parser_notFollowedBy(x_18, x_19);
x_21 = l_Lean_Parser_andthen(x_14, x_20);
x_22 = l_Lean_Parser_andthen(x_12, x_21);
lean_inc(x_5);
x_23 = l_Lean_Parser_leadingNode(x_5, x_11, x_22);
x_24 = l_Lean_Parser_withAntiquot(x_10, x_23);
x_25 = l_Lean_Parser_withCache(x_5, x_24);
return x_25;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doExpr__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = lean_mk_string_unchecked("doElem", 6, 6);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Term", 4, 4);
x_7 = lean_mk_string_unchecked("doExpr", 6, 6);
x_8 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_7);
x_9 = l_Lean_Parser_Term_doExpr;
x_10 = lean_unsigned_to_nat(1000u);
x_11 = l_Lean_Parser_addBuiltinLeadingParser(x_3, x_8, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doExpr_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Term", 4, 4);
x_5 = lean_mk_string_unchecked("doExpr", 6, 6);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(220u);
x_8 = lean_unsigned_to_nat(25u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(223u);
x_11 = lean_unsigned_to_nat(49u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_11);
x_14 = lean_unsigned_to_nat(29u);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_unsigned_to_nat(35u);
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
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doExpr_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("Parser", 6, 6);
x_8 = lean_mk_string_unchecked("Term", 4, 4);
x_9 = lean_mk_string_unchecked("doExpr", 6, 6);
lean_inc(x_9);
x_10 = l_Lean_Name_mkStr4(x_6, x_7, x_8, x_9);
x_11 = lean_box(1);
x_12 = lean_box(0);
lean_inc(x_10);
x_13 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(x_13, 0, x_9);
lean_closure_set(x_13, 1, x_10);
lean_closure_set(x_13, 2, x_11);
lean_closure_set(x_13, 3, x_12);
x_14 = lean_unsigned_to_nat(1024u);
x_15 = lean_alloc_closure((void*)(l_Lean_Parser_Term_notFollowedByRedefinedTermToken_formatter___boxed), 5, 0);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_alloc_closure((void*)(l_Lean_Parser_termParser_formatter___boxed), 6, 1);
lean_closure_set(x_17, 0, x_16);
x_18 = lean_mk_string_unchecked(":=", 2, 2);
x_19 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter), 6, 1);
lean_closure_set(x_19, 0, x_18);
x_20 = lean_alloc_closure((void*)(l_Lean_Parser_Term_leftArrow_formatter), 5, 0);
x_21 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter), 7, 2);
lean_closure_set(x_21, 0, x_19);
lean_closure_set(x_21, 1, x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_notFollowedBy_formatter___boxed), 6, 1);
lean_closure_set(x_22, 0, x_21);
x_23 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_23, 0, x_17);
lean_closure_set(x_23, 1, x_22);
x_24 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_24, 0, x_15);
lean_closure_set(x_24, 1, x_23);
x_25 = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(x_25, 0, x_10);
lean_closure_set(x_25, 1, x_14);
lean_closure_set(x_25, 2, x_24);
x_26 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_13, x_25, x_1, x_2, x_3, x_4, x_5);
return x_26;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doExpr_formatter__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_formatterAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("doExpr", 6, 6);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("formatter", 9, 9);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doExpr_formatter), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doExpr_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("Parser", 6, 6);
x_8 = lean_mk_string_unchecked("Term", 4, 4);
x_9 = lean_mk_string_unchecked("doExpr", 6, 6);
lean_inc(x_9);
x_10 = l_Lean_Name_mkStr4(x_6, x_7, x_8, x_9);
x_11 = lean_box(1);
x_12 = lean_box(0);
lean_inc(x_10);
x_13 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(x_13, 0, x_9);
lean_closure_set(x_13, 1, x_10);
lean_closure_set(x_13, 2, x_11);
lean_closure_set(x_13, 3, x_12);
x_14 = lean_unsigned_to_nat(1024u);
x_15 = lean_alloc_closure((void*)(l_Lean_Parser_Term_notFollowedByRedefinedTermToken_parenthesizer___boxed), 5, 0);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_alloc_closure((void*)(l_Lean_Parser_termParser_parenthesizer), 6, 1);
lean_closure_set(x_17, 0, x_16);
x_18 = lean_mk_string_unchecked(":=", 2, 2);
x_19 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___boxed), 6, 1);
lean_closure_set(x_19, 0, x_18);
x_20 = lean_alloc_closure((void*)(l_Lean_Parser_Term_leftArrow_parenthesizer), 5, 0);
x_21 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer), 7, 2);
lean_closure_set(x_21, 0, x_19);
lean_closure_set(x_21, 1, x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_notFollowedBy_parenthesizer___boxed), 6, 1);
lean_closure_set(x_22, 0, x_21);
x_23 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_23, 0, x_17);
lean_closure_set(x_23, 1, x_22);
x_24 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_24, 0, x_15);
lean_closure_set(x_24, 1, x_23);
x_25 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer), 8, 3);
lean_closure_set(x_25, 0, x_10);
lean_closure_set(x_25, 1, x_14);
lean_closure_set(x_25, 2, x_24);
x_26 = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(x_13, x_25, x_1, x_2, x_3, x_4, x_5);
return x_26;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doExpr_parenthesizer__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("doExpr", 6, 6);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("parenthesizer", 13, 13);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doExpr_parenthesizer), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
static lean_object* _init_l_Lean_Parser_Term_doNested() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Term", 4, 4);
x_4 = lean_mk_string_unchecked("doNested", 8, 8);
lean_inc(x_4);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_box(1);
x_7 = lean_box(0);
x_8 = lean_unbox(x_6);
x_9 = lean_unbox(x_7);
lean_inc(x_5);
x_10 = l_Lean_Parser_mkAntiquot(x_4, x_5, x_8, x_9);
lean_dec(x_4);
x_11 = lean_unsigned_to_nat(1024u);
x_12 = lean_mk_string_unchecked("do ", 3, 3);
x_13 = l_Lean_Parser_symbol(x_12);
lean_dec(x_12);
x_14 = l_Lean_Parser_Term_doSeq;
x_15 = l_Lean_Parser_andthen(x_13, x_14);
lean_inc(x_5);
x_16 = l_Lean_Parser_leadingNode(x_5, x_11, x_15);
x_17 = l_Lean_Parser_withAntiquot(x_10, x_16);
x_18 = l_Lean_Parser_withCache(x_5, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doNested__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = lean_mk_string_unchecked("doElem", 6, 6);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Term", 4, 4);
x_7 = lean_mk_string_unchecked("doNested", 8, 8);
x_8 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_7);
x_9 = l_Lean_Parser_Term_doNested;
x_10 = lean_unsigned_to_nat(1000u);
x_11 = l_Lean_Parser_addBuiltinLeadingParser(x_3, x_8, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doNested_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Term", 4, 4);
x_5 = lean_mk_string_unchecked("doNested", 8, 8);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(224u);
x_8 = lean_unsigned_to_nat(25u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(225u);
x_11 = lean_unsigned_to_nat(16u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_11);
x_14 = lean_unsigned_to_nat(29u);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_unsigned_to_nat(37u);
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
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doNested_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("Parser", 6, 6);
x_8 = lean_mk_string_unchecked("Term", 4, 4);
x_9 = lean_mk_string_unchecked("doNested", 8, 8);
lean_inc(x_9);
x_10 = l_Lean_Name_mkStr4(x_6, x_7, x_8, x_9);
x_11 = lean_box(1);
x_12 = lean_box(0);
lean_inc(x_10);
x_13 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(x_13, 0, x_9);
lean_closure_set(x_13, 1, x_10);
lean_closure_set(x_13, 2, x_11);
lean_closure_set(x_13, 3, x_12);
x_14 = lean_unsigned_to_nat(1024u);
x_15 = lean_mk_string_unchecked("do ", 3, 3);
x_16 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter), 6, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doSeq_formatter), 5, 0);
x_18 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_18, 0, x_16);
lean_closure_set(x_18, 1, x_17);
x_19 = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(x_19, 0, x_10);
lean_closure_set(x_19, 1, x_14);
lean_closure_set(x_19, 2, x_18);
x_20 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_13, x_19, x_1, x_2, x_3, x_4, x_5);
return x_20;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doNested_formatter__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_formatterAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("doNested", 8, 8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("formatter", 9, 9);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doNested_formatter), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_doNested_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("Parser", 6, 6);
x_8 = lean_mk_string_unchecked("Term", 4, 4);
x_9 = lean_mk_string_unchecked("doNested", 8, 8);
lean_inc(x_9);
x_10 = l_Lean_Name_mkStr4(x_6, x_7, x_8, x_9);
x_11 = lean_box(1);
x_12 = lean_box(0);
lean_inc(x_10);
x_13 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(x_13, 0, x_9);
lean_closure_set(x_13, 1, x_10);
lean_closure_set(x_13, 2, x_11);
lean_closure_set(x_13, 3, x_12);
x_14 = lean_unsigned_to_nat(1024u);
x_15 = lean_mk_string_unchecked("do ", 3, 3);
x_16 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___boxed), 6, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doSeq_parenthesizer), 5, 0);
x_18 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_18, 0, x_16);
lean_closure_set(x_18, 1, x_17);
x_19 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer), 8, 3);
lean_closure_set(x_19, 0, x_10);
lean_closure_set(x_19, 1, x_14);
lean_closure_set(x_19, 2, x_18);
x_20 = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(x_13, x_19, x_1, x_2, x_3, x_4, x_5);
return x_20;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_doNested_parenthesizer__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("doNested", 8, 8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("parenthesizer", 13, 13);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doNested_parenthesizer), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
static lean_object* _init_l_Lean_Parser_Term_do() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Term", 4, 4);
x_4 = lean_mk_string_unchecked("do", 2, 2);
lean_inc(x_4);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_box(1);
x_7 = lean_box(0);
x_8 = lean_unbox(x_6);
x_9 = lean_unbox(x_7);
lean_inc(x_5);
x_10 = l_Lean_Parser_mkAntiquot(x_4, x_5, x_8, x_9);
lean_dec(x_4);
x_11 = lean_unsigned_to_nat(1023u);
x_12 = l_Lean_Parser_skip;
x_13 = lean_mk_string_unchecked("do ", 3, 3);
x_14 = l_Lean_Parser_symbol(x_13);
lean_dec(x_13);
x_15 = l_Lean_Parser_Term_doSeq;
x_16 = l_Lean_Parser_andthen(x_14, x_15);
x_17 = l_Lean_Parser_andthen(x_12, x_16);
lean_inc(x_5);
x_18 = l_Lean_Parser_leadingNode(x_5, x_11, x_17);
x_19 = l_Lean_Parser_withAntiquot(x_10, x_18);
x_20 = l_Lean_Parser_withCache(x_5, x_19);
return x_20;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_do__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = lean_mk_string_unchecked("term", 4, 4);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Term", 4, 4);
x_7 = lean_mk_string_unchecked("do", 2, 2);
x_8 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_7);
x_9 = l_Lean_Parser_Term_do;
x_10 = lean_unsigned_to_nat(1000u);
x_11 = l_Lean_Parser_addBuiltinLeadingParser(x_3, x_8, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_do_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Term", 4, 4);
x_5 = lean_mk_string_unchecked("do", 2, 2);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(227u);
x_8 = lean_unsigned_to_nat(23u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(228u);
x_11 = lean_unsigned_to_nat(36u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_11);
x_14 = lean_unsigned_to_nat(27u);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_unsigned_to_nat(31u);
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
LEAN_EXPORT lean_object* l_Lean_Parser_Term_do_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("Parser", 6, 6);
x_8 = lean_mk_string_unchecked("Term", 4, 4);
x_9 = lean_mk_string_unchecked("do", 2, 2);
lean_inc(x_9);
x_10 = l_Lean_Name_mkStr4(x_6, x_7, x_8, x_9);
x_11 = lean_box(1);
x_12 = lean_box(0);
lean_inc(x_10);
x_13 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(x_13, 0, x_9);
lean_closure_set(x_13, 1, x_10);
lean_closure_set(x_13, 2, x_11);
lean_closure_set(x_13, 3, x_12);
x_14 = lean_unsigned_to_nat(1023u);
x_15 = lean_alloc_closure((void*)(l_Lean_ppAllowUngrouped_formatter___boxed), 5, 0);
x_16 = lean_mk_string_unchecked("do ", 3, 3);
x_17 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter), 6, 1);
lean_closure_set(x_17, 0, x_16);
x_18 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doSeq_formatter), 5, 0);
x_19 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_19, 0, x_17);
lean_closure_set(x_19, 1, x_18);
x_20 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_20, 0, x_15);
lean_closure_set(x_20, 1, x_19);
x_21 = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(x_21, 0, x_10);
lean_closure_set(x_21, 1, x_14);
lean_closure_set(x_21, 2, x_20);
x_22 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_13, x_21, x_1, x_2, x_3, x_4, x_5);
return x_22;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_do_formatter__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_formatterAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("do", 2, 2);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("formatter", 9, 9);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Term_do_formatter), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_do_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doSeqItem_parenthesizer___lam__0___boxed), 5, 0);
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
x_8 = lean_mk_string_unchecked("Parser", 6, 6);
x_9 = lean_mk_string_unchecked("Term", 4, 4);
x_10 = lean_mk_string_unchecked("do", 2, 2);
lean_inc(x_10);
x_11 = l_Lean_Name_mkStr4(x_7, x_8, x_9, x_10);
x_12 = lean_box(1);
x_13 = lean_box(0);
lean_inc(x_11);
x_14 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(x_14, 0, x_10);
lean_closure_set(x_14, 1, x_11);
lean_closure_set(x_14, 2, x_12);
lean_closure_set(x_14, 3, x_13);
x_15 = lean_unsigned_to_nat(1023u);
x_16 = lean_mk_string_unchecked("do ", 3, 3);
x_17 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___boxed), 6, 1);
lean_closure_set(x_17, 0, x_16);
x_18 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doSeq_parenthesizer), 5, 0);
x_19 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_19, 0, x_17);
lean_closure_set(x_19, 1, x_18);
x_20 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_20, 0, x_6);
lean_closure_set(x_20, 1, x_19);
x_21 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer), 8, 3);
lean_closure_set(x_21, 0, x_11);
lean_closure_set(x_21, 1, x_15);
lean_closure_set(x_21, 2, x_20);
x_22 = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(x_14, x_21, x_1, x_2, x_3, x_4, x_5);
return x_22;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_do_parenthesizer__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("do", 2, 2);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("parenthesizer", 13, 13);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Term_do_parenthesizer), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
static lean_object* _init_l_Lean_Parser_Term_termUnless() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Term", 4, 4);
x_4 = lean_mk_string_unchecked("termUnless", 10, 10);
lean_inc(x_4);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_box(1);
x_7 = lean_box(0);
x_8 = lean_unbox(x_6);
x_9 = lean_unbox(x_7);
lean_inc(x_5);
x_10 = l_Lean_Parser_mkAntiquot(x_4, x_5, x_8, x_9);
lean_dec(x_4);
x_11 = lean_unsigned_to_nat(1024u);
x_12 = lean_mk_string_unchecked("unless ", 7, 7);
x_13 = l_Lean_Parser_symbol(x_12);
lean_dec(x_12);
x_14 = lean_mk_string_unchecked("do", 2, 2);
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Lean_Parser_termParser(x_15);
x_17 = l_Lean_Parser_withForbidden(x_14, x_16);
x_18 = lean_mk_string_unchecked(" do ", 4, 4);
x_19 = l_Lean_Parser_symbol(x_18);
lean_dec(x_18);
x_20 = l_Lean_Parser_Term_doSeq;
x_21 = l_Lean_Parser_andthen(x_19, x_20);
x_22 = l_Lean_Parser_andthen(x_17, x_21);
x_23 = l_Lean_Parser_andthen(x_13, x_22);
lean_inc(x_5);
x_24 = l_Lean_Parser_leadingNode(x_5, x_11, x_23);
x_25 = l_Lean_Parser_withAntiquot(x_10, x_24);
x_26 = l_Lean_Parser_withCache(x_5, x_25);
return x_26;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_termUnless__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = lean_mk_string_unchecked("term", 4, 4);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Term", 4, 4);
x_7 = lean_mk_string_unchecked("termUnless", 10, 10);
x_8 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_7);
x_9 = l_Lean_Parser_Term_termUnless;
x_10 = lean_unsigned_to_nat(1000u);
x_11 = l_Lean_Parser_addBuiltinLeadingParser(x_3, x_8, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_termUnless_docString__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Term", 4, 4);
x_5 = lean_mk_string_unchecked("termUnless", 10, 10);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_mk_string_unchecked("`unless e do s` is a nicer way to write `if !e do s`. ", 54, 54);
x_8 = l_Lean_addBuiltinDocString(x_6, x_7, x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_termUnless_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Term", 4, 4);
x_5 = lean_mk_string_unchecked("termUnless", 10, 10);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(236u);
x_8 = lean_unsigned_to_nat(23u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(237u);
x_11 = lean_unsigned_to_nat(63u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_11);
x_14 = lean_unsigned_to_nat(27u);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_unsigned_to_nat(37u);
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
LEAN_EXPORT lean_object* l_Lean_Parser_Term_termUnless_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doUnless_formatter___lam__0), 5, 0);
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
x_8 = lean_mk_string_unchecked("Parser", 6, 6);
x_9 = lean_mk_string_unchecked("Term", 4, 4);
x_10 = lean_mk_string_unchecked("termUnless", 10, 10);
lean_inc(x_10);
x_11 = l_Lean_Name_mkStr4(x_7, x_8, x_9, x_10);
x_12 = lean_box(1);
x_13 = lean_box(0);
lean_inc(x_11);
x_14 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(x_14, 0, x_10);
lean_closure_set(x_14, 1, x_11);
lean_closure_set(x_14, 2, x_12);
lean_closure_set(x_14, 3, x_13);
x_15 = lean_unsigned_to_nat(1024u);
x_16 = lean_mk_string_unchecked("unless ", 7, 7);
x_17 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter), 6, 1);
lean_closure_set(x_17, 0, x_16);
x_18 = lean_mk_string_unchecked(" do ", 4, 4);
x_19 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter), 6, 1);
lean_closure_set(x_19, 0, x_18);
x_20 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doSeq_formatter), 5, 0);
x_21 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_21, 0, x_19);
lean_closure_set(x_21, 1, x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_22, 0, x_6);
lean_closure_set(x_22, 1, x_21);
x_23 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_23, 0, x_17);
lean_closure_set(x_23, 1, x_22);
x_24 = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(x_24, 0, x_11);
lean_closure_set(x_24, 1, x_15);
lean_closure_set(x_24, 2, x_23);
x_25 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_14, x_24, x_1, x_2, x_3, x_4, x_5);
return x_25;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_termUnless_formatter__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_formatterAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("termUnless", 10, 10);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("formatter", 9, 9);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Term_termUnless_formatter), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_termUnless_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("Parser", 6, 6);
x_8 = lean_mk_string_unchecked("Term", 4, 4);
x_9 = lean_mk_string_unchecked("termUnless", 10, 10);
lean_inc(x_9);
x_10 = l_Lean_Name_mkStr4(x_6, x_7, x_8, x_9);
x_11 = lean_box(1);
x_12 = lean_box(0);
lean_inc(x_10);
x_13 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(x_13, 0, x_9);
lean_closure_set(x_13, 1, x_10);
lean_closure_set(x_13, 2, x_11);
lean_closure_set(x_13, 3, x_12);
x_14 = lean_unsigned_to_nat(1024u);
x_15 = lean_mk_string_unchecked("unless ", 7, 7);
x_16 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___boxed), 6, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = lean_mk_string_unchecked("do", 2, 2);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_alloc_closure((void*)(l_Lean_Parser_termParser_parenthesizer), 6, 1);
lean_closure_set(x_19, 0, x_18);
x_20 = lean_alloc_closure((void*)(l_Lean_Parser_withForbidden_parenthesizer___boxed), 7, 2);
lean_closure_set(x_20, 0, x_17);
lean_closure_set(x_20, 1, x_19);
x_21 = lean_mk_string_unchecked(" do ", 4, 4);
x_22 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___boxed), 6, 1);
lean_closure_set(x_22, 0, x_21);
x_23 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doSeq_parenthesizer), 5, 0);
x_24 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_24, 0, x_22);
lean_closure_set(x_24, 1, x_23);
x_25 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_25, 0, x_20);
lean_closure_set(x_25, 1, x_24);
x_26 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_26, 0, x_16);
lean_closure_set(x_26, 1, x_25);
x_27 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer), 8, 3);
lean_closure_set(x_27, 0, x_10);
lean_closure_set(x_27, 1, x_14);
lean_closure_set(x_27, 2, x_26);
x_28 = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(x_13, x_27, x_1, x_2, x_3, x_4, x_5);
return x_28;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_termUnless_parenthesizer__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("termUnless", 10, 10);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("parenthesizer", 13, 13);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Term_termUnless_parenthesizer), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
static lean_object* _init_l_Lean_Parser_Term_termFor() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Term", 4, 4);
x_4 = lean_mk_string_unchecked("termFor", 7, 7);
lean_inc(x_4);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_box(1);
x_7 = lean_box(0);
x_8 = lean_unbox(x_6);
x_9 = lean_unbox(x_7);
lean_inc(x_5);
x_10 = l_Lean_Parser_mkAntiquot(x_4, x_5, x_8, x_9);
lean_dec(x_4);
x_11 = lean_unsigned_to_nat(1024u);
x_12 = lean_mk_string_unchecked("for ", 4, 4);
x_13 = l_Lean_Parser_symbol(x_12);
lean_dec(x_12);
x_14 = l_Lean_Parser_Term_doForDecl;
x_15 = lean_mk_string_unchecked(", ", 2, 2);
x_16 = l_Lean_Parser_symbol(x_15);
x_17 = lean_unbox(x_7);
x_18 = l_Lean_Parser_sepBy1(x_14, x_15, x_16, x_17);
lean_dec(x_15);
x_19 = lean_mk_string_unchecked(" do ", 4, 4);
x_20 = l_Lean_Parser_symbol(x_19);
lean_dec(x_19);
x_21 = l_Lean_Parser_Term_doSeq;
x_22 = l_Lean_Parser_andthen(x_20, x_21);
x_23 = l_Lean_Parser_andthen(x_18, x_22);
x_24 = l_Lean_Parser_andthen(x_13, x_23);
lean_inc(x_5);
x_25 = l_Lean_Parser_leadingNode(x_5, x_11, x_24);
x_26 = l_Lean_Parser_withAntiquot(x_10, x_25);
x_27 = l_Lean_Parser_withCache(x_5, x_26);
return x_27;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_termFor__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = lean_mk_string_unchecked("term", 4, 4);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Term", 4, 4);
x_7 = lean_mk_string_unchecked("termFor", 7, 7);
x_8 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_7);
x_9 = l_Lean_Parser_Term_termFor;
x_10 = lean_unsigned_to_nat(1000u);
x_11 = l_Lean_Parser_addBuiltinLeadingParser(x_3, x_8, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_termFor_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Term", 4, 4);
x_5 = lean_mk_string_unchecked("termFor", 7, 7);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(238u);
x_8 = lean_unsigned_to_nat(23u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(239u);
x_11 = lean_unsigned_to_nat(52u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_11);
x_14 = lean_unsigned_to_nat(27u);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_unsigned_to_nat(34u);
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
LEAN_EXPORT lean_object* l_Lean_Parser_Term_termFor_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("Parser", 6, 6);
x_8 = lean_mk_string_unchecked("Term", 4, 4);
x_9 = lean_mk_string_unchecked("termFor", 7, 7);
lean_inc(x_9);
x_10 = l_Lean_Name_mkStr4(x_6, x_7, x_8, x_9);
x_11 = lean_box(1);
x_12 = lean_box(0);
lean_inc(x_10);
x_13 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(x_13, 0, x_9);
lean_closure_set(x_13, 1, x_10);
lean_closure_set(x_13, 2, x_11);
lean_closure_set(x_13, 3, x_12);
x_14 = lean_unsigned_to_nat(1024u);
x_15 = lean_mk_string_unchecked("for ", 4, 4);
x_16 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter), 6, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doForDecl_formatter), 5, 0);
x_18 = lean_mk_string_unchecked(", ", 2, 2);
lean_inc(x_18);
x_19 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter), 6, 1);
lean_closure_set(x_19, 0, x_18);
x_20 = lean_alloc_closure((void*)(l_Lean_Parser_sepBy1_formatter___boxed), 9, 4);
lean_closure_set(x_20, 0, x_17);
lean_closure_set(x_20, 1, x_18);
lean_closure_set(x_20, 2, x_19);
lean_closure_set(x_20, 3, x_12);
x_21 = lean_mk_string_unchecked(" do ", 4, 4);
x_22 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter), 6, 1);
lean_closure_set(x_22, 0, x_21);
x_23 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doSeq_formatter), 5, 0);
x_24 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_24, 0, x_22);
lean_closure_set(x_24, 1, x_23);
x_25 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_25, 0, x_20);
lean_closure_set(x_25, 1, x_24);
x_26 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_26, 0, x_16);
lean_closure_set(x_26, 1, x_25);
x_27 = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(x_27, 0, x_10);
lean_closure_set(x_27, 1, x_14);
lean_closure_set(x_27, 2, x_26);
x_28 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_13, x_27, x_1, x_2, x_3, x_4, x_5);
return x_28;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_termFor_formatter__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_formatterAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("termFor", 7, 7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("formatter", 9, 9);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Term_termFor_formatter), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_termFor_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("Parser", 6, 6);
x_8 = lean_mk_string_unchecked("Term", 4, 4);
x_9 = lean_mk_string_unchecked("termFor", 7, 7);
lean_inc(x_9);
x_10 = l_Lean_Name_mkStr4(x_6, x_7, x_8, x_9);
x_11 = lean_box(1);
x_12 = lean_box(0);
lean_inc(x_10);
x_13 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(x_13, 0, x_9);
lean_closure_set(x_13, 1, x_10);
lean_closure_set(x_13, 2, x_11);
lean_closure_set(x_13, 3, x_12);
x_14 = lean_unsigned_to_nat(1024u);
x_15 = lean_mk_string_unchecked("for ", 4, 4);
x_16 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___boxed), 6, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doForDecl_parenthesizer), 5, 0);
x_18 = lean_mk_string_unchecked(", ", 2, 2);
lean_inc(x_18);
x_19 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___boxed), 6, 1);
lean_closure_set(x_19, 0, x_18);
x_20 = lean_alloc_closure((void*)(l_Lean_Parser_sepBy1_parenthesizer___boxed), 9, 4);
lean_closure_set(x_20, 0, x_17);
lean_closure_set(x_20, 1, x_18);
lean_closure_set(x_20, 2, x_19);
lean_closure_set(x_20, 3, x_12);
x_21 = lean_mk_string_unchecked(" do ", 4, 4);
x_22 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___boxed), 6, 1);
lean_closure_set(x_22, 0, x_21);
x_23 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doSeq_parenthesizer), 5, 0);
x_24 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_24, 0, x_22);
lean_closure_set(x_24, 1, x_23);
x_25 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_25, 0, x_20);
lean_closure_set(x_25, 1, x_24);
x_26 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_26, 0, x_16);
lean_closure_set(x_26, 1, x_25);
x_27 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer), 8, 3);
lean_closure_set(x_27, 0, x_10);
lean_closure_set(x_27, 1, x_14);
lean_closure_set(x_27, 2, x_26);
x_28 = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(x_13, x_27, x_1, x_2, x_3, x_4, x_5);
return x_28;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_termFor_parenthesizer__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("termFor", 7, 7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("parenthesizer", 13, 13);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Term_termFor_parenthesizer), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
static lean_object* _init_l_Lean_Parser_Term_termTry() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Term", 4, 4);
x_4 = lean_mk_string_unchecked("termTry", 7, 7);
lean_inc(x_4);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_box(1);
x_7 = lean_box(0);
x_8 = lean_unbox(x_6);
x_9 = lean_unbox(x_7);
lean_inc(x_5);
x_10 = l_Lean_Parser_mkAntiquot(x_4, x_5, x_8, x_9);
lean_dec(x_4);
x_11 = lean_unsigned_to_nat(1024u);
x_12 = lean_mk_string_unchecked("try ", 4, 4);
x_13 = l_Lean_Parser_symbol(x_12);
lean_dec(x_12);
x_14 = l_Lean_Parser_Term_doSeq;
x_15 = l_Lean_Parser_Term_doCatch;
x_16 = l_Lean_Parser_Term_doCatchMatch;
x_17 = l_Lean_Parser_orelse(x_15, x_16);
x_18 = l_Lean_Parser_many(x_17);
x_19 = l_Lean_Parser_Term_doFinally;
x_20 = l_Lean_Parser_optional(x_19);
x_21 = l_Lean_Parser_andthen(x_18, x_20);
x_22 = l_Lean_Parser_andthen(x_14, x_21);
x_23 = l_Lean_Parser_andthen(x_13, x_22);
lean_inc(x_5);
x_24 = l_Lean_Parser_leadingNode(x_5, x_11, x_23);
x_25 = l_Lean_Parser_withAntiquot(x_10, x_24);
x_26 = l_Lean_Parser_withCache(x_5, x_25);
return x_26;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_termTry__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = lean_mk_string_unchecked("term", 4, 4);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Term", 4, 4);
x_7 = lean_mk_string_unchecked("termTry", 7, 7);
x_8 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_7);
x_9 = l_Lean_Parser_Term_termTry;
x_10 = lean_unsigned_to_nat(1000u);
x_11 = l_Lean_Parser_addBuiltinLeadingParser(x_3, x_8, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_termTry_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Term", 4, 4);
x_5 = lean_mk_string_unchecked("termTry", 7, 7);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(240u);
x_8 = lean_unsigned_to_nat(23u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(241u);
x_11 = lean_unsigned_to_nat(74u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_11);
x_14 = lean_unsigned_to_nat(27u);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_unsigned_to_nat(34u);
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
LEAN_EXPORT lean_object* l_Lean_Parser_Term_termTry_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("Parser", 6, 6);
x_8 = lean_mk_string_unchecked("Term", 4, 4);
x_9 = lean_mk_string_unchecked("termTry", 7, 7);
lean_inc(x_9);
x_10 = l_Lean_Name_mkStr4(x_6, x_7, x_8, x_9);
x_11 = lean_box(1);
x_12 = lean_box(0);
lean_inc(x_10);
x_13 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(x_13, 0, x_9);
lean_closure_set(x_13, 1, x_10);
lean_closure_set(x_13, 2, x_11);
lean_closure_set(x_13, 3, x_12);
x_14 = lean_unsigned_to_nat(1024u);
x_15 = lean_mk_string_unchecked("try ", 4, 4);
x_16 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter), 6, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doSeq_formatter), 5, 0);
x_18 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doCatch_formatter), 5, 0);
x_19 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doCatchMatch_formatter), 5, 0);
x_20 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter), 7, 2);
lean_closure_set(x_20, 0, x_18);
lean_closure_set(x_20, 1, x_19);
x_21 = lean_alloc_closure((void*)(l_Lean_Parser_many_formatter), 6, 1);
lean_closure_set(x_21, 0, x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doFinally_formatter), 5, 0);
x_23 = lean_alloc_closure((void*)(l_Lean_Parser_optional_formatter), 6, 1);
lean_closure_set(x_23, 0, x_22);
x_24 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_24, 0, x_21);
lean_closure_set(x_24, 1, x_23);
x_25 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_25, 0, x_17);
lean_closure_set(x_25, 1, x_24);
x_26 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_26, 0, x_16);
lean_closure_set(x_26, 1, x_25);
x_27 = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(x_27, 0, x_10);
lean_closure_set(x_27, 1, x_14);
lean_closure_set(x_27, 2, x_26);
x_28 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_13, x_27, x_1, x_2, x_3, x_4, x_5);
return x_28;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_termTry_formatter__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_formatterAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("termTry", 7, 7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("formatter", 9, 9);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Term_termTry_formatter), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_termTry_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("Parser", 6, 6);
x_8 = lean_mk_string_unchecked("Term", 4, 4);
x_9 = lean_mk_string_unchecked("termTry", 7, 7);
lean_inc(x_9);
x_10 = l_Lean_Name_mkStr4(x_6, x_7, x_8, x_9);
x_11 = lean_box(1);
x_12 = lean_box(0);
lean_inc(x_10);
x_13 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(x_13, 0, x_9);
lean_closure_set(x_13, 1, x_10);
lean_closure_set(x_13, 2, x_11);
lean_closure_set(x_13, 3, x_12);
x_14 = lean_unsigned_to_nat(1024u);
x_15 = lean_mk_string_unchecked("try ", 4, 4);
x_16 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___boxed), 6, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doSeq_parenthesizer), 5, 0);
x_18 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doCatch_parenthesizer), 5, 0);
x_19 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doCatchMatch_parenthesizer), 5, 0);
x_20 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer), 7, 2);
lean_closure_set(x_20, 0, x_18);
lean_closure_set(x_20, 1, x_19);
x_21 = lean_alloc_closure((void*)(l_Lean_Parser_many_parenthesizer), 6, 1);
lean_closure_set(x_21, 0, x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doFinally_parenthesizer), 5, 0);
x_23 = lean_alloc_closure((void*)(l_Lean_Parser_optional_parenthesizer), 6, 1);
lean_closure_set(x_23, 0, x_22);
x_24 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_24, 0, x_21);
lean_closure_set(x_24, 1, x_23);
x_25 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_25, 0, x_17);
lean_closure_set(x_25, 1, x_24);
x_26 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_26, 0, x_16);
lean_closure_set(x_26, 1, x_25);
x_27 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer), 8, 3);
lean_closure_set(x_27, 0, x_10);
lean_closure_set(x_27, 1, x_14);
lean_closure_set(x_27, 2, x_26);
x_28 = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(x_13, x_27, x_1, x_2, x_3, x_4, x_5);
return x_28;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_termTry_parenthesizer__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("termTry", 7, 7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("parenthesizer", 13, 13);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Term_termTry_parenthesizer), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
static lean_object* _init_l_Lean_Parser_Term_termReturn() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Term", 4, 4);
x_4 = lean_mk_string_unchecked("termReturn", 10, 10);
lean_inc(x_4);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_box(1);
x_7 = lean_box(0);
x_8 = lean_unbox(x_6);
x_9 = lean_unbox(x_7);
lean_inc(x_5);
x_10 = l_Lean_Parser_mkAntiquot(x_4, x_5, x_8, x_9);
lean_dec(x_4);
x_11 = lean_unsigned_to_nat(1022u);
x_12 = lean_mk_string_unchecked("return", 6, 6);
x_13 = l_Lean_Parser_symbol(x_12);
lean_dec(x_12);
x_14 = l_Lean_Parser_skip;
x_15 = lean_mk_string_unchecked("checkLineEq", 11, 11);
x_16 = l_Lean_Parser_checkLineEq(x_15);
x_17 = lean_unsigned_to_nat(0u);
x_18 = l_Lean_Parser_termParser(x_17);
x_19 = l_Lean_Parser_andthen(x_16, x_18);
x_20 = l_Lean_Parser_andthen(x_14, x_19);
x_21 = l_Lean_Parser_optional(x_20);
x_22 = l_Lean_Parser_andthen(x_13, x_21);
x_23 = l_Lean_Parser_withPosition(x_22);
lean_inc(x_5);
x_24 = l_Lean_Parser_leadingNode(x_5, x_11, x_23);
x_25 = l_Lean_Parser_withAntiquot(x_10, x_24);
x_26 = l_Lean_Parser_withCache(x_5, x_25);
return x_26;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_termReturn__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = lean_mk_string_unchecked("term", 4, 4);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Term", 4, 4);
x_7 = lean_mk_string_unchecked("termReturn", 10, 10);
x_8 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_7);
x_9 = l_Lean_Parser_Term_termReturn;
x_10 = lean_unsigned_to_nat(1000u);
x_11 = l_Lean_Parser_addBuiltinLeadingParser(x_3, x_8, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_termReturn_docString__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Term", 4, 4);
x_5 = lean_mk_string_unchecked("termReturn", 10, 10);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_mk_string_unchecked("`return` used outside of `do` blocks creates an implicit block around it\nand thus is equivalent to `pure e`, but helps with avoiding parentheses.\n", 146, 146);
x_8 = l_Lean_addBuiltinDocString(x_6, x_7, x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_termReturn_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Term", 4, 4);
x_5 = lean_mk_string_unchecked("termReturn", 10, 10);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(246u);
x_8 = lean_unsigned_to_nat(23u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(247u);
x_11 = lean_unsigned_to_nat(76u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_11);
x_14 = lean_unsigned_to_nat(27u);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_unsigned_to_nat(37u);
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
LEAN_EXPORT lean_object* l_Lean_Parser_Term_termReturn_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doIdDecl_formatter___lam__0___boxed), 5, 0);
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
x_8 = lean_mk_string_unchecked("Parser", 6, 6);
x_9 = lean_mk_string_unchecked("Term", 4, 4);
x_10 = lean_mk_string_unchecked("termReturn", 10, 10);
lean_inc(x_10);
x_11 = l_Lean_Name_mkStr4(x_7, x_8, x_9, x_10);
x_12 = lean_box(1);
x_13 = lean_box(0);
lean_inc(x_11);
x_14 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(x_14, 0, x_10);
lean_closure_set(x_14, 1, x_11);
lean_closure_set(x_14, 2, x_12);
lean_closure_set(x_14, 3, x_13);
x_15 = lean_unsigned_to_nat(1022u);
x_16 = lean_mk_string_unchecked("return", 6, 6);
x_17 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter), 6, 1);
lean_closure_set(x_17, 0, x_16);
x_18 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkLineEq_formatter___boxed), 5, 0);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_alloc_closure((void*)(l_Lean_Parser_termParser_formatter___boxed), 6, 1);
lean_closure_set(x_20, 0, x_19);
x_21 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_21, 0, x_18);
lean_closure_set(x_21, 1, x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_22, 0, x_6);
lean_closure_set(x_22, 1, x_21);
x_23 = lean_alloc_closure((void*)(l_Lean_Parser_optional_formatter), 6, 1);
lean_closure_set(x_23, 0, x_22);
x_24 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_24, 0, x_17);
lean_closure_set(x_24, 1, x_23);
x_25 = lean_alloc_closure((void*)(l_Lean_Parser_withPosition_formatter), 6, 1);
lean_closure_set(x_25, 0, x_24);
x_26 = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(x_26, 0, x_11);
lean_closure_set(x_26, 1, x_15);
lean_closure_set(x_26, 2, x_25);
x_27 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_14, x_26, x_1, x_2, x_3, x_4, x_5);
return x_27;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_termReturn_formatter__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_formatterAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("termReturn", 10, 10);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("formatter", 9, 9);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Term_termReturn_formatter), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Term_termReturn_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_Term_doSeqItem_parenthesizer___lam__0___boxed), 5, 0);
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
x_8 = lean_mk_string_unchecked("Parser", 6, 6);
x_9 = lean_mk_string_unchecked("Term", 4, 4);
x_10 = lean_mk_string_unchecked("termReturn", 10, 10);
lean_inc(x_10);
x_11 = l_Lean_Name_mkStr4(x_7, x_8, x_9, x_10);
x_12 = lean_box(1);
x_13 = lean_box(0);
lean_inc(x_11);
x_14 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(x_14, 0, x_10);
lean_closure_set(x_14, 1, x_11);
lean_closure_set(x_14, 2, x_12);
lean_closure_set(x_14, 3, x_13);
x_15 = lean_unsigned_to_nat(1022u);
x_16 = lean_mk_string_unchecked("return", 6, 6);
x_17 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___boxed), 6, 1);
lean_closure_set(x_17, 0, x_16);
x_18 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkLineEq_parenthesizer___boxed), 5, 0);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_alloc_closure((void*)(l_Lean_Parser_termParser_parenthesizer), 6, 1);
lean_closure_set(x_20, 0, x_19);
x_21 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_21, 0, x_18);
lean_closure_set(x_21, 1, x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_22, 0, x_6);
lean_closure_set(x_22, 1, x_21);
x_23 = lean_alloc_closure((void*)(l_Lean_Parser_optional_parenthesizer), 6, 1);
lean_closure_set(x_23, 0, x_22);
x_24 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_24, 0, x_17);
lean_closure_set(x_24, 1, x_23);
x_25 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_withPosition_parenthesizer), 6, 1);
lean_closure_set(x_25, 0, x_24);
x_26 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer), 8, 3);
lean_closure_set(x_26, 0, x_11);
lean_closure_set(x_26, 1, x_15);
lean_closure_set(x_26, 2, x_25);
x_27 = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(x_14, x_26, x_1, x_2, x_3, x_4, x_5);
return x_27;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Term_termReturn_parenthesizer__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Term", 4, 4);
x_6 = lean_mk_string_unchecked("termReturn", 10, 10);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("parenthesizer", 13, 13);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Term_termReturn_parenthesizer), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
lean_object* initialize_Lean_Parser_Term(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Parser_Do(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Parser_Term(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
if (builtin) {res = l_Lean_Parser_initFn____x40_Lean_Parser_Do___hyg_4_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l_Lean_Parser_initFn____x40_Lean_Parser_Do___hyg_42_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_Term_leftArrow = _init_l_Lean_Parser_Term_leftArrow();
lean_mark_persistent(l_Lean_Parser_Term_leftArrow);
l_Lean_Parser_Term_liftMethod = _init_l_Lean_Parser_Term_liftMethod();
lean_mark_persistent(l_Lean_Parser_Term_liftMethod);
if (builtin) {res = l___regBuiltin_Lean_Parser_Term_liftMethod__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_liftMethod_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_liftMethod_formatter__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_liftMethod_parenthesizer__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_Term_doSeqItem = _init_l_Lean_Parser_Term_doSeqItem();
lean_mark_persistent(l_Lean_Parser_Term_doSeqItem);
l_Lean_Parser_Term_doSeqIndent = _init_l_Lean_Parser_Term_doSeqIndent();
lean_mark_persistent(l_Lean_Parser_Term_doSeqIndent);
l_Lean_Parser_Term_doSeqBracketed = _init_l_Lean_Parser_Term_doSeqBracketed();
lean_mark_persistent(l_Lean_Parser_Term_doSeqBracketed);
if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doSeq_docString__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_Term_doSeq = _init_l_Lean_Parser_Term_doSeq();
lean_mark_persistent(l_Lean_Parser_Term_doSeq);
l_Lean_Parser_Term_termBeforeDo = _init_l_Lean_Parser_Term_termBeforeDo();
lean_mark_persistent(l_Lean_Parser_Term_termBeforeDo);
if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doSeqItem_formatter__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doSeqBracketed_formatter__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doSeqIndent_formatter__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doSeqItem_parenthesizer__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doSeqBracketed_parenthesizer__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doSeqIndent_parenthesizer__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l_Lean_Parser_Term_initFn____x40_Lean_Parser_Do___hyg_228_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_Term_notFollowedByRedefinedTermToken = _init_l_Lean_Parser_Term_notFollowedByRedefinedTermToken();
lean_mark_persistent(l_Lean_Parser_Term_notFollowedByRedefinedTermToken);
l_Lean_Parser_Term_doLet = _init_l_Lean_Parser_Term_doLet();
lean_mark_persistent(l_Lean_Parser_Term_doLet);
if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doLet__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doLet_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doLet_formatter__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doLet_parenthesizer__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_Term_doLetElse = _init_l_Lean_Parser_Term_doLetElse();
lean_mark_persistent(l_Lean_Parser_Term_doLetElse);
if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doLetElse__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doLetElse_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doLetElse_formatter__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doLetElse_parenthesizer__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_Term_doLetExpr = _init_l_Lean_Parser_Term_doLetExpr();
lean_mark_persistent(l_Lean_Parser_Term_doLetExpr);
if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doLetExpr__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doLetExpr_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doLetExpr_formatter__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doLetExpr_parenthesizer__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_Term_doLetMetaExpr = _init_l_Lean_Parser_Term_doLetMetaExpr();
lean_mark_persistent(l_Lean_Parser_Term_doLetMetaExpr);
if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doLetMetaExpr__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doLetMetaExpr_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doLetMetaExpr_formatter__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doLetMetaExpr_parenthesizer__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_Term_doLetRec = _init_l_Lean_Parser_Term_doLetRec();
lean_mark_persistent(l_Lean_Parser_Term_doLetRec);
if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doLetRec__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doLetRec_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doLetRec_formatter__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doLetRec_parenthesizer__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_Term_doIdDecl = _init_l_Lean_Parser_Term_doIdDecl();
lean_mark_persistent(l_Lean_Parser_Term_doIdDecl);
l_Lean_Parser_Term_doPatDecl = _init_l_Lean_Parser_Term_doPatDecl();
lean_mark_persistent(l_Lean_Parser_Term_doPatDecl);
l_Lean_Parser_Term_doLetArrow = _init_l_Lean_Parser_Term_doLetArrow();
lean_mark_persistent(l_Lean_Parser_Term_doLetArrow);
if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doLetArrow__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doLetArrow_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doIdDecl_formatter__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doPatDecl_formatter__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doLetArrow_formatter__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doIdDecl_parenthesizer__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doPatDecl_parenthesizer__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doLetArrow_parenthesizer__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_Term_letIdDeclNoBinders = _init_l_Lean_Parser_Term_letIdDeclNoBinders();
lean_mark_persistent(l_Lean_Parser_Term_letIdDeclNoBinders);
l_Lean_Parser_Term_doReassign = _init_l_Lean_Parser_Term_doReassign();
lean_mark_persistent(l_Lean_Parser_Term_doReassign);
if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doReassign__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doReassign_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_letIdDeclNoBinders_formatter__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doReassign_formatter__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_letIdDeclNoBinders_parenthesizer__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doReassign_parenthesizer__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_Term_doReassignArrow = _init_l_Lean_Parser_Term_doReassignArrow();
lean_mark_persistent(l_Lean_Parser_Term_doReassignArrow);
if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doReassignArrow__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doReassignArrow_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doReassignArrow_formatter__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doReassignArrow_parenthesizer__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_Term_doHave = _init_l_Lean_Parser_Term_doHave();
lean_mark_persistent(l_Lean_Parser_Term_doHave);
if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doHave__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doHave_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doHave_formatter__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doHave_parenthesizer__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_Term_elseIf = _init_l_Lean_Parser_Term_elseIf();
lean_mark_persistent(l_Lean_Parser_Term_elseIf);
l_Lean_Parser_Term_doIfLetPure = _init_l_Lean_Parser_Term_doIfLetPure();
lean_mark_persistent(l_Lean_Parser_Term_doIfLetPure);
l_Lean_Parser_Term_doIfLetBind = _init_l_Lean_Parser_Term_doIfLetBind();
lean_mark_persistent(l_Lean_Parser_Term_doIfLetBind);
l_Lean_Parser_Term_doIfLet = _init_l_Lean_Parser_Term_doIfLet();
lean_mark_persistent(l_Lean_Parser_Term_doIfLet);
l_Lean_Parser_Term_doIfProp = _init_l_Lean_Parser_Term_doIfProp();
lean_mark_persistent(l_Lean_Parser_Term_doIfProp);
l_Lean_Parser_Term_doIfCond = _init_l_Lean_Parser_Term_doIfCond();
lean_mark_persistent(l_Lean_Parser_Term_doIfCond);
l_Lean_Parser_Term_doIf = _init_l_Lean_Parser_Term_doIf();
lean_mark_persistent(l_Lean_Parser_Term_doIf);
if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doIf__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doIf_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doIfLetPure_formatter__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doIfLetBind_formatter__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doIfLet_formatter__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doIfProp_formatter__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doIf_formatter__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doIfLetPure_parenthesizer__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doIfLetBind_parenthesizer__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doIfLet_parenthesizer__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doIfProp_parenthesizer__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doIf_parenthesizer__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_Term_doUnless = _init_l_Lean_Parser_Term_doUnless();
lean_mark_persistent(l_Lean_Parser_Term_doUnless);
if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doUnless__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doUnless_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doUnless_formatter__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doUnless_parenthesizer__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_Term_doForDecl = _init_l_Lean_Parser_Term_doForDecl();
lean_mark_persistent(l_Lean_Parser_Term_doForDecl);
l_Lean_Parser_Term_doFor = _init_l_Lean_Parser_Term_doFor();
lean_mark_persistent(l_Lean_Parser_Term_doFor);
if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doFor__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doFor_docString__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doFor_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doForDecl_formatter__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doFor_formatter__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doForDecl_parenthesizer__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doFor_parenthesizer__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_Term_doMatchAlts = _init_l_Lean_Parser_Term_doMatchAlts();
lean_mark_persistent(l_Lean_Parser_Term_doMatchAlts);
l_Lean_Parser_Term_doMatch = _init_l_Lean_Parser_Term_doMatch();
lean_mark_persistent(l_Lean_Parser_Term_doMatch);
if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doMatch__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doMatch_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doMatch_formatter__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doMatch_parenthesizer__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_Term_doMatchExprAlts = _init_l_Lean_Parser_Term_doMatchExprAlts();
lean_mark_persistent(l_Lean_Parser_Term_doMatchExprAlts);
l_Lean_Parser_Term_optMetaFalse = _init_l_Lean_Parser_Term_optMetaFalse();
lean_mark_persistent(l_Lean_Parser_Term_optMetaFalse);
l_Lean_Parser_Term_doMatchExpr = _init_l_Lean_Parser_Term_doMatchExpr();
lean_mark_persistent(l_Lean_Parser_Term_doMatchExpr);
if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doMatchExpr__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doMatchExpr_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doMatchExpr_formatter__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doMatchExpr_parenthesizer__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_Term_doCatch = _init_l_Lean_Parser_Term_doCatch();
lean_mark_persistent(l_Lean_Parser_Term_doCatch);
l_Lean_Parser_Term_doCatchMatch = _init_l_Lean_Parser_Term_doCatchMatch();
lean_mark_persistent(l_Lean_Parser_Term_doCatchMatch);
l_Lean_Parser_Term_doFinally = _init_l_Lean_Parser_Term_doFinally();
lean_mark_persistent(l_Lean_Parser_Term_doFinally);
l_Lean_Parser_Term_doTry = _init_l_Lean_Parser_Term_doTry();
lean_mark_persistent(l_Lean_Parser_Term_doTry);
if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doTry__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doTry_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doCatch_formatter__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doCatchMatch_formatter__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doFinally_formatter__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doTry_formatter__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doCatch_parenthesizer__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doCatchMatch_parenthesizer__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doFinally_parenthesizer__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doTry_parenthesizer__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_Term_doBreak = _init_l_Lean_Parser_Term_doBreak();
lean_mark_persistent(l_Lean_Parser_Term_doBreak);
if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doBreak__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doBreak_docString__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doBreak_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doBreak_formatter__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doBreak_parenthesizer__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_Term_doContinue = _init_l_Lean_Parser_Term_doContinue();
lean_mark_persistent(l_Lean_Parser_Term_doContinue);
if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doContinue__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doContinue_docString__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doContinue_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doContinue_formatter__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doContinue_parenthesizer__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_Term_doReturn = _init_l_Lean_Parser_Term_doReturn();
lean_mark_persistent(l_Lean_Parser_Term_doReturn);
if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doReturn__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doReturn_docString__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doReturn_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doReturn_formatter__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doReturn_parenthesizer__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_Term_doDbgTrace = _init_l_Lean_Parser_Term_doDbgTrace();
lean_mark_persistent(l_Lean_Parser_Term_doDbgTrace);
if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doDbgTrace__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doDbgTrace_docString__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doDbgTrace_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doDbgTrace_formatter__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doDbgTrace_parenthesizer__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_Term_doAssert = _init_l_Lean_Parser_Term_doAssert();
lean_mark_persistent(l_Lean_Parser_Term_doAssert);
if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doAssert__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doAssert_docString__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doAssert_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doAssert_formatter__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doAssert_parenthesizer__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_Term_doDebugAssert = _init_l_Lean_Parser_Term_doDebugAssert();
lean_mark_persistent(l_Lean_Parser_Term_doDebugAssert);
if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doDebugAssert__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doDebugAssert_docString__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doDebugAssert_formatter__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doDebugAssert_parenthesizer__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_Term_doExpr = _init_l_Lean_Parser_Term_doExpr();
lean_mark_persistent(l_Lean_Parser_Term_doExpr);
if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doExpr__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doExpr_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doExpr_formatter__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doExpr_parenthesizer__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_Term_doNested = _init_l_Lean_Parser_Term_doNested();
lean_mark_persistent(l_Lean_Parser_Term_doNested);
if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doNested__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doNested_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doNested_formatter__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_doNested_parenthesizer__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_Term_do = _init_l_Lean_Parser_Term_do();
lean_mark_persistent(l_Lean_Parser_Term_do);
if (builtin) {res = l___regBuiltin_Lean_Parser_Term_do__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_do_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_do_formatter__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_do_parenthesizer__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_Term_termUnless = _init_l_Lean_Parser_Term_termUnless();
lean_mark_persistent(l_Lean_Parser_Term_termUnless);
if (builtin) {res = l___regBuiltin_Lean_Parser_Term_termUnless__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_termUnless_docString__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_termUnless_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_termUnless_formatter__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_termUnless_parenthesizer__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_Term_termFor = _init_l_Lean_Parser_Term_termFor();
lean_mark_persistent(l_Lean_Parser_Term_termFor);
if (builtin) {res = l___regBuiltin_Lean_Parser_Term_termFor__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_termFor_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_termFor_formatter__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_termFor_parenthesizer__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_Term_termTry = _init_l_Lean_Parser_Term_termTry();
lean_mark_persistent(l_Lean_Parser_Term_termTry);
if (builtin) {res = l___regBuiltin_Lean_Parser_Term_termTry__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_termTry_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_termTry_formatter__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_termTry_parenthesizer__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_Term_termReturn = _init_l_Lean_Parser_Term_termReturn();
lean_mark_persistent(l_Lean_Parser_Term_termReturn);
if (builtin) {res = l___regBuiltin_Lean_Parser_Term_termReturn__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_termReturn_docString__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_termReturn_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_termReturn_formatter__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Term_termReturn_parenthesizer__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
