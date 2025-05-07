// Lean compiler output
// Module: Lean.Parser
// Imports: Lean.Parser.Basic Lean.Parser.Level Lean.Parser.Term Lean.Parser.Tactic Lean.Parser.Command Lean.Parser.Module Lean.Parser.Syntax Lean.Parser.Do Lean.Parser.Tactic.Doc
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
LEAN_EXPORT lean_object* l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_many1_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_checkColEq(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_notFollowedBy_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_charLit_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_optional_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkWsBefore_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_charLit_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_mkAntiquot_parenthesizer_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_orelse_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_initFn___lam__0____x40_Lean_Parser___hyg_7_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_scientificLit_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_PrettyPrinter_Formatter_numLit_formatter__1(lean_object*);
lean_object* l_Lean_Parser_mkAntiquot_parenthesizer(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_PrettyPrinter_Formatter_charLit_formatter__1(lean_object*);
lean_object* l_Lean_Parser_many_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_recover(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_mkAntiquot_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_scientific_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_interpolatedStr(lean_object*);
lean_object* l_Lean_Parser_optional(lean_object*);
LEAN_EXPORT lean_object* lean_mk_antiquot_parenthesizer(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_nameLit_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_hygieneInfo_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_strLit;
lean_object* l_Lean_Parser_checkLinebreakBefore(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkNoWsBefore_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_orelse(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_hygieneInfo;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkColEq_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_str_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_ident_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_initFn___lam__1____x40_Lean_Parser___hyg_7_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkNoWsBefore_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_pretty_printer_parenthesizer_interpret_parser_descr(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_strLit_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_withPosition(lean_object*);
lean_object* l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer__1(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_PrettyPrinter_Formatter_strLit_formatter__1(lean_object*);
lean_object* l_Lean_Parser_ident_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_pretty_printer_formatter_interpret_parser_descr(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_many1_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_char_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_many1Indent_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkColGe_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_nonReservedSymbol_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_PrettyPrinter_parenthesizerAttribute;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Parser_numLit_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_manyIndent_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_lookahead_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_mkAntiquot_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_registerAlias(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_notFollowedBy(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_symbol_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkLinebreakBefore_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_nameLit_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_nameLit;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_checkNoWsBefore(lean_object*);
lean_object* l_Lean_Parser_symbol_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_lookahead_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_withPosition_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkColGt_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_ident_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkColGt_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_scientificLit_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_many_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_initFn___lam__3____x40_Lean_Parser___hyg_7_(lean_object*);
lean_object* l_Lean_Parser_Term_ident_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_getBinaryAlias(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_interpolatedStr_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_charLit_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_mk_antiquot_formatter(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_hygieneInfo_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_getUnaryAlias___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_andthen(lean_object*, lean_object*);
lean_object* l_Lean_Parser_checkColGe(lean_object*);
lean_object* l_Lean_Parser_atomic(lean_object*);
lean_object* l_Lean_Parser_ident_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_charLit;
lean_object* l_Lean_Parser_sepBy_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_PrettyPrinter_Formatter_formatterAliasesRef;
lean_object* l_Lean_PrettyPrinter_Formatter_checkColEq_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_scientificLit;
lean_object* l_Lean_PrettyPrinter_Formatter_checkLinebreakBefore_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_many(lean_object*);
extern lean_object* l_Lean_PrettyPrinter_combinatorFormatterAttribute;
LEAN_EXPORT lean_object* l_Lean_Parser_initFn___lam__4____x40_Lean_Parser___hyg_7_(lean_object*);
lean_object* l_Lean_Parser_Term_num_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_numLit_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_withPosition_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_ident;
lean_object* l_Lean_Parser_optional_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_PrettyPrinter_Formatter_scientificLit_formatter__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_PrettyPrinter_combinatorParenthesizerAttribute;
lean_object* l_Lean_Parser_sepBy1_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_manyIndent_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkLineEq_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_withoutForbidden_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_atomic_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_PrettyPrinter_Parenthesizer_parenthesizerAliasesRef;
lean_object* l_Lean_Parser_withoutPosition_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1(lean_object*);
lean_object* l_Lean_Parser_registerAlias(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_many1(lean_object*);
lean_object* l_Lean_Parser_getConstAlias(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_checkLineEq(lean_object*);
lean_object* l_Lean_Parser_Term_scientific_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_PrettyPrinter_Formatter_strLit_formatter__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_andthen_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkColGe_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_mkAntiquot_formatter_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer__1(lean_object*);
lean_object* l_Lean_Parser_checkWsBefore(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_many1Indent_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_char_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1(lean_object*);
lean_object* l_Lean_Parser_sepBy1_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_lookahead(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_notFollowedBy_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_withoutForbidden(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer__1(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
extern lean_object* l_Lean_Parser_numLit;
lean_object* l_Lean_Parser_mkAntiquot_formatter(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
extern lean_object* l_Lean_PrettyPrinter_formatterAttribute;
lean_object* l_Lean_Parser_strLit_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_sepBy_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_PrettyPrinter_Formatter_numLit_formatter__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_nonReservedSymbol_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_numLit_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_strLit_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_PrettyPrinter_Formatter_scientificLit_formatter__1(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_categoryParser_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_str_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_num_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_initFn____x40_Lean_Parser___hyg_7_(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkWsBefore_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_withoutPosition(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_PrettyPrinter_Formatter_charLit_formatter__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_withoutForbidden_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_checkColGt(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_initFn___lam__2____x40_Lean_Parser___hyg_7_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_scientificLit_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkLineEq_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_node_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_registerAlias(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_initFn___lam__0____x40_Lean_Parser___hyg_7_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_mk_string_unchecked("element", 7, 7);
x_3 = l_Lean_Parser_notFollowedBy(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initFn___lam__1____x40_Lean_Parser___hyg_7_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initFn___lam__2____x40_Lean_Parser___hyg_7_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initFn___lam__4____x40_Lean_Parser___hyg_7_(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_initFn___lam__3____x40_Lean_Parser___hyg_7_(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_initFn____x40_Lean_Parser___hyg_7_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_29; lean_object* x_30; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; uint8_t x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_197; lean_object* x_198; uint8_t x_199; lean_object* x_200; lean_object* x_201; lean_object* x_218; uint8_t x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_239; lean_object* x_240; uint8_t x_241; lean_object* x_242; lean_object* x_243; lean_object* x_261; uint8_t x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; uint8_t x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_542; lean_object* x_565; lean_object* x_585; lean_object* x_605; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_initFn___lam__0____x40_Lean_Parser___hyg_7_), 1, 0);
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_initFn___lam__1____x40_Lean_Parser___hyg_7_), 6, 0);
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_initFn___lam__2____x40_Lean_Parser___hyg_7_), 6, 0);
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_initFn___lam__4____x40_Lean_Parser___hyg_7_), 1, 0);
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_initFn___lam__3____x40_Lean_Parser___hyg_7_), 1, 0);
x_7 = lean_mk_string_unchecked("ws", 2, 2);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("Lean", 4, 4);
x_10 = lean_mk_string_unchecked("Parser", 6, 6);
x_167 = lean_mk_string_unchecked("checkWsBefore", 13, 13);
lean_inc(x_10);
lean_inc(x_9);
x_168 = l_Lean_Name_mkStr3(x_9, x_10, x_167);
x_169 = lean_mk_string_unchecked("space before", 12, 12);
x_170 = l_Lean_Parser_checkWsBefore(x_169);
x_171 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_171, 0, x_170);
lean_inc(x_168);
x_172 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_172, 0, x_168);
x_173 = lean_box(0);
x_309 = lean_unsigned_to_nat(0u);
x_310 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_310, 0, x_309);
x_311 = lean_box(1);
x_312 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_312, 0, x_173);
lean_ctor_set(x_312, 1, x_310);
x_313 = lean_unbox(x_311);
lean_ctor_set_uint8(x_312, sizeof(void*)*2, x_313);
lean_inc(x_8);
x_605 = l_Lean_Parser_registerAlias(x_8, x_168, x_171, x_172, x_312, x_1);
if (lean_obj_tag(x_605) == 0)
{
lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; 
x_606 = lean_ctor_get(x_605, 1);
lean_inc(x_606);
lean_dec(x_605);
x_607 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkWsBefore_formatter___boxed), 5, 0);
x_608 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_608, 0, x_607);
lean_inc(x_8);
x_609 = l_Lean_PrettyPrinter_Formatter_registerAlias(x_8, x_608, x_606);
if (lean_obj_tag(x_609) == 0)
{
lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; 
x_610 = lean_ctor_get(x_609, 1);
lean_inc(x_610);
lean_dec(x_609);
x_611 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkWsBefore_parenthesizer___boxed), 5, 0);
x_612 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_612, 0, x_611);
x_613 = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(x_8, x_612, x_610);
x_585 = x_613;
goto block_604;
}
else
{
lean_dec(x_8);
x_585 = x_609;
goto block_604;
}
}
else
{
lean_dec(x_8);
x_585 = x_605;
goto block_604;
}
block_28:
{
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_mk_string_unchecked("notFollowedBy", 13, 13);
lean_inc(x_14);
x_15 = l_Lean_Name_mkStr1(x_14);
x_16 = l_Lean_Name_mkStr3(x_9, x_10, x_14);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_2);
x_18 = lean_box(0);
lean_inc(x_15);
x_19 = l_Lean_Parser_registerAlias(x_15, x_16, x_17, x_18, x_11, x_13);
lean_dec(x_11);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_notFollowedBy_parenthesizer___boxed), 6, 0);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
lean_inc(x_15);
x_23 = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(x_15, x_22, x_20);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_notFollowedBy_formatter___boxed), 6, 0);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = l_Lean_PrettyPrinter_Formatter_registerAlias(x_15, x_26, x_24);
return x_27;
}
else
{
lean_dec(x_15);
return x_23;
}
}
else
{
lean_dec(x_15);
return x_19;
}
}
else
{
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_2);
return x_12;
}
}
block_45:
{
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_mk_string_unchecked("recover", 7, 7);
lean_inc(x_32);
x_33 = l_Lean_Name_mkStr1(x_32);
lean_inc(x_10);
lean_inc(x_9);
x_34 = l_Lean_Name_mkStr3(x_9, x_10, x_32);
x_35 = lean_alloc_closure((void*)(l_Lean_Parser_recover), 2, 0);
x_36 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_36, 0, x_35);
lean_inc(x_34);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_34);
lean_inc(x_33);
x_38 = l_Lean_Parser_registerAlias(x_33, x_34, x_36, x_37, x_29, x_31);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_3);
lean_inc(x_33);
x_41 = l_Lean_PrettyPrinter_Formatter_registerAlias(x_33, x_40, x_39);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_4);
x_44 = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(x_33, x_43, x_42);
x_11 = x_29;
x_12 = x_44;
goto block_28;
}
else
{
lean_dec(x_33);
lean_dec(x_4);
x_11 = x_29;
x_12 = x_41;
goto block_28;
}
}
else
{
lean_dec(x_33);
lean_dec(x_4);
lean_dec(x_3);
x_11 = x_29;
x_12 = x_38;
goto block_28;
}
}
else
{
lean_dec(x_29);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_30;
}
}
block_65:
{
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec(x_48);
x_50 = lean_mk_string_unchecked("andthen", 7, 7);
lean_inc(x_50);
x_51 = l_Lean_Name_mkStr1(x_50);
lean_inc(x_10);
lean_inc(x_9);
x_52 = l_Lean_Name_mkStr3(x_9, x_10, x_50);
x_53 = lean_alloc_closure((void*)(l_Lean_Parser_andthen), 2, 0);
x_54 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_54, 0, x_53);
lean_inc(x_52);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_52);
lean_inc(x_51);
x_56 = l_Lean_Parser_registerAlias(x_51, x_52, x_54, x_55, x_47, x_49);
lean_dec(x_47);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
lean_dec(x_56);
x_58 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 0);
x_59 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_59, 0, x_58);
lean_inc(x_51);
x_60 = l_Lean_PrettyPrinter_Formatter_registerAlias(x_51, x_59, x_57);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
lean_dec(x_60);
x_62 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 0);
x_63 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_63, 0, x_62);
x_64 = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(x_51, x_63, x_61);
x_29 = x_46;
x_30 = x_64;
goto block_45;
}
else
{
lean_dec(x_51);
x_29 = x_46;
x_30 = x_60;
goto block_45;
}
}
else
{
lean_dec(x_51);
x_29 = x_46;
x_30 = x_56;
goto block_45;
}
}
else
{
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_48;
}
}
block_85:
{
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
lean_dec(x_68);
x_70 = lean_mk_string_unchecked("orelse", 6, 6);
lean_inc(x_70);
x_71 = l_Lean_Name_mkStr1(x_70);
lean_inc(x_10);
lean_inc(x_9);
x_72 = l_Lean_Name_mkStr3(x_9, x_10, x_70);
x_73 = lean_alloc_closure((void*)(l_Lean_Parser_orelse), 2, 0);
x_74 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_74, 0, x_73);
lean_inc(x_72);
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_72);
lean_inc(x_71);
x_76 = l_Lean_Parser_registerAlias(x_71, x_72, x_74, x_75, x_66, x_69);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_77 = lean_ctor_get(x_76, 1);
lean_inc(x_77);
lean_dec(x_76);
x_78 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter), 7, 0);
x_79 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_79, 0, x_78);
lean_inc(x_71);
x_80 = l_Lean_PrettyPrinter_Formatter_registerAlias(x_71, x_79, x_77);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
lean_dec(x_80);
x_82 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer), 7, 0);
x_83 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_83, 0, x_82);
x_84 = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(x_71, x_83, x_81);
x_46 = x_66;
x_47 = x_67;
x_48 = x_84;
goto block_65;
}
else
{
lean_dec(x_71);
x_46 = x_66;
x_47 = x_67;
x_48 = x_80;
goto block_65;
}
}
else
{
lean_dec(x_71);
x_46 = x_66;
x_47 = x_67;
x_48 = x_76;
goto block_65;
}
}
else
{
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_68;
}
}
block_107:
{
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_89 = lean_ctor_get(x_88, 1);
lean_inc(x_89);
lean_dec(x_88);
x_90 = lean_mk_string_unchecked("interpolatedStr", 15, 15);
lean_inc(x_90);
x_91 = l_Lean_Name_mkStr1(x_90);
lean_inc(x_10);
lean_inc(x_9);
x_92 = l_Lean_Name_mkStr3(x_9, x_10, x_90);
x_93 = lean_alloc_closure((void*)(l_Lean_Parser_interpolatedStr), 1, 0);
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_93);
x_95 = lean_mk_string_unchecked("interpolatedStrKind", 19, 19);
x_96 = l_Lean_Name_mkStr1(x_95);
x_97 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_97, 0, x_96);
lean_inc(x_91);
x_98 = l_Lean_Parser_registerAlias(x_91, x_92, x_94, x_97, x_86, x_89);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_99 = lean_ctor_get(x_98, 1);
lean_inc(x_99);
lean_dec(x_98);
x_100 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter), 6, 0);
x_101 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_101, 0, x_100);
lean_inc(x_91);
x_102 = l_Lean_PrettyPrinter_Formatter_registerAlias(x_91, x_101, x_99);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_103 = lean_ctor_get(x_102, 1);
lean_inc(x_103);
lean_dec(x_102);
x_104 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_interpolatedStr_parenthesizer), 6, 0);
x_105 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_105, 0, x_104);
x_106 = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(x_91, x_105, x_103);
x_66 = x_86;
x_67 = x_87;
x_68 = x_106;
goto block_85;
}
else
{
lean_dec(x_91);
x_66 = x_86;
x_67 = x_87;
x_68 = x_102;
goto block_85;
}
}
else
{
lean_dec(x_91);
x_66 = x_86;
x_67 = x_87;
x_68 = x_98;
goto block_85;
}
}
else
{
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_88;
}
}
block_127:
{
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_111 = lean_ctor_get(x_110, 1);
lean_inc(x_111);
lean_dec(x_110);
x_112 = lean_mk_string_unchecked("withoutForbidden", 16, 16);
lean_inc(x_112);
x_113 = l_Lean_Name_mkStr1(x_112);
lean_inc(x_10);
lean_inc(x_9);
x_114 = l_Lean_Name_mkStr3(x_9, x_10, x_112);
x_115 = lean_alloc_closure((void*)(l_Lean_Parser_withoutForbidden), 1, 0);
x_116 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_116, 0, x_115);
lean_inc(x_114);
x_117 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_117, 0, x_114);
lean_inc(x_113);
x_118 = l_Lean_Parser_registerAlias(x_113, x_114, x_116, x_117, x_109, x_111);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_119 = lean_ctor_get(x_118, 1);
lean_inc(x_119);
lean_dec(x_118);
x_120 = lean_alloc_closure((void*)(l_Lean_Parser_withoutForbidden_formatter), 6, 0);
x_121 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_121, 0, x_120);
lean_inc(x_113);
x_122 = l_Lean_PrettyPrinter_Formatter_registerAlias(x_113, x_121, x_119);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_123 = lean_ctor_get(x_122, 1);
lean_inc(x_123);
lean_dec(x_122);
x_124 = lean_alloc_closure((void*)(l_Lean_Parser_withoutForbidden_parenthesizer), 6, 0);
x_125 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_125, 0, x_124);
x_126 = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(x_113, x_125, x_123);
x_86 = x_108;
x_87 = x_109;
x_88 = x_126;
goto block_107;
}
else
{
lean_dec(x_113);
x_86 = x_108;
x_87 = x_109;
x_88 = x_122;
goto block_107;
}
}
else
{
lean_dec(x_113);
x_86 = x_108;
x_87 = x_109;
x_88 = x_118;
goto block_107;
}
}
else
{
lean_dec(x_109);
lean_dec(x_108);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_110;
}
}
block_146:
{
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_131 = lean_ctor_get(x_130, 1);
lean_inc(x_131);
lean_dec(x_130);
x_132 = lean_mk_string_unchecked("withoutPosition", 15, 15);
lean_inc(x_132);
x_133 = l_Lean_Name_mkStr1(x_132);
lean_inc(x_10);
lean_inc(x_9);
x_134 = l_Lean_Name_mkStr3(x_9, x_10, x_132);
x_135 = lean_alloc_closure((void*)(l_Lean_Parser_withoutPosition), 1, 0);
x_136 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_136, 0, x_135);
lean_inc(x_134);
x_137 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_137, 0, x_134);
lean_inc(x_133);
x_138 = l_Lean_Parser_registerAlias(x_133, x_134, x_136, x_137, x_129, x_131);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_139 = lean_ctor_get(x_138, 1);
lean_inc(x_139);
lean_dec(x_138);
x_140 = lean_alloc_closure((void*)(l_Lean_Parser_withoutPosition_formatter), 6, 0);
x_141 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_141, 0, x_140);
lean_inc(x_133);
x_142 = l_Lean_PrettyPrinter_Formatter_registerAlias(x_133, x_141, x_139);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_143 = lean_ctor_get(x_142, 1);
lean_inc(x_143);
lean_dec(x_142);
lean_inc(x_4);
x_144 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_144, 0, x_4);
x_145 = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(x_133, x_144, x_143);
x_108 = x_128;
x_109 = x_129;
x_110 = x_145;
goto block_127;
}
else
{
lean_dec(x_133);
x_108 = x_128;
x_109 = x_129;
x_110 = x_142;
goto block_127;
}
}
else
{
lean_dec(x_133);
x_108 = x_128;
x_109 = x_129;
x_110 = x_138;
goto block_127;
}
}
else
{
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_130;
}
}
block_166:
{
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_150 = lean_ctor_get(x_149, 1);
lean_inc(x_150);
lean_dec(x_149);
x_151 = lean_mk_string_unchecked("withPosition", 12, 12);
lean_inc(x_151);
x_152 = l_Lean_Name_mkStr1(x_151);
lean_inc(x_10);
lean_inc(x_9);
x_153 = l_Lean_Name_mkStr3(x_9, x_10, x_151);
x_154 = lean_alloc_closure((void*)(l_Lean_Parser_withPosition), 1, 0);
x_155 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_155, 0, x_154);
lean_inc(x_153);
x_156 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_156, 0, x_153);
lean_inc(x_152);
x_157 = l_Lean_Parser_registerAlias(x_152, x_153, x_155, x_156, x_148, x_150);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_158 = lean_ctor_get(x_157, 1);
lean_inc(x_158);
lean_dec(x_157);
x_159 = lean_alloc_closure((void*)(l_Lean_Parser_withPosition_formatter), 6, 0);
x_160 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_160, 0, x_159);
lean_inc(x_152);
x_161 = l_Lean_PrettyPrinter_Formatter_registerAlias(x_152, x_160, x_158);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_162 = lean_ctor_get(x_161, 1);
lean_inc(x_162);
lean_dec(x_161);
x_163 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_withPosition_parenthesizer), 6, 0);
x_164 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_164, 0, x_163);
x_165 = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(x_152, x_164, x_162);
x_128 = x_147;
x_129 = x_148;
x_130 = x_165;
goto block_146;
}
else
{
lean_dec(x_152);
x_128 = x_147;
x_129 = x_148;
x_130 = x_161;
goto block_146;
}
}
else
{
lean_dec(x_152);
x_128 = x_147;
x_129 = x_148;
x_130 = x_157;
goto block_146;
}
}
else
{
lean_dec(x_148);
lean_dec(x_147);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_149;
}
}
block_196:
{
if (lean_obj_tag(x_178) == 0)
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_179 = lean_ctor_get(x_178, 1);
lean_inc(x_179);
lean_dec(x_178);
x_180 = lean_mk_string_unchecked("optional", 8, 8);
lean_inc(x_180);
x_181 = l_Lean_Name_mkStr1(x_180);
lean_inc(x_10);
lean_inc(x_9);
x_182 = l_Lean_Name_mkStr3(x_9, x_10, x_180);
x_183 = lean_alloc_closure((void*)(l_Lean_Parser_optional), 1, 0);
x_184 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_184, 0, x_183);
lean_inc(x_182);
x_185 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_185, 0, x_182);
x_186 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_186, 0, x_173);
lean_ctor_set(x_186, 1, x_176);
lean_ctor_set_uint8(x_186, sizeof(void*)*2, x_175);
lean_inc(x_181);
x_187 = l_Lean_Parser_registerAlias(x_181, x_182, x_184, x_185, x_186, x_179);
lean_dec(x_186);
if (lean_obj_tag(x_187) == 0)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_188 = lean_ctor_get(x_187, 1);
lean_inc(x_188);
lean_dec(x_187);
x_189 = lean_alloc_closure((void*)(l_Lean_Parser_optional_formatter), 6, 0);
x_190 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_190, 0, x_189);
lean_inc(x_181);
x_191 = l_Lean_PrettyPrinter_Formatter_registerAlias(x_181, x_190, x_188);
if (lean_obj_tag(x_191) == 0)
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_192 = lean_ctor_get(x_191, 1);
lean_inc(x_192);
lean_dec(x_191);
x_193 = lean_alloc_closure((void*)(l_Lean_Parser_optional_parenthesizer), 6, 0);
x_194 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_194, 0, x_193);
x_195 = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(x_181, x_194, x_192);
x_147 = x_174;
x_148 = x_177;
x_149 = x_195;
goto block_166;
}
else
{
lean_dec(x_181);
x_147 = x_174;
x_148 = x_177;
x_149 = x_191;
goto block_166;
}
}
else
{
lean_dec(x_181);
x_147 = x_174;
x_148 = x_177;
x_149 = x_187;
goto block_166;
}
}
else
{
lean_dec(x_177);
lean_dec(x_176);
lean_dec(x_174);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_178;
}
}
block_217:
{
if (lean_obj_tag(x_201) == 0)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_202 = lean_ctor_get(x_201, 1);
lean_inc(x_202);
lean_dec(x_201);
x_203 = lean_mk_string_unchecked("many1Indent", 11, 11);
lean_inc(x_203);
x_204 = l_Lean_Name_mkStr1(x_203);
lean_inc(x_10);
lean_inc(x_9);
x_205 = l_Lean_Name_mkStr3(x_9, x_10, x_203);
x_206 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_206, 0, x_5);
lean_inc(x_205);
x_207 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_207, 0, x_205);
lean_inc(x_204);
x_208 = l_Lean_Parser_registerAlias(x_204, x_205, x_206, x_207, x_197, x_202);
if (lean_obj_tag(x_208) == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_209 = lean_ctor_get(x_208, 1);
lean_inc(x_209);
lean_dec(x_208);
x_210 = lean_alloc_closure((void*)(l_Lean_Parser_many1Indent_formatter), 6, 0);
x_211 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_211, 0, x_210);
lean_inc(x_204);
x_212 = l_Lean_PrettyPrinter_Formatter_registerAlias(x_204, x_211, x_209);
if (lean_obj_tag(x_212) == 0)
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_213 = lean_ctor_get(x_212, 1);
lean_inc(x_213);
lean_dec(x_212);
x_214 = lean_alloc_closure((void*)(l_Lean_Parser_many1Indent_parenthesizer), 6, 0);
x_215 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_215, 0, x_214);
x_216 = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(x_204, x_215, x_213);
x_174 = x_197;
x_175 = x_199;
x_176 = x_198;
x_177 = x_200;
x_178 = x_216;
goto block_196;
}
else
{
lean_dec(x_204);
x_174 = x_197;
x_175 = x_199;
x_176 = x_198;
x_177 = x_200;
x_178 = x_212;
goto block_196;
}
}
else
{
lean_dec(x_204);
x_174 = x_197;
x_175 = x_199;
x_176 = x_198;
x_177 = x_200;
x_178 = x_208;
goto block_196;
}
}
else
{
lean_dec(x_200);
lean_dec(x_198);
lean_dec(x_197);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_201;
}
}
block_238:
{
if (lean_obj_tag(x_222) == 0)
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_223 = lean_ctor_get(x_222, 1);
lean_inc(x_223);
lean_dec(x_222);
x_224 = lean_mk_string_unchecked("manyIndent", 10, 10);
lean_inc(x_224);
x_225 = l_Lean_Name_mkStr1(x_224);
lean_inc(x_10);
lean_inc(x_9);
x_226 = l_Lean_Name_mkStr3(x_9, x_10, x_224);
x_227 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_227, 0, x_6);
lean_inc(x_226);
x_228 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_228, 0, x_226);
lean_inc(x_225);
x_229 = l_Lean_Parser_registerAlias(x_225, x_226, x_227, x_228, x_218, x_223);
if (lean_obj_tag(x_229) == 0)
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_230 = lean_ctor_get(x_229, 1);
lean_inc(x_230);
lean_dec(x_229);
x_231 = lean_alloc_closure((void*)(l_Lean_Parser_manyIndent_formatter), 6, 0);
x_232 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_232, 0, x_231);
lean_inc(x_225);
x_233 = l_Lean_PrettyPrinter_Formatter_registerAlias(x_225, x_232, x_230);
if (lean_obj_tag(x_233) == 0)
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_234 = lean_ctor_get(x_233, 1);
lean_inc(x_234);
lean_dec(x_233);
x_235 = lean_alloc_closure((void*)(l_Lean_Parser_manyIndent_parenthesizer), 6, 0);
x_236 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_236, 0, x_235);
x_237 = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(x_225, x_236, x_234);
x_197 = x_218;
x_198 = x_220;
x_199 = x_219;
x_200 = x_221;
x_201 = x_237;
goto block_217;
}
else
{
lean_dec(x_225);
x_197 = x_218;
x_198 = x_220;
x_199 = x_219;
x_200 = x_221;
x_201 = x_233;
goto block_217;
}
}
else
{
lean_dec(x_225);
x_197 = x_218;
x_198 = x_220;
x_199 = x_219;
x_200 = x_221;
x_201 = x_229;
goto block_217;
}
}
else
{
lean_dec(x_221);
lean_dec(x_220);
lean_dec(x_218);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_222;
}
}
block_260:
{
if (lean_obj_tag(x_243) == 0)
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_244 = lean_ctor_get(x_243, 1);
lean_inc(x_244);
lean_dec(x_243);
x_245 = lean_mk_string_unchecked("many1", 5, 5);
lean_inc(x_245);
x_246 = l_Lean_Name_mkStr1(x_245);
lean_inc(x_10);
lean_inc(x_9);
x_247 = l_Lean_Name_mkStr3(x_9, x_10, x_245);
x_248 = lean_alloc_closure((void*)(l_Lean_Parser_many1), 1, 0);
x_249 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_249, 0, x_248);
lean_inc(x_247);
x_250 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_250, 0, x_247);
lean_inc(x_246);
x_251 = l_Lean_Parser_registerAlias(x_246, x_247, x_249, x_250, x_239, x_244);
if (lean_obj_tag(x_251) == 0)
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; 
x_252 = lean_ctor_get(x_251, 1);
lean_inc(x_252);
lean_dec(x_251);
x_253 = lean_alloc_closure((void*)(l_Lean_Parser_many1_formatter), 6, 0);
x_254 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_254, 0, x_253);
lean_inc(x_246);
x_255 = l_Lean_PrettyPrinter_Formatter_registerAlias(x_246, x_254, x_252);
if (lean_obj_tag(x_255) == 0)
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; 
x_256 = lean_ctor_get(x_255, 1);
lean_inc(x_256);
lean_dec(x_255);
x_257 = lean_alloc_closure((void*)(l_Lean_Parser_many1_parenthesizer), 6, 0);
x_258 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_258, 0, x_257);
x_259 = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(x_246, x_258, x_256);
x_218 = x_239;
x_219 = x_241;
x_220 = x_240;
x_221 = x_242;
x_222 = x_259;
goto block_238;
}
else
{
lean_dec(x_246);
x_218 = x_239;
x_219 = x_241;
x_220 = x_240;
x_221 = x_242;
x_222 = x_255;
goto block_238;
}
}
else
{
lean_dec(x_246);
x_218 = x_239;
x_219 = x_241;
x_220 = x_240;
x_221 = x_242;
x_222 = x_251;
goto block_238;
}
}
else
{
lean_dec(x_242);
lean_dec(x_240);
lean_dec(x_239);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_243;
}
}
block_282:
{
if (lean_obj_tag(x_265) == 0)
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; 
x_266 = lean_ctor_get(x_265, 1);
lean_inc(x_266);
lean_dec(x_265);
x_267 = lean_mk_string_unchecked("many", 4, 4);
lean_inc(x_267);
x_268 = l_Lean_Name_mkStr1(x_267);
lean_inc(x_10);
lean_inc(x_9);
x_269 = l_Lean_Name_mkStr3(x_9, x_10, x_267);
x_270 = lean_alloc_closure((void*)(l_Lean_Parser_many), 1, 0);
x_271 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_271, 0, x_270);
lean_inc(x_269);
x_272 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_272, 0, x_269);
lean_inc(x_268);
x_273 = l_Lean_Parser_registerAlias(x_268, x_269, x_271, x_272, x_261, x_266);
if (lean_obj_tag(x_273) == 0)
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; 
x_274 = lean_ctor_get(x_273, 1);
lean_inc(x_274);
lean_dec(x_273);
x_275 = lean_alloc_closure((void*)(l_Lean_Parser_many_formatter), 6, 0);
x_276 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_276, 0, x_275);
lean_inc(x_268);
x_277 = l_Lean_PrettyPrinter_Formatter_registerAlias(x_268, x_276, x_274);
if (lean_obj_tag(x_277) == 0)
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; 
x_278 = lean_ctor_get(x_277, 1);
lean_inc(x_278);
lean_dec(x_277);
x_279 = lean_alloc_closure((void*)(l_Lean_Parser_many_parenthesizer), 6, 0);
x_280 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_280, 0, x_279);
x_281 = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(x_268, x_280, x_278);
x_239 = x_261;
x_240 = x_263;
x_241 = x_262;
x_242 = x_264;
x_243 = x_281;
goto block_260;
}
else
{
lean_dec(x_268);
x_239 = x_261;
x_240 = x_263;
x_241 = x_262;
x_242 = x_264;
x_243 = x_277;
goto block_260;
}
}
else
{
lean_dec(x_268);
x_239 = x_261;
x_240 = x_263;
x_241 = x_262;
x_242 = x_264;
x_243 = x_273;
goto block_260;
}
}
else
{
lean_dec(x_264);
lean_dec(x_263);
lean_dec(x_261);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_265;
}
}
block_308:
{
if (lean_obj_tag(x_285) == 0)
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; uint8_t x_296; lean_object* x_297; 
x_286 = lean_ctor_get(x_285, 1);
lean_inc(x_286);
lean_dec(x_285);
x_287 = lean_mk_string_unchecked("atomic", 6, 6);
lean_inc(x_287);
x_288 = l_Lean_Name_mkStr1(x_287);
lean_inc(x_10);
lean_inc(x_9);
x_289 = l_Lean_Name_mkStr3(x_9, x_10, x_287);
x_290 = lean_alloc_closure((void*)(l_Lean_Parser_atomic), 1, 0);
x_291 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_291, 0, x_290);
lean_inc(x_289);
x_292 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_292, 0, x_289);
x_293 = lean_box(0);
x_294 = lean_box(0);
x_295 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_295, 0, x_173);
lean_ctor_set(x_295, 1, x_293);
x_296 = lean_unbox(x_294);
lean_ctor_set_uint8(x_295, sizeof(void*)*2, x_296);
lean_inc(x_288);
x_297 = l_Lean_Parser_registerAlias(x_288, x_289, x_291, x_292, x_295, x_286);
if (lean_obj_tag(x_297) == 0)
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; 
x_298 = lean_ctor_get(x_297, 1);
lean_inc(x_298);
lean_dec(x_297);
x_299 = lean_alloc_closure((void*)(l_Lean_Parser_atomic_formatter), 6, 0);
x_300 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_300, 0, x_299);
lean_inc(x_288);
x_301 = l_Lean_PrettyPrinter_Formatter_registerAlias(x_288, x_300, x_298);
if (lean_obj_tag(x_301) == 0)
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; uint8_t x_305; 
x_302 = lean_ctor_get(x_301, 1);
lean_inc(x_302);
lean_dec(x_301);
lean_inc(x_4);
x_303 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_303, 0, x_4);
x_304 = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(x_288, x_303, x_302);
x_305 = lean_unbox(x_294);
x_261 = x_283;
x_262 = x_305;
x_263 = x_284;
x_264 = x_295;
x_265 = x_304;
goto block_282;
}
else
{
uint8_t x_306; 
lean_dec(x_288);
x_306 = lean_unbox(x_294);
x_261 = x_283;
x_262 = x_306;
x_263 = x_284;
x_264 = x_295;
x_265 = x_301;
goto block_282;
}
}
else
{
uint8_t x_307; 
lean_dec(x_288);
x_307 = lean_unbox(x_294);
x_261 = x_283;
x_262 = x_307;
x_263 = x_284;
x_264 = x_295;
x_265 = x_297;
goto block_282;
}
}
else
{
lean_dec(x_284);
lean_dec(x_283);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_285;
}
}
block_333:
{
if (lean_obj_tag(x_316) == 0)
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; 
x_317 = lean_ctor_get(x_316, 1);
lean_inc(x_317);
lean_dec(x_316);
x_318 = lean_mk_string_unchecked("lookahead", 9, 9);
lean_inc(x_318);
x_319 = l_Lean_Name_mkStr1(x_318);
lean_inc(x_10);
lean_inc(x_9);
x_320 = l_Lean_Name_mkStr3(x_9, x_10, x_318);
x_321 = lean_alloc_closure((void*)(l_Lean_Parser_lookahead), 1, 0);
x_322 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_322, 0, x_321);
lean_inc(x_320);
x_323 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_323, 0, x_320);
lean_inc(x_319);
x_324 = l_Lean_Parser_registerAlias(x_319, x_320, x_322, x_323, x_312, x_317);
lean_dec(x_312);
if (lean_obj_tag(x_324) == 0)
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; 
x_325 = lean_ctor_get(x_324, 1);
lean_inc(x_325);
lean_dec(x_324);
x_326 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_lookahead_formatter___boxed), 6, 0);
x_327 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_327, 0, x_326);
lean_inc(x_319);
x_328 = l_Lean_PrettyPrinter_Formatter_registerAlias(x_319, x_327, x_325);
if (lean_obj_tag(x_328) == 0)
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; 
x_329 = lean_ctor_get(x_328, 1);
lean_inc(x_329);
lean_dec(x_328);
x_330 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_lookahead_parenthesizer___boxed), 6, 0);
x_331 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_331, 0, x_330);
x_332 = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(x_319, x_331, x_329);
x_283 = x_314;
x_284 = x_315;
x_285 = x_332;
goto block_308;
}
else
{
lean_dec(x_319);
x_283 = x_314;
x_284 = x_315;
x_285 = x_328;
goto block_308;
}
}
else
{
lean_dec(x_319);
x_283 = x_314;
x_284 = x_315;
x_285 = x_324;
goto block_308;
}
}
else
{
lean_dec(x_315);
lean_dec(x_314);
lean_dec(x_312);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_316;
}
}
block_354:
{
if (lean_obj_tag(x_336) == 0)
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; 
x_337 = lean_ctor_get(x_336, 1);
lean_inc(x_337);
lean_dec(x_336);
x_338 = lean_mk_string_unchecked("lineEq", 6, 6);
x_339 = l_Lean_Name_mkStr1(x_338);
x_340 = lean_mk_string_unchecked("checkLineEq", 11, 11);
lean_inc(x_340);
lean_inc(x_10);
lean_inc(x_9);
x_341 = l_Lean_Name_mkStr3(x_9, x_10, x_340);
x_342 = l_Lean_Parser_checkLineEq(x_340);
x_343 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_343, 0, x_342);
lean_inc(x_341);
x_344 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_344, 0, x_341);
lean_inc(x_339);
x_345 = l_Lean_Parser_registerAlias(x_339, x_341, x_343, x_344, x_312, x_337);
if (lean_obj_tag(x_345) == 0)
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; 
x_346 = lean_ctor_get(x_345, 1);
lean_inc(x_346);
lean_dec(x_345);
x_347 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkLineEq_formatter___boxed), 5, 0);
x_348 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_348, 0, x_347);
lean_inc(x_339);
x_349 = l_Lean_PrettyPrinter_Formatter_registerAlias(x_339, x_348, x_346);
if (lean_obj_tag(x_349) == 0)
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; 
x_350 = lean_ctor_get(x_349, 1);
lean_inc(x_350);
lean_dec(x_349);
x_351 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkLineEq_parenthesizer___boxed), 5, 0);
x_352 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_352, 0, x_351);
x_353 = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(x_339, x_352, x_350);
x_314 = x_334;
x_315 = x_335;
x_316 = x_353;
goto block_333;
}
else
{
lean_dec(x_339);
x_314 = x_334;
x_315 = x_335;
x_316 = x_349;
goto block_333;
}
}
else
{
lean_dec(x_339);
x_314 = x_334;
x_315 = x_335;
x_316 = x_345;
goto block_333;
}
}
else
{
lean_dec(x_335);
lean_dec(x_334);
lean_dec(x_312);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_336;
}
}
block_375:
{
if (lean_obj_tag(x_357) == 0)
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; 
x_358 = lean_ctor_get(x_357, 1);
lean_inc(x_358);
lean_dec(x_357);
x_359 = lean_mk_string_unchecked("colEq", 5, 5);
x_360 = l_Lean_Name_mkStr1(x_359);
x_361 = lean_mk_string_unchecked("checkColEq", 10, 10);
lean_inc(x_361);
lean_inc(x_10);
lean_inc(x_9);
x_362 = l_Lean_Name_mkStr3(x_9, x_10, x_361);
x_363 = l_Lean_Parser_checkColEq(x_361);
x_364 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_364, 0, x_363);
lean_inc(x_362);
x_365 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_365, 0, x_362);
lean_inc(x_360);
x_366 = l_Lean_Parser_registerAlias(x_360, x_362, x_364, x_365, x_312, x_358);
if (lean_obj_tag(x_366) == 0)
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; 
x_367 = lean_ctor_get(x_366, 1);
lean_inc(x_367);
lean_dec(x_366);
x_368 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkColEq_formatter___boxed), 5, 0);
x_369 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_369, 0, x_368);
lean_inc(x_360);
x_370 = l_Lean_PrettyPrinter_Formatter_registerAlias(x_360, x_369, x_367);
if (lean_obj_tag(x_370) == 0)
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; 
x_371 = lean_ctor_get(x_370, 1);
lean_inc(x_371);
lean_dec(x_370);
x_372 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkColEq_parenthesizer___boxed), 5, 0);
x_373 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_373, 0, x_372);
x_374 = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(x_360, x_373, x_371);
x_334 = x_355;
x_335 = x_356;
x_336 = x_374;
goto block_354;
}
else
{
lean_dec(x_360);
x_334 = x_355;
x_335 = x_356;
x_336 = x_370;
goto block_354;
}
}
else
{
lean_dec(x_360);
x_334 = x_355;
x_335 = x_356;
x_336 = x_366;
goto block_354;
}
}
else
{
lean_dec(x_356);
lean_dec(x_355);
lean_dec(x_312);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_357;
}
}
block_396:
{
if (lean_obj_tag(x_378) == 0)
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; 
x_379 = lean_ctor_get(x_378, 1);
lean_inc(x_379);
lean_dec(x_378);
x_380 = lean_mk_string_unchecked("colGe", 5, 5);
x_381 = l_Lean_Name_mkStr1(x_380);
x_382 = lean_mk_string_unchecked("checkColGe", 10, 10);
lean_inc(x_382);
lean_inc(x_10);
lean_inc(x_9);
x_383 = l_Lean_Name_mkStr3(x_9, x_10, x_382);
x_384 = l_Lean_Parser_checkColGe(x_382);
x_385 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_385, 0, x_384);
lean_inc(x_383);
x_386 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_386, 0, x_383);
lean_inc(x_381);
x_387 = l_Lean_Parser_registerAlias(x_381, x_383, x_385, x_386, x_312, x_379);
if (lean_obj_tag(x_387) == 0)
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; 
x_388 = lean_ctor_get(x_387, 1);
lean_inc(x_388);
lean_dec(x_387);
x_389 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkColGe_formatter___boxed), 5, 0);
x_390 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_390, 0, x_389);
lean_inc(x_381);
x_391 = l_Lean_PrettyPrinter_Formatter_registerAlias(x_381, x_390, x_388);
if (lean_obj_tag(x_391) == 0)
{
lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; 
x_392 = lean_ctor_get(x_391, 1);
lean_inc(x_392);
lean_dec(x_391);
x_393 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkColGe_parenthesizer___boxed), 5, 0);
x_394 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_394, 0, x_393);
x_395 = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(x_381, x_394, x_392);
x_355 = x_376;
x_356 = x_377;
x_357 = x_395;
goto block_375;
}
else
{
lean_dec(x_381);
x_355 = x_376;
x_356 = x_377;
x_357 = x_391;
goto block_375;
}
}
else
{
lean_dec(x_381);
x_355 = x_376;
x_356 = x_377;
x_357 = x_387;
goto block_375;
}
}
else
{
lean_dec(x_377);
lean_dec(x_376);
lean_dec(x_312);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_378;
}
}
block_417:
{
if (lean_obj_tag(x_399) == 0)
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; 
x_400 = lean_ctor_get(x_399, 1);
lean_inc(x_400);
lean_dec(x_399);
x_401 = lean_mk_string_unchecked("colGt", 5, 5);
x_402 = l_Lean_Name_mkStr1(x_401);
x_403 = lean_mk_string_unchecked("checkColGt", 10, 10);
lean_inc(x_403);
lean_inc(x_10);
lean_inc(x_9);
x_404 = l_Lean_Name_mkStr3(x_9, x_10, x_403);
x_405 = l_Lean_Parser_checkColGt(x_403);
x_406 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_406, 0, x_405);
lean_inc(x_404);
x_407 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_407, 0, x_404);
lean_inc(x_402);
x_408 = l_Lean_Parser_registerAlias(x_402, x_404, x_406, x_407, x_312, x_400);
if (lean_obj_tag(x_408) == 0)
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; 
x_409 = lean_ctor_get(x_408, 1);
lean_inc(x_409);
lean_dec(x_408);
x_410 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkColGt_formatter___boxed), 5, 0);
x_411 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_411, 0, x_410);
lean_inc(x_402);
x_412 = l_Lean_PrettyPrinter_Formatter_registerAlias(x_402, x_411, x_409);
if (lean_obj_tag(x_412) == 0)
{
lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; 
x_413 = lean_ctor_get(x_412, 1);
lean_inc(x_413);
lean_dec(x_412);
x_414 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkColGt_parenthesizer___boxed), 5, 0);
x_415 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_415, 0, x_414);
x_416 = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(x_402, x_415, x_413);
x_376 = x_397;
x_377 = x_398;
x_378 = x_416;
goto block_396;
}
else
{
lean_dec(x_402);
x_376 = x_397;
x_377 = x_398;
x_378 = x_412;
goto block_396;
}
}
else
{
lean_dec(x_402);
x_376 = x_397;
x_377 = x_398;
x_378 = x_408;
goto block_396;
}
}
else
{
lean_dec(x_398);
lean_dec(x_397);
lean_dec(x_312);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_399;
}
}
block_437:
{
if (lean_obj_tag(x_420) == 0)
{
lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; 
x_421 = lean_ctor_get(x_420, 1);
lean_inc(x_421);
lean_dec(x_420);
x_422 = lean_mk_string_unchecked("hygieneInfo", 11, 11);
lean_inc(x_422);
x_423 = l_Lean_Name_mkStr1(x_422);
lean_inc(x_10);
lean_inc(x_9);
x_424 = l_Lean_Name_mkStr3(x_9, x_10, x_422);
x_425 = l_Lean_Parser_hygieneInfo;
x_426 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_426, 0, x_425);
lean_inc(x_423);
x_427 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_427, 0, x_423);
lean_inc(x_423);
x_428 = l_Lean_Parser_registerAlias(x_423, x_424, x_426, x_427, x_418, x_421);
if (lean_obj_tag(x_428) == 0)
{
lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; 
x_429 = lean_ctor_get(x_428, 1);
lean_inc(x_429);
lean_dec(x_428);
x_430 = lean_alloc_closure((void*)(l_Lean_Parser_hygieneInfo_formatter), 5, 0);
x_431 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_431, 0, x_430);
lean_inc(x_423);
x_432 = l_Lean_PrettyPrinter_Formatter_registerAlias(x_423, x_431, x_429);
if (lean_obj_tag(x_432) == 0)
{
lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; 
x_433 = lean_ctor_get(x_432, 1);
lean_inc(x_433);
lean_dec(x_432);
x_434 = lean_alloc_closure((void*)(l_Lean_Parser_hygieneInfo_parenthesizer), 5, 0);
x_435 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_435, 0, x_434);
x_436 = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(x_423, x_435, x_433);
x_397 = x_418;
x_398 = x_419;
x_399 = x_436;
goto block_417;
}
else
{
lean_dec(x_423);
x_397 = x_418;
x_398 = x_419;
x_399 = x_432;
goto block_417;
}
}
else
{
lean_dec(x_423);
x_397 = x_418;
x_398 = x_419;
x_399 = x_428;
goto block_417;
}
}
else
{
lean_dec(x_419);
lean_dec(x_418);
lean_dec(x_312);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_420;
}
}
block_457:
{
if (lean_obj_tag(x_440) == 0)
{
lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; 
x_441 = lean_ctor_get(x_440, 1);
lean_inc(x_441);
lean_dec(x_440);
x_442 = lean_mk_string_unchecked("ident", 5, 5);
lean_inc(x_442);
x_443 = l_Lean_Name_mkStr1(x_442);
lean_inc(x_10);
lean_inc(x_9);
x_444 = l_Lean_Name_mkStr3(x_9, x_10, x_442);
x_445 = l_Lean_Parser_ident;
x_446 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_446, 0, x_445);
lean_inc(x_443);
x_447 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_447, 0, x_443);
lean_inc(x_443);
x_448 = l_Lean_Parser_registerAlias(x_443, x_444, x_446, x_447, x_438, x_441);
if (lean_obj_tag(x_448) == 0)
{
lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; 
x_449 = lean_ctor_get(x_448, 1);
lean_inc(x_449);
lean_dec(x_448);
x_450 = lean_alloc_closure((void*)(l_Lean_Parser_ident_formatter), 5, 0);
x_451 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_451, 0, x_450);
lean_inc(x_443);
x_452 = l_Lean_PrettyPrinter_Formatter_registerAlias(x_443, x_451, x_449);
if (lean_obj_tag(x_452) == 0)
{
lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; 
x_453 = lean_ctor_get(x_452, 1);
lean_inc(x_453);
lean_dec(x_452);
x_454 = lean_alloc_closure((void*)(l_Lean_Parser_ident_parenthesizer), 5, 0);
x_455 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_455, 0, x_454);
x_456 = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(x_443, x_455, x_453);
x_418 = x_438;
x_419 = x_439;
x_420 = x_456;
goto block_437;
}
else
{
lean_dec(x_443);
x_418 = x_438;
x_419 = x_439;
x_420 = x_452;
goto block_437;
}
}
else
{
lean_dec(x_443);
x_418 = x_438;
x_419 = x_439;
x_420 = x_448;
goto block_437;
}
}
else
{
lean_dec(x_439);
lean_dec(x_438);
lean_dec(x_312);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_440;
}
}
block_478:
{
if (lean_obj_tag(x_460) == 0)
{
lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; 
x_461 = lean_ctor_get(x_460, 1);
lean_inc(x_461);
lean_dec(x_460);
x_462 = lean_mk_string_unchecked("scientific", 10, 10);
x_463 = l_Lean_Name_mkStr1(x_462);
x_464 = lean_mk_string_unchecked("scientificLit", 13, 13);
lean_inc(x_10);
lean_inc(x_9);
x_465 = l_Lean_Name_mkStr3(x_9, x_10, x_464);
x_466 = l_Lean_Parser_scientificLit;
x_467 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_467, 0, x_466);
lean_inc(x_463);
x_468 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_468, 0, x_463);
lean_inc(x_463);
x_469 = l_Lean_Parser_registerAlias(x_463, x_465, x_467, x_468, x_458, x_461);
if (lean_obj_tag(x_469) == 0)
{
lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; 
x_470 = lean_ctor_get(x_469, 1);
lean_inc(x_470);
lean_dec(x_469);
x_471 = lean_alloc_closure((void*)(l_Lean_Parser_scientificLit_formatter), 5, 0);
x_472 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_472, 0, x_471);
lean_inc(x_463);
x_473 = l_Lean_PrettyPrinter_Formatter_registerAlias(x_463, x_472, x_470);
if (lean_obj_tag(x_473) == 0)
{
lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; 
x_474 = lean_ctor_get(x_473, 1);
lean_inc(x_474);
lean_dec(x_473);
x_475 = lean_alloc_closure((void*)(l_Lean_Parser_scientificLit_parenthesizer), 5, 0);
x_476 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_476, 0, x_475);
x_477 = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(x_463, x_476, x_474);
x_438 = x_458;
x_439 = x_459;
x_440 = x_477;
goto block_457;
}
else
{
lean_dec(x_463);
x_438 = x_458;
x_439 = x_459;
x_440 = x_473;
goto block_457;
}
}
else
{
lean_dec(x_463);
x_438 = x_458;
x_439 = x_459;
x_440 = x_469;
goto block_457;
}
}
else
{
lean_dec(x_459);
lean_dec(x_458);
lean_dec(x_312);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_460;
}
}
block_499:
{
if (lean_obj_tag(x_481) == 0)
{
lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; 
x_482 = lean_ctor_get(x_481, 1);
lean_inc(x_482);
lean_dec(x_481);
x_483 = lean_mk_string_unchecked("name", 4, 4);
x_484 = l_Lean_Name_mkStr1(x_483);
x_485 = lean_mk_string_unchecked("nameLit", 7, 7);
lean_inc(x_10);
lean_inc(x_9);
x_486 = l_Lean_Name_mkStr3(x_9, x_10, x_485);
x_487 = l_Lean_Parser_nameLit;
x_488 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_488, 0, x_487);
lean_inc(x_484);
x_489 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_489, 0, x_484);
lean_inc(x_484);
x_490 = l_Lean_Parser_registerAlias(x_484, x_486, x_488, x_489, x_479, x_482);
if (lean_obj_tag(x_490) == 0)
{
lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; 
x_491 = lean_ctor_get(x_490, 1);
lean_inc(x_491);
lean_dec(x_490);
x_492 = lean_alloc_closure((void*)(l_Lean_Parser_nameLit_formatter), 5, 0);
x_493 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_493, 0, x_492);
lean_inc(x_484);
x_494 = l_Lean_PrettyPrinter_Formatter_registerAlias(x_484, x_493, x_491);
if (lean_obj_tag(x_494) == 0)
{
lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; 
x_495 = lean_ctor_get(x_494, 1);
lean_inc(x_495);
lean_dec(x_494);
x_496 = lean_alloc_closure((void*)(l_Lean_Parser_nameLit_parenthesizer), 5, 0);
x_497 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_497, 0, x_496);
x_498 = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(x_484, x_497, x_495);
x_458 = x_479;
x_459 = x_480;
x_460 = x_498;
goto block_478;
}
else
{
lean_dec(x_484);
x_458 = x_479;
x_459 = x_480;
x_460 = x_494;
goto block_478;
}
}
else
{
lean_dec(x_484);
x_458 = x_479;
x_459 = x_480;
x_460 = x_490;
goto block_478;
}
}
else
{
lean_dec(x_480);
lean_dec(x_479);
lean_dec(x_312);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_481;
}
}
block_520:
{
if (lean_obj_tag(x_502) == 0)
{
lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; 
x_503 = lean_ctor_get(x_502, 1);
lean_inc(x_503);
lean_dec(x_502);
x_504 = lean_mk_string_unchecked("char", 4, 4);
x_505 = l_Lean_Name_mkStr1(x_504);
x_506 = lean_mk_string_unchecked("charLit", 7, 7);
lean_inc(x_10);
lean_inc(x_9);
x_507 = l_Lean_Name_mkStr3(x_9, x_10, x_506);
x_508 = l_Lean_Parser_charLit;
x_509 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_509, 0, x_508);
lean_inc(x_505);
x_510 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_510, 0, x_505);
lean_inc(x_505);
x_511 = l_Lean_Parser_registerAlias(x_505, x_507, x_509, x_510, x_500, x_503);
if (lean_obj_tag(x_511) == 0)
{
lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; 
x_512 = lean_ctor_get(x_511, 1);
lean_inc(x_512);
lean_dec(x_511);
x_513 = lean_alloc_closure((void*)(l_Lean_Parser_charLit_formatter), 5, 0);
x_514 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_514, 0, x_513);
lean_inc(x_505);
x_515 = l_Lean_PrettyPrinter_Formatter_registerAlias(x_505, x_514, x_512);
if (lean_obj_tag(x_515) == 0)
{
lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; 
x_516 = lean_ctor_get(x_515, 1);
lean_inc(x_516);
lean_dec(x_515);
x_517 = lean_alloc_closure((void*)(l_Lean_Parser_charLit_parenthesizer), 5, 0);
x_518 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_518, 0, x_517);
x_519 = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(x_505, x_518, x_516);
x_479 = x_500;
x_480 = x_501;
x_481 = x_519;
goto block_499;
}
else
{
lean_dec(x_505);
x_479 = x_500;
x_480 = x_501;
x_481 = x_515;
goto block_499;
}
}
else
{
lean_dec(x_505);
x_479 = x_500;
x_480 = x_501;
x_481 = x_511;
goto block_499;
}
}
else
{
lean_dec(x_501);
lean_dec(x_500);
lean_dec(x_312);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_502;
}
}
block_541:
{
if (lean_obj_tag(x_523) == 0)
{
lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; 
x_524 = lean_ctor_get(x_523, 1);
lean_inc(x_524);
lean_dec(x_523);
x_525 = lean_mk_string_unchecked("str", 3, 3);
x_526 = l_Lean_Name_mkStr1(x_525);
x_527 = lean_mk_string_unchecked("strLit", 6, 6);
lean_inc(x_10);
lean_inc(x_9);
x_528 = l_Lean_Name_mkStr3(x_9, x_10, x_527);
x_529 = l_Lean_Parser_strLit;
x_530 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_530, 0, x_529);
lean_inc(x_526);
x_531 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_531, 0, x_526);
lean_inc(x_526);
x_532 = l_Lean_Parser_registerAlias(x_526, x_528, x_530, x_531, x_521, x_524);
if (lean_obj_tag(x_532) == 0)
{
lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; 
x_533 = lean_ctor_get(x_532, 1);
lean_inc(x_533);
lean_dec(x_532);
x_534 = lean_alloc_closure((void*)(l_Lean_Parser_strLit_formatter), 5, 0);
x_535 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_535, 0, x_534);
lean_inc(x_526);
x_536 = l_Lean_PrettyPrinter_Formatter_registerAlias(x_526, x_535, x_533);
if (lean_obj_tag(x_536) == 0)
{
lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; 
x_537 = lean_ctor_get(x_536, 1);
lean_inc(x_537);
lean_dec(x_536);
x_538 = lean_alloc_closure((void*)(l_Lean_Parser_strLit_parenthesizer), 5, 0);
x_539 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_539, 0, x_538);
x_540 = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(x_526, x_539, x_537);
x_500 = x_521;
x_501 = x_522;
x_502 = x_540;
goto block_520;
}
else
{
lean_dec(x_526);
x_500 = x_521;
x_501 = x_522;
x_502 = x_536;
goto block_520;
}
}
else
{
lean_dec(x_526);
x_500 = x_521;
x_501 = x_522;
x_502 = x_532;
goto block_520;
}
}
else
{
lean_dec(x_522);
lean_dec(x_521);
lean_dec(x_312);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_523;
}
}
block_564:
{
if (lean_obj_tag(x_542) == 0)
{
lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; uint8_t x_554; lean_object* x_555; 
x_543 = lean_ctor_get(x_542, 1);
lean_inc(x_543);
lean_dec(x_542);
x_544 = lean_mk_string_unchecked("num", 3, 3);
x_545 = l_Lean_Name_mkStr1(x_544);
x_546 = lean_mk_string_unchecked("numLit", 6, 6);
lean_inc(x_10);
lean_inc(x_9);
x_547 = l_Lean_Name_mkStr3(x_9, x_10, x_546);
x_548 = l_Lean_Parser_numLit;
x_549 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_549, 0, x_548);
lean_inc(x_545);
x_550 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_550, 0, x_545);
x_551 = lean_unsigned_to_nat(1u);
x_552 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_552, 0, x_551);
lean_inc(x_552);
x_553 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_553, 0, x_173);
lean_ctor_set(x_553, 1, x_552);
x_554 = lean_unbox(x_311);
lean_ctor_set_uint8(x_553, sizeof(void*)*2, x_554);
lean_inc(x_545);
x_555 = l_Lean_Parser_registerAlias(x_545, x_547, x_549, x_550, x_553, x_543);
if (lean_obj_tag(x_555) == 0)
{
lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; 
x_556 = lean_ctor_get(x_555, 1);
lean_inc(x_556);
lean_dec(x_555);
x_557 = lean_alloc_closure((void*)(l_Lean_Parser_numLit_formatter), 5, 0);
x_558 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_558, 0, x_557);
lean_inc(x_545);
x_559 = l_Lean_PrettyPrinter_Formatter_registerAlias(x_545, x_558, x_556);
if (lean_obj_tag(x_559) == 0)
{
lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; 
x_560 = lean_ctor_get(x_559, 1);
lean_inc(x_560);
lean_dec(x_559);
x_561 = lean_alloc_closure((void*)(l_Lean_Parser_numLit_parenthesizer), 5, 0);
x_562 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_562, 0, x_561);
x_563 = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(x_545, x_562, x_560);
x_521 = x_553;
x_522 = x_552;
x_523 = x_563;
goto block_541;
}
else
{
lean_dec(x_545);
x_521 = x_553;
x_522 = x_552;
x_523 = x_559;
goto block_541;
}
}
else
{
lean_dec(x_545);
x_521 = x_553;
x_522 = x_552;
x_523 = x_555;
goto block_541;
}
}
else
{
lean_dec(x_312);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_542;
}
}
block_584:
{
if (lean_obj_tag(x_565) == 0)
{
lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; 
x_566 = lean_ctor_get(x_565, 1);
lean_inc(x_566);
lean_dec(x_565);
x_567 = lean_mk_string_unchecked("linebreak", 9, 9);
x_568 = l_Lean_Name_mkStr1(x_567);
x_569 = lean_mk_string_unchecked("checkLinebreakBefore", 20, 20);
lean_inc(x_10);
lean_inc(x_9);
x_570 = l_Lean_Name_mkStr3(x_9, x_10, x_569);
x_571 = lean_mk_string_unchecked("line break", 10, 10);
x_572 = l_Lean_Parser_checkLinebreakBefore(x_571);
x_573 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_573, 0, x_572);
lean_inc(x_570);
x_574 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_574, 0, x_570);
lean_inc(x_568);
x_575 = l_Lean_Parser_registerAlias(x_568, x_570, x_573, x_574, x_312, x_566);
if (lean_obj_tag(x_575) == 0)
{
lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; 
x_576 = lean_ctor_get(x_575, 1);
lean_inc(x_576);
lean_dec(x_575);
x_577 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkLinebreakBefore_formatter___boxed), 5, 0);
x_578 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_578, 0, x_577);
lean_inc(x_568);
x_579 = l_Lean_PrettyPrinter_Formatter_registerAlias(x_568, x_578, x_576);
if (lean_obj_tag(x_579) == 0)
{
lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; 
x_580 = lean_ctor_get(x_579, 1);
lean_inc(x_580);
lean_dec(x_579);
x_581 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkLinebreakBefore_parenthesizer___boxed), 5, 0);
x_582 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_582, 0, x_581);
x_583 = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(x_568, x_582, x_580);
x_542 = x_583;
goto block_564;
}
else
{
lean_dec(x_568);
x_542 = x_579;
goto block_564;
}
}
else
{
lean_dec(x_568);
x_542 = x_575;
goto block_564;
}
}
else
{
lean_dec(x_312);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_565;
}
}
block_604:
{
if (lean_obj_tag(x_585) == 0)
{
lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; 
x_586 = lean_ctor_get(x_585, 1);
lean_inc(x_586);
lean_dec(x_585);
x_587 = lean_mk_string_unchecked("noWs", 4, 4);
x_588 = l_Lean_Name_mkStr1(x_587);
x_589 = lean_mk_string_unchecked("checkNoWsBefore", 15, 15);
lean_inc(x_10);
lean_inc(x_9);
x_590 = l_Lean_Name_mkStr3(x_9, x_10, x_589);
x_591 = lean_mk_string_unchecked("no space before", 15, 15);
x_592 = l_Lean_Parser_checkNoWsBefore(x_591);
x_593 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_593, 0, x_592);
lean_inc(x_590);
x_594 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_594, 0, x_590);
lean_inc(x_588);
x_595 = l_Lean_Parser_registerAlias(x_588, x_590, x_593, x_594, x_312, x_586);
if (lean_obj_tag(x_595) == 0)
{
lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; 
x_596 = lean_ctor_get(x_595, 1);
lean_inc(x_596);
lean_dec(x_595);
x_597 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkNoWsBefore_formatter___boxed), 5, 0);
x_598 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_598, 0, x_597);
lean_inc(x_588);
x_599 = l_Lean_PrettyPrinter_Formatter_registerAlias(x_588, x_598, x_596);
if (lean_obj_tag(x_599) == 0)
{
lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; 
x_600 = lean_ctor_get(x_599, 1);
lean_inc(x_600);
lean_dec(x_599);
x_601 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkNoWsBefore_parenthesizer___boxed), 5, 0);
x_602 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_602, 0, x_601);
x_603 = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(x_588, x_602, x_600);
x_565 = x_603;
goto block_584;
}
else
{
lean_dec(x_588);
x_565 = x_599;
goto block_584;
}
}
else
{
lean_dec(x_588);
x_565 = x_595;
goto block_584;
}
}
else
{
lean_dec(x_312);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_585;
}
}
}
}
LEAN_EXPORT lean_object* lean_mk_antiquot_parenthesizer(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Parser_mkAntiquot_parenthesizer(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_mkAntiquot_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_Term_ident_parenthesizer(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_Term_ident_parenthesizer(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = lean_alloc_closure((void*)(l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___lam__0), 5, 0);
x_3 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_4 = lean_mk_string_unchecked("ident", 5, 5);
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_Term_num_parenthesizer(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer__1___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_Term_num_parenthesizer(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = lean_alloc_closure((void*)(l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer__1___lam__0), 5, 0);
x_3 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_4 = lean_mk_string_unchecked("num", 3, 3);
x_5 = l_Lean_Name_mkStr1(x_4);
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("PrettyPrinter", 13, 13);
x_8 = lean_mk_string_unchecked("Parenthesizer", 13, 13);
x_9 = lean_mk_string_unchecked("numLit", 6, 6);
x_10 = lean_mk_string_unchecked("parenthesizer", 13, 13);
x_11 = l_Lean_Name_mkStr5(x_6, x_7, x_8, x_9, x_10);
x_12 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_3, x_5, x_11, x_2, x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_Term_scientific_parenthesizer(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer__1___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_Term_scientific_parenthesizer(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = lean_alloc_closure((void*)(l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer__1___lam__0), 5, 0);
x_3 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_4 = lean_mk_string_unchecked("scientific", 10, 10);
x_5 = l_Lean_Name_mkStr1(x_4);
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("PrettyPrinter", 13, 13);
x_8 = lean_mk_string_unchecked("Parenthesizer", 13, 13);
x_9 = lean_mk_string_unchecked("scientificLit", 13, 13);
x_10 = lean_mk_string_unchecked("parenthesizer", 13, 13);
x_11 = l_Lean_Name_mkStr5(x_6, x_7, x_8, x_9, x_10);
x_12 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_3, x_5, x_11, x_2, x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_Term_char_parenthesizer(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer__1___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_Term_char_parenthesizer(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = lean_alloc_closure((void*)(l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer__1___lam__0), 5, 0);
x_3 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_4 = lean_mk_string_unchecked("char", 4, 4);
x_5 = l_Lean_Name_mkStr1(x_4);
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("PrettyPrinter", 13, 13);
x_8 = lean_mk_string_unchecked("Parenthesizer", 13, 13);
x_9 = lean_mk_string_unchecked("charLit", 7, 7);
x_10 = lean_mk_string_unchecked("parenthesizer", 13, 13);
x_11 = l_Lean_Name_mkStr5(x_6, x_7, x_8, x_9, x_10);
x_12 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_3, x_5, x_11, x_2, x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_Term_str_parenthesizer(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer__1___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_Term_str_parenthesizer(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = lean_alloc_closure((void*)(l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer__1___lam__0), 5, 0);
x_3 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_4 = lean_mk_string_unchecked("str", 3, 3);
x_5 = l_Lean_Name_mkStr1(x_4);
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("PrettyPrinter", 13, 13);
x_8 = lean_mk_string_unchecked("Parenthesizer", 13, 13);
x_9 = lean_mk_string_unchecked("strLit", 6, 6);
x_10 = lean_mk_string_unchecked("parenthesizer", 13, 13);
x_11 = l_Lean_Name_mkStr5(x_6, x_7, x_8, x_9, x_10);
x_12 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_3, x_5, x_11, x_2, x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* lean_pretty_printer_parenthesizer_interpret_parser_descr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_5; 
lean_dec(x_3);
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = l_Lean_PrettyPrinter_Parenthesizer_parenthesizerAliasesRef;
x_8 = l_Lean_Parser_getConstAlias(lean_box(0), x_7, x_6, x_4);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
lean_free_object(x_1);
lean_dec(x_2);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
return x_8;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_8);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_8, 0);
x_15 = lean_ctor_get(x_2, 5);
lean_inc(x_15);
lean_dec(x_2);
x_16 = lean_io_error_to_string(x_14);
lean_ctor_set_tag(x_1, 3);
lean_ctor_set(x_1, 0, x_16);
x_17 = l_Lean_MessageData_ofFormat(x_1);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set(x_8, 0, x_18);
return x_8;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_8, 0);
x_20 = lean_ctor_get(x_8, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_8);
x_21 = lean_ctor_get(x_2, 5);
lean_inc(x_21);
lean_dec(x_2);
x_22 = lean_io_error_to_string(x_19);
lean_ctor_set_tag(x_1, 3);
lean_ctor_set(x_1, 0, x_22);
x_23 = l_Lean_MessageData_ofFormat(x_1);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_20);
return x_25;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_1, 0);
lean_inc(x_26);
lean_dec(x_1);
x_27 = l_Lean_PrettyPrinter_Parenthesizer_parenthesizerAliasesRef;
x_28 = l_Lean_Parser_getConstAlias(lean_box(0), x_27, x_26, x_4);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_2);
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
if (lean_is_scalar(x_31)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_31;
}
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_33 = lean_ctor_get(x_28, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_28, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_35 = x_28;
} else {
 lean_dec_ref(x_28);
 x_35 = lean_box(0);
}
x_36 = lean_ctor_get(x_2, 5);
lean_inc(x_36);
lean_dec(x_2);
x_37 = lean_io_error_to_string(x_33);
x_38 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_39 = l_Lean_MessageData_ofFormat(x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_36);
lean_ctor_set(x_40, 1, x_39);
if (lean_is_scalar(x_35)) {
 x_41 = lean_alloc_ctor(1, 2, 0);
} else {
 x_41 = x_35;
}
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_34);
return x_41;
}
}
}
case 1:
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_1);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_1, 0);
x_44 = lean_ctor_get(x_1, 1);
x_45 = l_Lean_PrettyPrinter_Parenthesizer_parenthesizerAliasesRef;
x_46 = l_Lean_Parser_getUnaryAlias___redArg(x_45, x_43, x_4);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_free_object(x_1);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_pretty_printer_parenthesizer_interpret_parser_descr(x_44, x_2, x_3, x_48);
if (lean_obj_tag(x_49) == 0)
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_49, 0);
x_52 = lean_apply_1(x_47, x_51);
lean_ctor_set(x_49, 0, x_52);
return x_49;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_49, 0);
x_54 = lean_ctor_get(x_49, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_49);
x_55 = lean_apply_1(x_47, x_53);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
}
else
{
lean_dec(x_47);
return x_49;
}
}
else
{
uint8_t x_57; 
lean_dec(x_44);
lean_dec(x_3);
x_57 = !lean_is_exclusive(x_46);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_58 = lean_ctor_get(x_46, 0);
x_59 = lean_ctor_get(x_2, 5);
lean_inc(x_59);
lean_dec(x_2);
x_60 = lean_io_error_to_string(x_58);
x_61 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_61, 0, x_60);
x_62 = l_Lean_MessageData_ofFormat(x_61);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_62);
lean_ctor_set(x_1, 0, x_59);
lean_ctor_set(x_46, 0, x_1);
return x_46;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_63 = lean_ctor_get(x_46, 0);
x_64 = lean_ctor_get(x_46, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_46);
x_65 = lean_ctor_get(x_2, 5);
lean_inc(x_65);
lean_dec(x_2);
x_66 = lean_io_error_to_string(x_63);
x_67 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_67, 0, x_66);
x_68 = l_Lean_MessageData_ofFormat(x_67);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_68);
lean_ctor_set(x_1, 0, x_65);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_1);
lean_ctor_set(x_69, 1, x_64);
return x_69;
}
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_70 = lean_ctor_get(x_1, 0);
x_71 = lean_ctor_get(x_1, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_1);
x_72 = l_Lean_PrettyPrinter_Parenthesizer_parenthesizerAliasesRef;
x_73 = l_Lean_Parser_getUnaryAlias___redArg(x_72, x_70, x_4);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_76 = lean_pretty_printer_parenthesizer_interpret_parser_descr(x_71, x_2, x_3, x_75);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_79 = x_76;
} else {
 lean_dec_ref(x_76);
 x_79 = lean_box(0);
}
x_80 = lean_apply_1(x_74, x_77);
if (lean_is_scalar(x_79)) {
 x_81 = lean_alloc_ctor(0, 2, 0);
} else {
 x_81 = x_79;
}
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_78);
return x_81;
}
else
{
lean_dec(x_74);
return x_76;
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_71);
lean_dec(x_3);
x_82 = lean_ctor_get(x_73, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_73, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_84 = x_73;
} else {
 lean_dec_ref(x_73);
 x_84 = lean_box(0);
}
x_85 = lean_ctor_get(x_2, 5);
lean_inc(x_85);
lean_dec(x_2);
x_86 = lean_io_error_to_string(x_82);
x_87 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_87, 0, x_86);
x_88 = l_Lean_MessageData_ofFormat(x_87);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_85);
lean_ctor_set(x_89, 1, x_88);
if (lean_is_scalar(x_84)) {
 x_90 = lean_alloc_ctor(1, 2, 0);
} else {
 x_90 = x_84;
}
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_83);
return x_90;
}
}
}
case 2:
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_91 = lean_ctor_get(x_1, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_1, 1);
lean_inc(x_92);
x_93 = lean_ctor_get(x_1, 2);
lean_inc(x_93);
lean_dec(x_1);
x_94 = l_Lean_PrettyPrinter_Parenthesizer_parenthesizerAliasesRef;
x_95 = l_Lean_Parser_getBinaryAlias(lean_box(0), x_94, x_91, x_4);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
lean_inc(x_3);
lean_inc(x_2);
x_98 = lean_pretty_printer_parenthesizer_interpret_parser_descr(x_92, x_2, x_3, x_97);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
x_101 = lean_pretty_printer_parenthesizer_interpret_parser_descr(x_93, x_2, x_3, x_100);
if (lean_obj_tag(x_101) == 0)
{
uint8_t x_102; 
x_102 = !lean_is_exclusive(x_101);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; 
x_103 = lean_ctor_get(x_101, 0);
x_104 = lean_apply_2(x_96, x_99, x_103);
lean_ctor_set(x_101, 0, x_104);
return x_101;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_105 = lean_ctor_get(x_101, 0);
x_106 = lean_ctor_get(x_101, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_101);
x_107 = lean_apply_2(x_96, x_99, x_105);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_106);
return x_108;
}
}
else
{
lean_dec(x_99);
lean_dec(x_96);
return x_101;
}
}
else
{
lean_dec(x_96);
lean_dec(x_93);
lean_dec(x_3);
lean_dec(x_2);
return x_98;
}
}
else
{
uint8_t x_109; 
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_3);
x_109 = !lean_is_exclusive(x_95);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_110 = lean_ctor_get(x_95, 0);
x_111 = lean_ctor_get(x_2, 5);
lean_inc(x_111);
lean_dec(x_2);
x_112 = lean_io_error_to_string(x_110);
x_113 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_113, 0, x_112);
x_114 = l_Lean_MessageData_ofFormat(x_113);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_111);
lean_ctor_set(x_115, 1, x_114);
lean_ctor_set(x_95, 0, x_115);
return x_95;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_116 = lean_ctor_get(x_95, 0);
x_117 = lean_ctor_get(x_95, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_95);
x_118 = lean_ctor_get(x_2, 5);
lean_inc(x_118);
lean_dec(x_2);
x_119 = lean_io_error_to_string(x_116);
x_120 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_120, 0, x_119);
x_121 = l_Lean_MessageData_ofFormat(x_120);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_118);
lean_ctor_set(x_122, 1, x_121);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_117);
return x_123;
}
}
}
case 3:
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_124 = lean_ctor_get(x_1, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_1, 1);
lean_inc(x_125);
x_126 = lean_ctor_get(x_1, 2);
lean_inc(x_126);
lean_dec(x_1);
x_127 = lean_pretty_printer_parenthesizer_interpret_parser_descr(x_126, x_2, x_3, x_4);
if (lean_obj_tag(x_127) == 0)
{
uint8_t x_128; 
x_128 = !lean_is_exclusive(x_127);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; 
x_129 = lean_ctor_get(x_127, 0);
x_130 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer), 8, 3);
lean_closure_set(x_130, 0, x_124);
lean_closure_set(x_130, 1, x_125);
lean_closure_set(x_130, 2, x_129);
lean_ctor_set(x_127, 0, x_130);
return x_127;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_131 = lean_ctor_get(x_127, 0);
x_132 = lean_ctor_get(x_127, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_127);
x_133 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer), 8, 3);
lean_closure_set(x_133, 0, x_124);
lean_closure_set(x_133, 1, x_125);
lean_closure_set(x_133, 2, x_131);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_132);
return x_134;
}
}
else
{
lean_dec(x_125);
lean_dec(x_124);
return x_127;
}
}
case 4:
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_135 = lean_ctor_get(x_1, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_1, 1);
lean_inc(x_136);
x_137 = lean_ctor_get(x_1, 2);
lean_inc(x_137);
x_138 = lean_ctor_get(x_1, 3);
lean_inc(x_138);
lean_dec(x_1);
x_139 = lean_pretty_printer_parenthesizer_interpret_parser_descr(x_138, x_2, x_3, x_4);
if (lean_obj_tag(x_139) == 0)
{
uint8_t x_140; 
x_140 = !lean_is_exclusive(x_139);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; 
x_141 = lean_ctor_get(x_139, 0);
x_142 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer), 9, 4);
lean_closure_set(x_142, 0, x_135);
lean_closure_set(x_142, 1, x_136);
lean_closure_set(x_142, 2, x_137);
lean_closure_set(x_142, 3, x_141);
lean_ctor_set(x_139, 0, x_142);
return x_139;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_143 = lean_ctor_get(x_139, 0);
x_144 = lean_ctor_get(x_139, 1);
lean_inc(x_144);
lean_inc(x_143);
lean_dec(x_139);
x_145 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer), 9, 4);
lean_closure_set(x_145, 0, x_135);
lean_closure_set(x_145, 1, x_136);
lean_closure_set(x_145, 2, x_137);
lean_closure_set(x_145, 3, x_143);
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_144);
return x_146;
}
}
else
{
lean_dec(x_137);
lean_dec(x_136);
lean_dec(x_135);
return x_139;
}
}
case 5:
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; 
lean_dec(x_3);
lean_dec(x_2);
x_147 = lean_ctor_get(x_1, 0);
lean_inc(x_147);
lean_dec(x_1);
x_148 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___boxed), 6, 1);
lean_closure_set(x_148, 0, x_147);
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_4);
return x_149;
}
case 6:
{
lean_object* x_150; uint8_t x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
lean_dec(x_3);
lean_dec(x_2);
x_150 = lean_ctor_get(x_1, 0);
lean_inc(x_150);
x_151 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_152 = lean_box(x_151);
x_153 = lean_alloc_closure((void*)(l_Lean_Parser_nonReservedSymbol_parenthesizer___boxed), 7, 2);
lean_closure_set(x_153, 0, x_150);
lean_closure_set(x_153, 1, x_152);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_4);
return x_154;
}
case 7:
{
uint8_t x_155; 
lean_dec(x_3);
lean_dec(x_2);
x_155 = !lean_is_exclusive(x_1);
if (x_155 == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_156 = lean_ctor_get(x_1, 0);
x_157 = lean_ctor_get(x_1, 1);
x_158 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer), 7, 2);
lean_closure_set(x_158, 0, x_156);
lean_closure_set(x_158, 1, x_157);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_4);
lean_ctor_set(x_1, 0, x_158);
return x_1;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_159 = lean_ctor_get(x_1, 0);
x_160 = lean_ctor_get(x_1, 1);
lean_inc(x_160);
lean_inc(x_159);
lean_dec(x_1);
x_161 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer), 7, 2);
lean_closure_set(x_161, 0, x_159);
lean_closure_set(x_161, 1, x_160);
x_162 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_4);
return x_162;
}
}
case 8:
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_ctor_get(x_1, 0);
lean_inc(x_163);
lean_dec(x_1);
x_164 = l_Lean_PrettyPrinter_combinatorParenthesizerAttribute;
x_165 = l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg(x_164, x_163, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_165;
}
case 9:
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_166 = lean_ctor_get(x_1, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_1, 1);
lean_inc(x_167);
x_168 = lean_ctor_get(x_1, 2);
lean_inc(x_168);
lean_dec(x_1);
x_169 = lean_pretty_printer_parenthesizer_interpret_parser_descr(x_168, x_2, x_3, x_4);
if (lean_obj_tag(x_169) == 0)
{
uint8_t x_170; 
x_170 = !lean_is_exclusive(x_169);
if (x_170 == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_171 = lean_ctor_get(x_169, 0);
x_172 = lean_box(1);
x_173 = lean_box(0);
lean_inc(x_167);
x_174 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_mkAntiquot_parenthesizer_x27___boxed), 9, 4);
lean_closure_set(x_174, 0, x_166);
lean_closure_set(x_174, 1, x_167);
lean_closure_set(x_174, 2, x_172);
lean_closure_set(x_174, 3, x_173);
x_175 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer), 7, 2);
lean_closure_set(x_175, 0, x_167);
lean_closure_set(x_175, 1, x_171);
x_176 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer), 7, 2);
lean_closure_set(x_176, 0, x_174);
lean_closure_set(x_176, 1, x_175);
lean_ctor_set(x_169, 0, x_176);
return x_169;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_177 = lean_ctor_get(x_169, 0);
x_178 = lean_ctor_get(x_169, 1);
lean_inc(x_178);
lean_inc(x_177);
lean_dec(x_169);
x_179 = lean_box(1);
x_180 = lean_box(0);
lean_inc(x_167);
x_181 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_mkAntiquot_parenthesizer_x27___boxed), 9, 4);
lean_closure_set(x_181, 0, x_166);
lean_closure_set(x_181, 1, x_167);
lean_closure_set(x_181, 2, x_179);
lean_closure_set(x_181, 3, x_180);
x_182 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer), 7, 2);
lean_closure_set(x_182, 0, x_167);
lean_closure_set(x_182, 1, x_177);
x_183 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer), 7, 2);
lean_closure_set(x_183, 0, x_181);
lean_closure_set(x_183, 1, x_182);
x_184 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set(x_184, 1, x_178);
return x_184;
}
}
else
{
lean_dec(x_167);
lean_dec(x_166);
return x_169;
}
}
case 10:
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; uint8_t x_188; lean_object* x_189; 
x_185 = lean_ctor_get(x_1, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_1, 1);
lean_inc(x_186);
x_187 = lean_ctor_get(x_1, 2);
lean_inc(x_187);
x_188 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
lean_dec(x_1);
lean_inc(x_3);
lean_inc(x_2);
x_189 = lean_pretty_printer_parenthesizer_interpret_parser_descr(x_185, x_2, x_3, x_4);
if (lean_obj_tag(x_189) == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_189, 1);
lean_inc(x_191);
lean_dec(x_189);
x_192 = lean_pretty_printer_parenthesizer_interpret_parser_descr(x_187, x_2, x_3, x_191);
if (lean_obj_tag(x_192) == 0)
{
uint8_t x_193; 
x_193 = !lean_is_exclusive(x_192);
if (x_193 == 0)
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_194 = lean_ctor_get(x_192, 0);
x_195 = lean_box(x_188);
x_196 = lean_alloc_closure((void*)(l_Lean_Parser_sepBy_parenthesizer___boxed), 9, 4);
lean_closure_set(x_196, 0, x_190);
lean_closure_set(x_196, 1, x_186);
lean_closure_set(x_196, 2, x_194);
lean_closure_set(x_196, 3, x_195);
lean_ctor_set(x_192, 0, x_196);
return x_192;
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_197 = lean_ctor_get(x_192, 0);
x_198 = lean_ctor_get(x_192, 1);
lean_inc(x_198);
lean_inc(x_197);
lean_dec(x_192);
x_199 = lean_box(x_188);
x_200 = lean_alloc_closure((void*)(l_Lean_Parser_sepBy_parenthesizer___boxed), 9, 4);
lean_closure_set(x_200, 0, x_190);
lean_closure_set(x_200, 1, x_186);
lean_closure_set(x_200, 2, x_197);
lean_closure_set(x_200, 3, x_199);
x_201 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_198);
return x_201;
}
}
else
{
lean_dec(x_190);
lean_dec(x_186);
return x_192;
}
}
else
{
lean_dec(x_187);
lean_dec(x_186);
lean_dec(x_3);
lean_dec(x_2);
return x_189;
}
}
default: 
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; uint8_t x_205; lean_object* x_206; 
x_202 = lean_ctor_get(x_1, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_1, 1);
lean_inc(x_203);
x_204 = lean_ctor_get(x_1, 2);
lean_inc(x_204);
x_205 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
lean_dec(x_1);
lean_inc(x_3);
lean_inc(x_2);
x_206 = lean_pretty_printer_parenthesizer_interpret_parser_descr(x_202, x_2, x_3, x_4);
if (lean_obj_tag(x_206) == 0)
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_206, 1);
lean_inc(x_208);
lean_dec(x_206);
x_209 = lean_pretty_printer_parenthesizer_interpret_parser_descr(x_204, x_2, x_3, x_208);
if (lean_obj_tag(x_209) == 0)
{
uint8_t x_210; 
x_210 = !lean_is_exclusive(x_209);
if (x_210 == 0)
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_211 = lean_ctor_get(x_209, 0);
x_212 = lean_box(x_205);
x_213 = lean_alloc_closure((void*)(l_Lean_Parser_sepBy1_parenthesizer___boxed), 9, 4);
lean_closure_set(x_213, 0, x_207);
lean_closure_set(x_213, 1, x_203);
lean_closure_set(x_213, 2, x_211);
lean_closure_set(x_213, 3, x_212);
lean_ctor_set(x_209, 0, x_213);
return x_209;
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_214 = lean_ctor_get(x_209, 0);
x_215 = lean_ctor_get(x_209, 1);
lean_inc(x_215);
lean_inc(x_214);
lean_dec(x_209);
x_216 = lean_box(x_205);
x_217 = lean_alloc_closure((void*)(l_Lean_Parser_sepBy1_parenthesizer___boxed), 9, 4);
lean_closure_set(x_217, 0, x_207);
lean_closure_set(x_217, 1, x_203);
lean_closure_set(x_217, 2, x_214);
lean_closure_set(x_217, 3, x_216);
x_218 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_218, 0, x_217);
lean_ctor_set(x_218, 1, x_215);
return x_218;
}
}
else
{
lean_dec(x_207);
lean_dec(x_203);
return x_209;
}
}
else
{
lean_dec(x_204);
lean_dec(x_203);
lean_dec(x_3);
lean_dec(x_2);
return x_206;
}
}
}
}
}
LEAN_EXPORT lean_object* lean_mk_antiquot_formatter(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Parser_mkAntiquot_formatter(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_mkAntiquot_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_ident_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_Term_ident_formatter(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_Term_ident_formatter(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = lean_alloc_closure((void*)(l___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___lam__0), 5, 0);
x_3 = l_Lean_PrettyPrinter_formatterAttribute;
x_4 = lean_mk_string_unchecked("ident", 5, 5);
lean_inc(x_4);
x_5 = l_Lean_Name_mkStr1(x_4);
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("PrettyPrinter", 13, 13);
x_8 = lean_mk_string_unchecked("Formatter", 9, 9);
x_9 = lean_mk_string_unchecked("formatter", 9, 9);
x_10 = l_Lean_Name_mkStr5(x_6, x_7, x_8, x_4, x_9);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_3, x_5, x_10, x_2, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_numLit_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_Term_num_formatter(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_PrettyPrinter_Formatter_numLit_formatter__1___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_Term_num_formatter(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_PrettyPrinter_Formatter_numLit_formatter__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = lean_alloc_closure((void*)(l___regBuiltin_Lean_PrettyPrinter_Formatter_numLit_formatter__1___lam__0), 5, 0);
x_3 = l_Lean_PrettyPrinter_formatterAttribute;
x_4 = lean_mk_string_unchecked("num", 3, 3);
x_5 = l_Lean_Name_mkStr1(x_4);
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("PrettyPrinter", 13, 13);
x_8 = lean_mk_string_unchecked("Formatter", 9, 9);
x_9 = lean_mk_string_unchecked("numLit", 6, 6);
x_10 = lean_mk_string_unchecked("formatter", 9, 9);
x_11 = l_Lean_Name_mkStr5(x_6, x_7, x_8, x_9, x_10);
x_12 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_3, x_5, x_11, x_2, x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_scientificLit_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_Term_scientific_formatter(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_PrettyPrinter_Formatter_scientificLit_formatter__1___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_Term_scientific_formatter(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_PrettyPrinter_Formatter_scientificLit_formatter__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = lean_alloc_closure((void*)(l___regBuiltin_Lean_PrettyPrinter_Formatter_scientificLit_formatter__1___lam__0), 5, 0);
x_3 = l_Lean_PrettyPrinter_formatterAttribute;
x_4 = lean_mk_string_unchecked("scientific", 10, 10);
x_5 = l_Lean_Name_mkStr1(x_4);
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("PrettyPrinter", 13, 13);
x_8 = lean_mk_string_unchecked("Formatter", 9, 9);
x_9 = lean_mk_string_unchecked("scientificLit", 13, 13);
x_10 = lean_mk_string_unchecked("formatter", 9, 9);
x_11 = l_Lean_Name_mkStr5(x_6, x_7, x_8, x_9, x_10);
x_12 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_3, x_5, x_11, x_2, x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_charLit_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_Term_char_formatter(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_PrettyPrinter_Formatter_charLit_formatter__1___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_Term_char_formatter(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_PrettyPrinter_Formatter_charLit_formatter__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = lean_alloc_closure((void*)(l___regBuiltin_Lean_PrettyPrinter_Formatter_charLit_formatter__1___lam__0), 5, 0);
x_3 = l_Lean_PrettyPrinter_formatterAttribute;
x_4 = lean_mk_string_unchecked("char", 4, 4);
x_5 = l_Lean_Name_mkStr1(x_4);
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("PrettyPrinter", 13, 13);
x_8 = lean_mk_string_unchecked("Formatter", 9, 9);
x_9 = lean_mk_string_unchecked("charLit", 7, 7);
x_10 = lean_mk_string_unchecked("formatter", 9, 9);
x_11 = l_Lean_Name_mkStr5(x_6, x_7, x_8, x_9, x_10);
x_12 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_3, x_5, x_11, x_2, x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_strLit_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_Term_str_formatter(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_PrettyPrinter_Formatter_strLit_formatter__1___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_Term_str_formatter(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_PrettyPrinter_Formatter_strLit_formatter__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = lean_alloc_closure((void*)(l___regBuiltin_Lean_PrettyPrinter_Formatter_strLit_formatter__1___lam__0), 5, 0);
x_3 = l_Lean_PrettyPrinter_formatterAttribute;
x_4 = lean_mk_string_unchecked("str", 3, 3);
x_5 = l_Lean_Name_mkStr1(x_4);
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("PrettyPrinter", 13, 13);
x_8 = lean_mk_string_unchecked("Formatter", 9, 9);
x_9 = lean_mk_string_unchecked("strLit", 6, 6);
x_10 = lean_mk_string_unchecked("formatter", 9, 9);
x_11 = l_Lean_Name_mkStr5(x_6, x_7, x_8, x_9, x_10);
x_12 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_3, x_5, x_11, x_2, x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* lean_pretty_printer_formatter_interpret_parser_descr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_5; 
lean_dec(x_3);
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = l_Lean_PrettyPrinter_Formatter_formatterAliasesRef;
x_8 = l_Lean_Parser_getConstAlias(lean_box(0), x_7, x_6, x_4);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
lean_free_object(x_1);
lean_dec(x_2);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
return x_8;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_8);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_8, 0);
x_15 = lean_ctor_get(x_2, 5);
lean_inc(x_15);
lean_dec(x_2);
x_16 = lean_io_error_to_string(x_14);
lean_ctor_set_tag(x_1, 3);
lean_ctor_set(x_1, 0, x_16);
x_17 = l_Lean_MessageData_ofFormat(x_1);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set(x_8, 0, x_18);
return x_8;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_8, 0);
x_20 = lean_ctor_get(x_8, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_8);
x_21 = lean_ctor_get(x_2, 5);
lean_inc(x_21);
lean_dec(x_2);
x_22 = lean_io_error_to_string(x_19);
lean_ctor_set_tag(x_1, 3);
lean_ctor_set(x_1, 0, x_22);
x_23 = l_Lean_MessageData_ofFormat(x_1);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_20);
return x_25;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_1, 0);
lean_inc(x_26);
lean_dec(x_1);
x_27 = l_Lean_PrettyPrinter_Formatter_formatterAliasesRef;
x_28 = l_Lean_Parser_getConstAlias(lean_box(0), x_27, x_26, x_4);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_2);
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
if (lean_is_scalar(x_31)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_31;
}
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_33 = lean_ctor_get(x_28, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_28, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_35 = x_28;
} else {
 lean_dec_ref(x_28);
 x_35 = lean_box(0);
}
x_36 = lean_ctor_get(x_2, 5);
lean_inc(x_36);
lean_dec(x_2);
x_37 = lean_io_error_to_string(x_33);
x_38 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_39 = l_Lean_MessageData_ofFormat(x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_36);
lean_ctor_set(x_40, 1, x_39);
if (lean_is_scalar(x_35)) {
 x_41 = lean_alloc_ctor(1, 2, 0);
} else {
 x_41 = x_35;
}
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_34);
return x_41;
}
}
}
case 1:
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_1);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_1, 0);
x_44 = lean_ctor_get(x_1, 1);
x_45 = l_Lean_PrettyPrinter_Formatter_formatterAliasesRef;
x_46 = l_Lean_Parser_getUnaryAlias___redArg(x_45, x_43, x_4);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_free_object(x_1);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_pretty_printer_formatter_interpret_parser_descr(x_44, x_2, x_3, x_48);
if (lean_obj_tag(x_49) == 0)
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_49, 0);
x_52 = lean_apply_1(x_47, x_51);
lean_ctor_set(x_49, 0, x_52);
return x_49;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_49, 0);
x_54 = lean_ctor_get(x_49, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_49);
x_55 = lean_apply_1(x_47, x_53);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
}
else
{
lean_dec(x_47);
return x_49;
}
}
else
{
uint8_t x_57; 
lean_dec(x_44);
lean_dec(x_3);
x_57 = !lean_is_exclusive(x_46);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_58 = lean_ctor_get(x_46, 0);
x_59 = lean_ctor_get(x_2, 5);
lean_inc(x_59);
lean_dec(x_2);
x_60 = lean_io_error_to_string(x_58);
x_61 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_61, 0, x_60);
x_62 = l_Lean_MessageData_ofFormat(x_61);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_62);
lean_ctor_set(x_1, 0, x_59);
lean_ctor_set(x_46, 0, x_1);
return x_46;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_63 = lean_ctor_get(x_46, 0);
x_64 = lean_ctor_get(x_46, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_46);
x_65 = lean_ctor_get(x_2, 5);
lean_inc(x_65);
lean_dec(x_2);
x_66 = lean_io_error_to_string(x_63);
x_67 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_67, 0, x_66);
x_68 = l_Lean_MessageData_ofFormat(x_67);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_68);
lean_ctor_set(x_1, 0, x_65);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_1);
lean_ctor_set(x_69, 1, x_64);
return x_69;
}
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_70 = lean_ctor_get(x_1, 0);
x_71 = lean_ctor_get(x_1, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_1);
x_72 = l_Lean_PrettyPrinter_Formatter_formatterAliasesRef;
x_73 = l_Lean_Parser_getUnaryAlias___redArg(x_72, x_70, x_4);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_76 = lean_pretty_printer_formatter_interpret_parser_descr(x_71, x_2, x_3, x_75);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_79 = x_76;
} else {
 lean_dec_ref(x_76);
 x_79 = lean_box(0);
}
x_80 = lean_apply_1(x_74, x_77);
if (lean_is_scalar(x_79)) {
 x_81 = lean_alloc_ctor(0, 2, 0);
} else {
 x_81 = x_79;
}
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_78);
return x_81;
}
else
{
lean_dec(x_74);
return x_76;
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_71);
lean_dec(x_3);
x_82 = lean_ctor_get(x_73, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_73, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_84 = x_73;
} else {
 lean_dec_ref(x_73);
 x_84 = lean_box(0);
}
x_85 = lean_ctor_get(x_2, 5);
lean_inc(x_85);
lean_dec(x_2);
x_86 = lean_io_error_to_string(x_82);
x_87 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_87, 0, x_86);
x_88 = l_Lean_MessageData_ofFormat(x_87);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_85);
lean_ctor_set(x_89, 1, x_88);
if (lean_is_scalar(x_84)) {
 x_90 = lean_alloc_ctor(1, 2, 0);
} else {
 x_90 = x_84;
}
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_83);
return x_90;
}
}
}
case 2:
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_91 = lean_ctor_get(x_1, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_1, 1);
lean_inc(x_92);
x_93 = lean_ctor_get(x_1, 2);
lean_inc(x_93);
lean_dec(x_1);
x_94 = l_Lean_PrettyPrinter_Formatter_formatterAliasesRef;
x_95 = l_Lean_Parser_getBinaryAlias(lean_box(0), x_94, x_91, x_4);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
lean_inc(x_3);
lean_inc(x_2);
x_98 = lean_pretty_printer_formatter_interpret_parser_descr(x_92, x_2, x_3, x_97);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
x_101 = lean_pretty_printer_formatter_interpret_parser_descr(x_93, x_2, x_3, x_100);
if (lean_obj_tag(x_101) == 0)
{
uint8_t x_102; 
x_102 = !lean_is_exclusive(x_101);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; 
x_103 = lean_ctor_get(x_101, 0);
x_104 = lean_apply_2(x_96, x_99, x_103);
lean_ctor_set(x_101, 0, x_104);
return x_101;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_105 = lean_ctor_get(x_101, 0);
x_106 = lean_ctor_get(x_101, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_101);
x_107 = lean_apply_2(x_96, x_99, x_105);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_106);
return x_108;
}
}
else
{
lean_dec(x_99);
lean_dec(x_96);
return x_101;
}
}
else
{
lean_dec(x_96);
lean_dec(x_93);
lean_dec(x_3);
lean_dec(x_2);
return x_98;
}
}
else
{
uint8_t x_109; 
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_3);
x_109 = !lean_is_exclusive(x_95);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_110 = lean_ctor_get(x_95, 0);
x_111 = lean_ctor_get(x_2, 5);
lean_inc(x_111);
lean_dec(x_2);
x_112 = lean_io_error_to_string(x_110);
x_113 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_113, 0, x_112);
x_114 = l_Lean_MessageData_ofFormat(x_113);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_111);
lean_ctor_set(x_115, 1, x_114);
lean_ctor_set(x_95, 0, x_115);
return x_95;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_116 = lean_ctor_get(x_95, 0);
x_117 = lean_ctor_get(x_95, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_95);
x_118 = lean_ctor_get(x_2, 5);
lean_inc(x_118);
lean_dec(x_2);
x_119 = lean_io_error_to_string(x_116);
x_120 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_120, 0, x_119);
x_121 = l_Lean_MessageData_ofFormat(x_120);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_118);
lean_ctor_set(x_122, 1, x_121);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_117);
return x_123;
}
}
}
case 3:
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_1, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_1, 2);
lean_inc(x_125);
lean_dec(x_1);
x_126 = lean_pretty_printer_formatter_interpret_parser_descr(x_125, x_2, x_3, x_4);
if (lean_obj_tag(x_126) == 0)
{
uint8_t x_127; 
x_127 = !lean_is_exclusive(x_126);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; 
x_128 = lean_ctor_get(x_126, 0);
x_129 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_node_formatter), 7, 2);
lean_closure_set(x_129, 0, x_124);
lean_closure_set(x_129, 1, x_128);
lean_ctor_set(x_126, 0, x_129);
return x_126;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_130 = lean_ctor_get(x_126, 0);
x_131 = lean_ctor_get(x_126, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_126);
x_132 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_node_formatter), 7, 2);
lean_closure_set(x_132, 0, x_124);
lean_closure_set(x_132, 1, x_130);
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_131);
return x_133;
}
}
else
{
lean_dec(x_124);
return x_126;
}
}
case 4:
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_134 = lean_ctor_get(x_1, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_1, 1);
lean_inc(x_135);
x_136 = lean_ctor_get(x_1, 2);
lean_inc(x_136);
x_137 = lean_ctor_get(x_1, 3);
lean_inc(x_137);
lean_dec(x_1);
x_138 = lean_pretty_printer_formatter_interpret_parser_descr(x_137, x_2, x_3, x_4);
if (lean_obj_tag(x_138) == 0)
{
uint8_t x_139; 
x_139 = !lean_is_exclusive(x_138);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; 
x_140 = lean_ctor_get(x_138, 0);
x_141 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___boxed), 9, 4);
lean_closure_set(x_141, 0, x_134);
lean_closure_set(x_141, 1, x_135);
lean_closure_set(x_141, 2, x_136);
lean_closure_set(x_141, 3, x_140);
lean_ctor_set(x_138, 0, x_141);
return x_138;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_142 = lean_ctor_get(x_138, 0);
x_143 = lean_ctor_get(x_138, 1);
lean_inc(x_143);
lean_inc(x_142);
lean_dec(x_138);
x_144 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___boxed), 9, 4);
lean_closure_set(x_144, 0, x_134);
lean_closure_set(x_144, 1, x_135);
lean_closure_set(x_144, 2, x_136);
lean_closure_set(x_144, 3, x_142);
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_143);
return x_145;
}
}
else
{
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_134);
return x_138;
}
}
case 5:
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
lean_dec(x_3);
lean_dec(x_2);
x_146 = lean_ctor_get(x_1, 0);
lean_inc(x_146);
lean_dec(x_1);
x_147 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter), 6, 1);
lean_closure_set(x_147, 0, x_146);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_4);
return x_148;
}
case 6:
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
lean_dec(x_3);
lean_dec(x_2);
x_149 = lean_ctor_get(x_1, 0);
lean_inc(x_149);
lean_dec(x_1);
x_150 = lean_box(0);
x_151 = lean_alloc_closure((void*)(l_Lean_Parser_nonReservedSymbol_formatter___boxed), 7, 2);
lean_closure_set(x_151, 0, x_149);
lean_closure_set(x_151, 1, x_150);
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_4);
return x_152;
}
case 7:
{
uint8_t x_153; 
lean_dec(x_3);
lean_dec(x_2);
x_153 = !lean_is_exclusive(x_1);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_154 = lean_ctor_get(x_1, 0);
x_155 = lean_ctor_get(x_1, 1);
lean_dec(x_155);
x_156 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_categoryParser_formatter), 6, 1);
lean_closure_set(x_156, 0, x_154);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_4);
lean_ctor_set(x_1, 0, x_156);
return x_1;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_157 = lean_ctor_get(x_1, 0);
lean_inc(x_157);
lean_dec(x_1);
x_158 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_categoryParser_formatter), 6, 1);
lean_closure_set(x_158, 0, x_157);
x_159 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_4);
return x_159;
}
}
case 8:
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_160 = lean_ctor_get(x_1, 0);
lean_inc(x_160);
lean_dec(x_1);
x_161 = l_Lean_PrettyPrinter_combinatorFormatterAttribute;
x_162 = l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg(x_161, x_160, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_162;
}
case 9:
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_163 = lean_ctor_get(x_1, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_1, 1);
lean_inc(x_164);
x_165 = lean_ctor_get(x_1, 2);
lean_inc(x_165);
lean_dec(x_1);
x_166 = lean_pretty_printer_formatter_interpret_parser_descr(x_165, x_2, x_3, x_4);
if (lean_obj_tag(x_166) == 0)
{
uint8_t x_167; 
x_167 = !lean_is_exclusive(x_166);
if (x_167 == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_168 = lean_ctor_get(x_166, 0);
x_169 = lean_box(1);
x_170 = lean_box(0);
lean_inc(x_164);
x_171 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_mkAntiquot_formatter_x27___boxed), 9, 4);
lean_closure_set(x_171, 0, x_163);
lean_closure_set(x_171, 1, x_164);
lean_closure_set(x_171, 2, x_169);
lean_closure_set(x_171, 3, x_170);
x_172 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_node_formatter), 7, 2);
lean_closure_set(x_172, 0, x_164);
lean_closure_set(x_172, 1, x_168);
x_173 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_interpretParserDescr___lam__0), 7, 2);
lean_closure_set(x_173, 0, x_171);
lean_closure_set(x_173, 1, x_172);
lean_ctor_set(x_166, 0, x_173);
return x_166;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_174 = lean_ctor_get(x_166, 0);
x_175 = lean_ctor_get(x_166, 1);
lean_inc(x_175);
lean_inc(x_174);
lean_dec(x_166);
x_176 = lean_box(1);
x_177 = lean_box(0);
lean_inc(x_164);
x_178 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_mkAntiquot_formatter_x27___boxed), 9, 4);
lean_closure_set(x_178, 0, x_163);
lean_closure_set(x_178, 1, x_164);
lean_closure_set(x_178, 2, x_176);
lean_closure_set(x_178, 3, x_177);
x_179 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_node_formatter), 7, 2);
lean_closure_set(x_179, 0, x_164);
lean_closure_set(x_179, 1, x_174);
x_180 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_interpretParserDescr___lam__0), 7, 2);
lean_closure_set(x_180, 0, x_178);
lean_closure_set(x_180, 1, x_179);
x_181 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_175);
return x_181;
}
}
else
{
lean_dec(x_164);
lean_dec(x_163);
return x_166;
}
}
case 10:
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; uint8_t x_185; lean_object* x_186; 
x_182 = lean_ctor_get(x_1, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_1, 1);
lean_inc(x_183);
x_184 = lean_ctor_get(x_1, 2);
lean_inc(x_184);
x_185 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
lean_dec(x_1);
lean_inc(x_3);
lean_inc(x_2);
x_186 = lean_pretty_printer_formatter_interpret_parser_descr(x_182, x_2, x_3, x_4);
if (lean_obj_tag(x_186) == 0)
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_186, 1);
lean_inc(x_188);
lean_dec(x_186);
x_189 = lean_pretty_printer_formatter_interpret_parser_descr(x_184, x_2, x_3, x_188);
if (lean_obj_tag(x_189) == 0)
{
uint8_t x_190; 
x_190 = !lean_is_exclusive(x_189);
if (x_190 == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_191 = lean_ctor_get(x_189, 0);
x_192 = lean_box(x_185);
x_193 = lean_alloc_closure((void*)(l_Lean_Parser_sepBy_formatter___boxed), 9, 4);
lean_closure_set(x_193, 0, x_187);
lean_closure_set(x_193, 1, x_183);
lean_closure_set(x_193, 2, x_191);
lean_closure_set(x_193, 3, x_192);
lean_ctor_set(x_189, 0, x_193);
return x_189;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_194 = lean_ctor_get(x_189, 0);
x_195 = lean_ctor_get(x_189, 1);
lean_inc(x_195);
lean_inc(x_194);
lean_dec(x_189);
x_196 = lean_box(x_185);
x_197 = lean_alloc_closure((void*)(l_Lean_Parser_sepBy_formatter___boxed), 9, 4);
lean_closure_set(x_197, 0, x_187);
lean_closure_set(x_197, 1, x_183);
lean_closure_set(x_197, 2, x_194);
lean_closure_set(x_197, 3, x_196);
x_198 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_195);
return x_198;
}
}
else
{
lean_dec(x_187);
lean_dec(x_183);
return x_189;
}
}
else
{
lean_dec(x_184);
lean_dec(x_183);
lean_dec(x_3);
lean_dec(x_2);
return x_186;
}
}
default: 
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; uint8_t x_202; lean_object* x_203; 
x_199 = lean_ctor_get(x_1, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_1, 1);
lean_inc(x_200);
x_201 = lean_ctor_get(x_1, 2);
lean_inc(x_201);
x_202 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
lean_dec(x_1);
lean_inc(x_3);
lean_inc(x_2);
x_203 = lean_pretty_printer_formatter_interpret_parser_descr(x_199, x_2, x_3, x_4);
if (lean_obj_tag(x_203) == 0)
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_204 = lean_ctor_get(x_203, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_203, 1);
lean_inc(x_205);
lean_dec(x_203);
x_206 = lean_pretty_printer_formatter_interpret_parser_descr(x_201, x_2, x_3, x_205);
if (lean_obj_tag(x_206) == 0)
{
uint8_t x_207; 
x_207 = !lean_is_exclusive(x_206);
if (x_207 == 0)
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_208 = lean_ctor_get(x_206, 0);
x_209 = lean_box(x_202);
x_210 = lean_alloc_closure((void*)(l_Lean_Parser_sepBy1_formatter___boxed), 9, 4);
lean_closure_set(x_210, 0, x_204);
lean_closure_set(x_210, 1, x_200);
lean_closure_set(x_210, 2, x_208);
lean_closure_set(x_210, 3, x_209);
lean_ctor_set(x_206, 0, x_210);
return x_206;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_211 = lean_ctor_get(x_206, 0);
x_212 = lean_ctor_get(x_206, 1);
lean_inc(x_212);
lean_inc(x_211);
lean_dec(x_206);
x_213 = lean_box(x_202);
x_214 = lean_alloc_closure((void*)(l_Lean_Parser_sepBy1_formatter___boxed), 9, 4);
lean_closure_set(x_214, 0, x_204);
lean_closure_set(x_214, 1, x_200);
lean_closure_set(x_214, 2, x_211);
lean_closure_set(x_214, 3, x_213);
x_215 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_215, 0, x_214);
lean_ctor_set(x_215, 1, x_212);
return x_215;
}
}
else
{
lean_dec(x_204);
lean_dec(x_200);
return x_206;
}
}
else
{
lean_dec(x_201);
lean_dec(x_200);
lean_dec(x_3);
lean_dec(x_2);
return x_203;
}
}
}
}
}
lean_object* initialize_Lean_Parser_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Parser_Level(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Parser_Term(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Parser_Tactic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Parser_Command(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Parser_Module(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Parser_Syntax(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Parser_Do(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Parser_Tactic_Doc(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Parser(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Parser_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Level(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Term(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Tactic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Command(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Module(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Syntax(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Do(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Tactic_Doc(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
if (builtin) {res = l_Lean_Parser_initFn____x40_Lean_Parser___hyg_7_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_PrettyPrinter_Formatter_numLit_formatter__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_PrettyPrinter_Formatter_scientificLit_formatter__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_PrettyPrinter_Formatter_charLit_formatter__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_PrettyPrinter_Formatter_strLit_formatter__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
