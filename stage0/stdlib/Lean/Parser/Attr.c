// Lean compiler output
// Module: Lean.Parser.Attr
// Imports: Lean.Parser.Basic Lean.Parser.Extra
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
lean_object* l_Lean_Parser_checkPrec(lean_object*);
lean_object* l_Lean_Parser_many1_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Attr_tactic__tag__1(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Attr_tactic__alt_docString__1(lean_object*);
lean_object* l_Lean_Parser_optional_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_registerBuiltinParserAttribute(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Attr_export__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_default__instance_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkAntiquot_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_recursor_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__1(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Attr_tactic__tag_parenthesizer__1(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Attr_class__1(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_orelse_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Attr_tactic__tag_docString__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Attr___hyg_3_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_attrParser(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_priorityParser_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_checkPrec_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_many_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_leadingNode(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_categoryParser(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Attr_default__instance_declRange__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Priority_numPrio_parenthesizer___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_tactic__tag;
lean_object* l_Lean_Parser_optional(lean_object*);
lean_object* l_Lean_Parser_nonReservedSymbol(lean_object*, uint8_t);
extern lean_object* l_Lean_Parser_strLit;
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_simple_parenthesizer___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Attr_specialize_formatter__1(lean_object*);
lean_object* l_Lean_Parser_orelse(lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_specialize;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Attr_class_declRange__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_simple;
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Attr_macro_formatter__1(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Attr_tactic__tag_formatter__1(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Attr_recursor_formatter__1(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Attr_export_formatter__1(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Attr_macro__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_simple_formatter___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_priorityParser_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_class;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Attr_class_parenthesizer__1(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Priority_numPrio_declRange__1(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_extern_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Attr_extern_parenthesizer__1(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_skip_parenthesizer___redArg(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Attr_simple_formatter__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_tactic__alt_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_macro;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Attr_export_declRange__1(lean_object*);
lean_object* l_Lean_Parser_mkAntiquot_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_strLit_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_simple_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_recursor;
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_tactic__tag_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ident_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Attr_recursor_declRange__1(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Priority_numPrio__1(lean_object*);
lean_object* l_Lean_Parser_many1_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Attr_instance_declRange__1(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Attr_macro_declRange__1(lean_object*);
lean_object* l_Lean_Parser_nonReservedSymbol_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_simple_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_tactic__alt;
LEAN_EXPORT lean_object* l_Lean_Parser_priorityParser(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Attr_default__instance__1(lean_object*);
extern lean_object* l_Lean_PrettyPrinter_parenthesizerAttribute;
lean_object* l_Lean_Parser_numLit_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Attr_instance_formatter__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_default__instance_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Attr_simple__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_instance_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Attr_externEntry_parenthesizer__1(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_extern;
lean_object* l_Lean_Parser_symbol(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_export;
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_default__instance;
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Parser_symbol_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_attrParser_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_simple_formatter___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_symbol_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_withAntiquot(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__1(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_addPrecCheck___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_pushLine___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_tactic__alt_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Parser_many_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Priority_numPrio_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_specialize_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Attr_specialize_declRange__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_priorityParser_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_class_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_andthen(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Attr_specialize__1(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Attr_externEntry_formatter__1(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Attr_tactic__alt_parenthesizer__1(lean_object*);
lean_object* l_Lean_Parser_ident_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Priority_numPrio;
LEAN_EXPORT lean_object* l_Lean_Parser_attrParser_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_attrParser_formatter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Attr_instance__1(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Attr_recursor__1(lean_object*);
lean_object* l_Lean_Parser_many(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_macro_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Attr_instance_parenthesizer__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_attrParser_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_leadingNode_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Attr_specialize_parenthesizer__1(lean_object*);
extern lean_object* l_Lean_Parser_ident;
lean_object* l_Lean_Parser_optional_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_instance;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Attr_extern_formatter__1(lean_object*);
lean_object* l_Lean_Parser_withCache(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_externEntry;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Attr_default__instance_parenthesizer__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Attr___hyg_82_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_specialize_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_skip;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Attr_tactic__alt__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_class_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_priorityParser_formatter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_addBuiltinLeadingParser(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_externEntry_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_many1(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Attr_recursor_parenthesizer__1(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_andthen_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Attr_extern__1(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_instance_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkAntiquot(lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Parser_Priority_numPrio_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Attr_simple_declRange__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Priority_numPrio_parenthesizer___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Attr_class_formatter__1(lean_object*);
extern lean_object* l_Lean_Parser_numLit;
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Attr_export_parenthesizer__1(lean_object*);
extern lean_object* l_Lean_PrettyPrinter_formatterAttribute;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_strLit_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_simple_parenthesizer___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_nonReservedSymbol_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_numLit_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Attr_tactic__alt_formatter__1(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Attr_extern_declRange__1(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_categoryParser_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_externEntry_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_recursor_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_export_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_tactic__tag_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_registerBuiltinDynamicParserAttribute(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_export_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_extern_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Attr_macro_parenthesizer__1(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Attr_default__instance_formatter__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_macro_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Attr___hyg_3_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_2 = lean_mk_string_unchecked("builtin_prio_parser", 19, 19);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Category", 8, 8);
x_7 = lean_mk_string_unchecked("prio", 4, 4);
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_4);
x_8 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_7);
x_9 = lean_box(2);
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
x_19 = lean_mk_string_unchecked("Attr", 4, 4);
x_20 = l_Lean_Name_str___override(x_18, x_19);
x_21 = lean_mk_string_unchecked("_hyg", 4, 4);
x_22 = l_Lean_Name_str___override(x_20, x_21);
x_23 = lean_unsigned_to_nat(3u);
x_24 = l_Lean_Name_num___override(x_22, x_23);
x_25 = lean_unbox(x_9);
lean_inc(x_24);
x_26 = l_Lean_Parser_registerBuiltinParserAttribute(x_3, x_8, x_25, x_24, x_1);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_mk_string_unchecked("prio_parser", 11, 11);
x_29 = l_Lean_Name_mkStr1(x_28);
x_30 = l_Lean_Name_mkStr1(x_7);
x_31 = l_Lean_Parser_registerBuiltinDynamicParserAttribute(x_29, x_30, x_24, x_27);
return x_31;
}
else
{
lean_dec(x_24);
lean_dec(x_7);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Attr___hyg_82_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_2 = lean_mk_string_unchecked("builtin_attr_parser", 19, 19);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Category", 8, 8);
x_7 = lean_mk_string_unchecked("attr", 4, 4);
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_4);
x_8 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_7);
x_9 = lean_box(1);
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
x_19 = lean_mk_string_unchecked("Attr", 4, 4);
x_20 = l_Lean_Name_str___override(x_18, x_19);
x_21 = lean_mk_string_unchecked("_hyg", 4, 4);
x_22 = l_Lean_Name_str___override(x_20, x_21);
x_23 = lean_unsigned_to_nat(82u);
x_24 = l_Lean_Name_num___override(x_22, x_23);
x_25 = lean_unbox(x_9);
lean_inc(x_24);
x_26 = l_Lean_Parser_registerBuiltinParserAttribute(x_3, x_8, x_25, x_24, x_1);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_mk_string_unchecked("attr_parser", 11, 11);
x_29 = l_Lean_Name_mkStr1(x_28);
x_30 = l_Lean_Name_mkStr1(x_7);
x_31 = l_Lean_Parser_registerBuiltinDynamicParserAttribute(x_29, x_30, x_24, x_27);
return x_31;
}
else
{
lean_dec(x_24);
lean_dec(x_7);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_priorityParser(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_mk_string_unchecked("prio", 4, 4);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = l_Lean_Parser_categoryParser(x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_attrParser(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_mk_string_unchecked("attr", 4, 4);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = l_Lean_Parser_categoryParser(x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_priorityParser_formatter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_mk_string_unchecked("prio", 4, 4);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = l_Lean_PrettyPrinter_Formatter_categoryParser_formatter(x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_priorityParser_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_priorityParser_formatter___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_priorityParser_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_priorityParser_formatter(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_priorityParser_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_mk_string_unchecked("prio", 4, 4);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer(x_8, x_1, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_attrParser_formatter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_mk_string_unchecked("attr", 4, 4);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = l_Lean_PrettyPrinter_Formatter_categoryParser_formatter(x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_attrParser_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_attrParser_formatter___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_attrParser_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_attrParser_formatter(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_attrParser_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_mk_string_unchecked("attr", 4, 4);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer(x_8, x_1, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
static lean_object* _init_l_Lean_Parser_Priority_numPrio() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(1024u);
x_2 = l_Lean_Parser_checkPrec(x_1);
x_3 = l_Lean_Parser_numLit;
x_4 = l_Lean_Parser_andthen(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Priority_numPrio__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = lean_mk_string_unchecked("prio", 4, 4);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Priority", 8, 8);
x_7 = lean_mk_string_unchecked("numPrio", 7, 7);
x_8 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_7);
x_9 = l_Lean_Parser_Priority_numPrio;
x_10 = lean_unsigned_to_nat(1000u);
x_11 = l_Lean_Parser_addBuiltinLeadingParser(x_3, x_8, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Priority_numPrio_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Priority", 8, 8);
x_5 = lean_mk_string_unchecked("numPrio", 7, 7);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(30u);
x_8 = lean_unsigned_to_nat(23u);
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
x_13 = lean_unsigned_to_nat(27u);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_unsigned_to_nat(34u);
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
LEAN_EXPORT lean_object* l_Lean_Parser_Priority_numPrio_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkPrec_formatter___boxed), 5, 0);
x_7 = lean_alloc_closure((void*)(l_Lean_Parser_numLit_formatter), 5, 0);
x_8 = l_Lean_PrettyPrinter_Formatter_andthen_formatter(x_6, x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Priority_numPrio_parenthesizer___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Parenthesizer_addPrecCheck___redArg(x_1, x_3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Priority_numPrio_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_unsigned_to_nat(1024u);
x_7 = lean_alloc_closure((void*)(l_Lean_Parser_Priority_numPrio_parenthesizer___lam__0___boxed), 6, 1);
lean_closure_set(x_7, 0, x_6);
x_8 = lean_alloc_closure((void*)(l_Lean_Parser_numLit_parenthesizer), 5, 0);
x_9 = l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer(x_7, x_8, x_1, x_2, x_3, x_4, x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Priority_numPrio_parenthesizer___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_Priority_numPrio_parenthesizer___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
static lean_object* _init_l_Lean_Parser_Attr_simple() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Attr", 4, 4);
x_4 = lean_mk_string_unchecked("simple", 6, 6);
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
x_12 = l_Lean_Parser_ident;
x_13 = l_Lean_Parser_skip;
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_mk_string_unchecked("prio", 4, 4);
x_16 = l_Lean_Name_mkStr1(x_15);
x_17 = l_Lean_Parser_categoryParser(x_16, x_14);
x_18 = l_Lean_Parser_orelse(x_17, x_12);
x_19 = l_Lean_Parser_andthen(x_13, x_18);
x_20 = l_Lean_Parser_optional(x_19);
x_21 = l_Lean_Parser_andthen(x_12, x_20);
lean_inc(x_5);
x_22 = l_Lean_Parser_leadingNode(x_5, x_11, x_21);
x_23 = l_Lean_Parser_withAntiquot(x_10, x_22);
x_24 = l_Lean_Parser_withCache(x_5, x_23);
return x_24;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Attr_simple__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = lean_mk_string_unchecked("attr", 4, 4);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Attr", 4, 4);
x_7 = lean_mk_string_unchecked("simple", 6, 6);
x_8 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_7);
x_9 = l_Lean_Parser_Attr_simple;
x_10 = lean_unsigned_to_nat(1000u);
x_11 = l_Lean_Parser_addBuiltinLeadingParser(x_3, x_8, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Attr_simple_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Attr", 4, 4);
x_5 = lean_mk_string_unchecked("simple", 6, 6);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(36u);
x_8 = lean_unsigned_to_nat(23u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(113u);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_8);
lean_ctor_set(x_12, 2, x_11);
lean_ctor_set(x_12, 3, x_10);
x_13 = lean_unsigned_to_nat(27u);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_unsigned_to_nat(33u);
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
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_simple_formatter___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Formatter_pushLine___redArg(x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_simple_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_Attr_simple_formatter___lam__0___boxed), 5, 0);
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
x_8 = lean_mk_string_unchecked("Parser", 6, 6);
x_9 = lean_mk_string_unchecked("Attr", 4, 4);
x_10 = lean_mk_string_unchecked("simple", 6, 6);
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
x_16 = lean_alloc_closure((void*)(l_Lean_Parser_ident_formatter), 5, 0);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_alloc_closure((void*)(l_Lean_Parser_priorityParser_formatter___boxed), 6, 1);
lean_closure_set(x_18, 0, x_17);
lean_inc(x_16);
x_19 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter), 7, 2);
lean_closure_set(x_19, 0, x_18);
lean_closure_set(x_19, 1, x_16);
x_20 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_20, 0, x_6);
lean_closure_set(x_20, 1, x_19);
x_21 = lean_alloc_closure((void*)(l_Lean_Parser_optional_formatter), 6, 1);
lean_closure_set(x_21, 0, x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_22, 0, x_16);
lean_closure_set(x_22, 1, x_21);
x_23 = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(x_23, 0, x_11);
lean_closure_set(x_23, 1, x_15);
lean_closure_set(x_23, 2, x_22);
x_24 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_14, x_23, x_1, x_2, x_3, x_4, x_5);
return x_24;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_simple_formatter___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_Attr_simple_formatter___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Attr_simple_formatter__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_formatterAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Attr", 4, 4);
x_6 = lean_mk_string_unchecked("simple", 6, 6);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("formatter", 9, 9);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Attr_simple_formatter), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_simple_parenthesizer___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Parenthesizer_skip_parenthesizer___redArg(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_simple_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_Attr_simple_parenthesizer___lam__0___boxed), 5, 0);
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
x_8 = lean_mk_string_unchecked("Parser", 6, 6);
x_9 = lean_mk_string_unchecked("Attr", 4, 4);
x_10 = lean_mk_string_unchecked("simple", 6, 6);
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
x_16 = lean_alloc_closure((void*)(l_Lean_Parser_ident_parenthesizer), 5, 0);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_alloc_closure((void*)(l_Lean_Parser_priorityParser_parenthesizer), 6, 1);
lean_closure_set(x_18, 0, x_17);
lean_inc(x_16);
x_19 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer), 7, 2);
lean_closure_set(x_19, 0, x_18);
lean_closure_set(x_19, 1, x_16);
x_20 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_20, 0, x_6);
lean_closure_set(x_20, 1, x_19);
x_21 = lean_alloc_closure((void*)(l_Lean_Parser_optional_parenthesizer), 6, 1);
lean_closure_set(x_21, 0, x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_22, 0, x_16);
lean_closure_set(x_22, 1, x_21);
x_23 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer), 8, 3);
lean_closure_set(x_23, 0, x_11);
lean_closure_set(x_23, 1, x_15);
lean_closure_set(x_23, 2, x_22);
x_24 = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(x_14, x_23, x_1, x_2, x_3, x_4, x_5);
return x_24;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_simple_parenthesizer___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_Attr_simple_parenthesizer___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Attr", 4, 4);
x_6 = lean_mk_string_unchecked("simple", 6, 6);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("parenthesizer", 13, 13);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Attr_simple_parenthesizer), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
static lean_object* _init_l_Lean_Parser_Attr_macro() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Attr", 4, 4);
x_4 = lean_mk_string_unchecked("macro", 5, 5);
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
x_12 = lean_mk_string_unchecked("macro ", 6, 6);
x_13 = l_Lean_Parser_symbol(x_12);
lean_dec(x_12);
x_14 = l_Lean_Parser_ident;
x_15 = l_Lean_Parser_andthen(x_13, x_14);
lean_inc(x_5);
x_16 = l_Lean_Parser_leadingNode(x_5, x_11, x_15);
x_17 = l_Lean_Parser_withAntiquot(x_10, x_16);
x_18 = l_Lean_Parser_withCache(x_5, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Attr_macro__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = lean_mk_string_unchecked("attr", 4, 4);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Attr", 4, 4);
x_7 = lean_mk_string_unchecked("macro", 5, 5);
x_8 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_7);
x_9 = l_Lean_Parser_Attr_macro;
x_10 = lean_unsigned_to_nat(1000u);
x_11 = l_Lean_Parser_addBuiltinLeadingParser(x_3, x_8, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Attr_macro_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Attr", 4, 4);
x_5 = lean_mk_string_unchecked("macro", 5, 5);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(38u);
x_8 = lean_unsigned_to_nat(23u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(73u);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_8);
lean_ctor_set(x_12, 2, x_11);
lean_ctor_set(x_12, 3, x_10);
x_13 = lean_unsigned_to_nat(27u);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_unsigned_to_nat(34u);
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
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_macro_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("Parser", 6, 6);
x_8 = lean_mk_string_unchecked("Attr", 4, 4);
x_9 = lean_mk_string_unchecked("macro", 5, 5);
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
x_15 = lean_mk_string_unchecked("macro ", 6, 6);
x_16 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter), 6, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = lean_alloc_closure((void*)(l_Lean_Parser_ident_formatter), 5, 0);
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
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Attr_macro_formatter__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_formatterAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Attr", 4, 4);
x_6 = lean_mk_string_unchecked("macro", 5, 5);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("formatter", 9, 9);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Attr_macro_formatter), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_macro_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("Parser", 6, 6);
x_8 = lean_mk_string_unchecked("Attr", 4, 4);
x_9 = lean_mk_string_unchecked("macro", 5, 5);
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
x_15 = lean_mk_string_unchecked("macro ", 6, 6);
x_16 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___boxed), 6, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = lean_alloc_closure((void*)(l_Lean_Parser_ident_parenthesizer), 5, 0);
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
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Attr_macro_parenthesizer__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Attr", 4, 4);
x_6 = lean_mk_string_unchecked("macro", 5, 5);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("parenthesizer", 13, 13);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Attr_macro_parenthesizer), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
static lean_object* _init_l_Lean_Parser_Attr_export() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Attr", 4, 4);
x_4 = lean_mk_string_unchecked("export", 6, 6);
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
x_12 = lean_mk_string_unchecked("export ", 7, 7);
x_13 = l_Lean_Parser_symbol(x_12);
lean_dec(x_12);
x_14 = l_Lean_Parser_ident;
x_15 = l_Lean_Parser_andthen(x_13, x_14);
lean_inc(x_5);
x_16 = l_Lean_Parser_leadingNode(x_5, x_11, x_15);
x_17 = l_Lean_Parser_withAntiquot(x_10, x_16);
x_18 = l_Lean_Parser_withCache(x_5, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Attr_export__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = lean_mk_string_unchecked("attr", 4, 4);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Attr", 4, 4);
x_7 = lean_mk_string_unchecked("export", 6, 6);
x_8 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_7);
x_9 = l_Lean_Parser_Attr_export;
x_10 = lean_unsigned_to_nat(1000u);
x_11 = l_Lean_Parser_addBuiltinLeadingParser(x_3, x_8, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Attr_export_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Attr", 4, 4);
x_5 = lean_mk_string_unchecked("export", 6, 6);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(39u);
x_8 = lean_unsigned_to_nat(23u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(74u);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_8);
lean_ctor_set(x_12, 2, x_11);
lean_ctor_set(x_12, 3, x_10);
x_13 = lean_unsigned_to_nat(27u);
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
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_export_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("Parser", 6, 6);
x_8 = lean_mk_string_unchecked("Attr", 4, 4);
x_9 = lean_mk_string_unchecked("export", 6, 6);
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
x_15 = lean_mk_string_unchecked("export ", 7, 7);
x_16 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter), 6, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = lean_alloc_closure((void*)(l_Lean_Parser_ident_formatter), 5, 0);
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
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Attr_export_formatter__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_formatterAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Attr", 4, 4);
x_6 = lean_mk_string_unchecked("export", 6, 6);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("formatter", 9, 9);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Attr_export_formatter), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_export_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("Parser", 6, 6);
x_8 = lean_mk_string_unchecked("Attr", 4, 4);
x_9 = lean_mk_string_unchecked("export", 6, 6);
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
x_15 = lean_mk_string_unchecked("export ", 7, 7);
x_16 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___boxed), 6, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = lean_alloc_closure((void*)(l_Lean_Parser_ident_parenthesizer), 5, 0);
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
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Attr_export_parenthesizer__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Attr", 4, 4);
x_6 = lean_mk_string_unchecked("export", 6, 6);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("parenthesizer", 13, 13);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Attr_export_parenthesizer), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
static lean_object* _init_l_Lean_Parser_Attr_recursor() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Attr", 4, 4);
x_4 = lean_mk_string_unchecked("recursor", 8, 8);
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
x_12 = lean_mk_string_unchecked("recursor ", 9, 9);
x_13 = lean_unbox(x_7);
x_14 = l_Lean_Parser_nonReservedSymbol(x_12, x_13);
lean_dec(x_12);
x_15 = l_Lean_Parser_numLit;
x_16 = l_Lean_Parser_andthen(x_14, x_15);
lean_inc(x_5);
x_17 = l_Lean_Parser_leadingNode(x_5, x_11, x_16);
x_18 = l_Lean_Parser_withAntiquot(x_10, x_17);
x_19 = l_Lean_Parser_withCache(x_5, x_18);
return x_19;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Attr_recursor__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = lean_mk_string_unchecked("attr", 4, 4);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Attr", 4, 4);
x_7 = lean_mk_string_unchecked("recursor", 8, 8);
x_8 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_7);
x_9 = l_Lean_Parser_Attr_recursor;
x_10 = lean_unsigned_to_nat(1000u);
x_11 = l_Lean_Parser_addBuiltinLeadingParser(x_3, x_8, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Attr_recursor_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Attr", 4, 4);
x_5 = lean_mk_string_unchecked("recursor", 8, 8);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(42u);
x_8 = lean_unsigned_to_nat(23u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(101u);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_8);
lean_ctor_set(x_12, 2, x_11);
lean_ctor_set(x_12, 3, x_10);
x_13 = lean_unsigned_to_nat(27u);
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
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_recursor_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("Parser", 6, 6);
x_8 = lean_mk_string_unchecked("Attr", 4, 4);
x_9 = lean_mk_string_unchecked("recursor", 8, 8);
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
x_15 = lean_mk_string_unchecked("recursor ", 9, 9);
x_16 = lean_alloc_closure((void*)(l_Lean_Parser_nonReservedSymbol_formatter___boxed), 7, 2);
lean_closure_set(x_16, 0, x_15);
lean_closure_set(x_16, 1, x_12);
x_17 = lean_alloc_closure((void*)(l_Lean_Parser_numLit_formatter), 5, 0);
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
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Attr_recursor_formatter__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_formatterAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Attr", 4, 4);
x_6 = lean_mk_string_unchecked("recursor", 8, 8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("formatter", 9, 9);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Attr_recursor_formatter), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_recursor_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("Parser", 6, 6);
x_8 = lean_mk_string_unchecked("Attr", 4, 4);
x_9 = lean_mk_string_unchecked("recursor", 8, 8);
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
x_15 = lean_mk_string_unchecked("recursor ", 9, 9);
x_16 = lean_alloc_closure((void*)(l_Lean_Parser_nonReservedSymbol_parenthesizer___boxed), 7, 2);
lean_closure_set(x_16, 0, x_15);
lean_closure_set(x_16, 1, x_12);
x_17 = lean_alloc_closure((void*)(l_Lean_Parser_numLit_parenthesizer), 5, 0);
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
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Attr_recursor_parenthesizer__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Attr", 4, 4);
x_6 = lean_mk_string_unchecked("recursor", 8, 8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("parenthesizer", 13, 13);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Attr_recursor_parenthesizer), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
static lean_object* _init_l_Lean_Parser_Attr_class() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Attr", 4, 4);
x_4 = lean_mk_string_unchecked("class", 5, 5);
lean_inc(x_4);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_box(1);
x_7 = lean_box(0);
x_8 = lean_unbox(x_6);
x_9 = lean_unbox(x_7);
lean_inc(x_5);
x_10 = l_Lean_Parser_mkAntiquot(x_4, x_5, x_8, x_9);
x_11 = lean_unsigned_to_nat(1024u);
x_12 = l_Lean_Parser_symbol(x_4);
lean_dec(x_4);
lean_inc(x_5);
x_13 = l_Lean_Parser_leadingNode(x_5, x_11, x_12);
x_14 = l_Lean_Parser_withAntiquot(x_10, x_13);
x_15 = l_Lean_Parser_withCache(x_5, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Attr_class__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = lean_mk_string_unchecked("attr", 4, 4);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Attr", 4, 4);
x_7 = lean_mk_string_unchecked("class", 5, 5);
x_8 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_7);
x_9 = l_Lean_Parser_Attr_class;
x_10 = lean_unsigned_to_nat(1000u);
x_11 = l_Lean_Parser_addBuiltinLeadingParser(x_3, x_8, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Attr_class_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Attr", 4, 4);
x_5 = lean_mk_string_unchecked("class", 5, 5);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(43u);
x_8 = lean_unsigned_to_nat(23u);
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
x_13 = lean_unsigned_to_nat(27u);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_unsigned_to_nat(34u);
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
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_class_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("Parser", 6, 6);
x_8 = lean_mk_string_unchecked("Attr", 4, 4);
x_9 = lean_mk_string_unchecked("class", 5, 5);
lean_inc(x_9);
x_10 = l_Lean_Name_mkStr4(x_6, x_7, x_8, x_9);
x_11 = lean_box(1);
x_12 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
x_13 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(x_13, 0, x_9);
lean_closure_set(x_13, 1, x_10);
lean_closure_set(x_13, 2, x_11);
lean_closure_set(x_13, 3, x_12);
x_14 = lean_unsigned_to_nat(1024u);
x_15 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter), 6, 1);
lean_closure_set(x_15, 0, x_9);
x_16 = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(x_16, 0, x_10);
lean_closure_set(x_16, 1, x_14);
lean_closure_set(x_16, 2, x_15);
x_17 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_13, x_16, x_1, x_2, x_3, x_4, x_5);
return x_17;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Attr_class_formatter__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_formatterAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Attr", 4, 4);
x_6 = lean_mk_string_unchecked("class", 5, 5);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("formatter", 9, 9);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Attr_class_formatter), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_class_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("Parser", 6, 6);
x_8 = lean_mk_string_unchecked("Attr", 4, 4);
x_9 = lean_mk_string_unchecked("class", 5, 5);
lean_inc(x_9);
x_10 = l_Lean_Name_mkStr4(x_6, x_7, x_8, x_9);
x_11 = lean_box(1);
x_12 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
x_13 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(x_13, 0, x_9);
lean_closure_set(x_13, 1, x_10);
lean_closure_set(x_13, 2, x_11);
lean_closure_set(x_13, 3, x_12);
x_14 = lean_unsigned_to_nat(1024u);
x_15 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___boxed), 6, 1);
lean_closure_set(x_15, 0, x_9);
x_16 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer), 8, 3);
lean_closure_set(x_16, 0, x_10);
lean_closure_set(x_16, 1, x_14);
lean_closure_set(x_16, 2, x_15);
x_17 = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(x_13, x_16, x_1, x_2, x_3, x_4, x_5);
return x_17;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Attr_class_parenthesizer__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Attr", 4, 4);
x_6 = lean_mk_string_unchecked("class", 5, 5);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("parenthesizer", 13, 13);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Attr_class_parenthesizer), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
static lean_object* _init_l_Lean_Parser_Attr_instance() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Attr", 4, 4);
x_4 = lean_mk_string_unchecked("instance", 8, 8);
lean_inc(x_4);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_box(1);
x_7 = lean_box(0);
x_8 = lean_unbox(x_6);
x_9 = lean_unbox(x_7);
lean_inc(x_5);
x_10 = l_Lean_Parser_mkAntiquot(x_4, x_5, x_8, x_9);
x_11 = lean_unsigned_to_nat(1024u);
x_12 = l_Lean_Parser_symbol(x_4);
lean_dec(x_4);
x_13 = l_Lean_Parser_skip;
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_mk_string_unchecked("prio", 4, 4);
x_16 = l_Lean_Name_mkStr1(x_15);
x_17 = l_Lean_Parser_categoryParser(x_16, x_14);
x_18 = l_Lean_Parser_andthen(x_13, x_17);
x_19 = l_Lean_Parser_optional(x_18);
x_20 = l_Lean_Parser_andthen(x_12, x_19);
lean_inc(x_5);
x_21 = l_Lean_Parser_leadingNode(x_5, x_11, x_20);
x_22 = l_Lean_Parser_withAntiquot(x_10, x_21);
x_23 = l_Lean_Parser_withCache(x_5, x_22);
return x_23;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Attr_instance__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = lean_mk_string_unchecked("attr", 4, 4);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Attr", 4, 4);
x_7 = lean_mk_string_unchecked("instance", 8, 8);
x_8 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_7);
x_9 = l_Lean_Parser_Attr_instance;
x_10 = lean_unsigned_to_nat(1000u);
x_11 = l_Lean_Parser_addBuiltinLeadingParser(x_3, x_8, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Attr_instance_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Attr", 4, 4);
x_5 = lean_mk_string_unchecked("instance", 8, 8);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(44u);
x_8 = lean_unsigned_to_nat(23u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(112u);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_8);
lean_ctor_set(x_12, 2, x_11);
lean_ctor_set(x_12, 3, x_10);
x_13 = lean_unsigned_to_nat(27u);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_unsigned_to_nat(37u);
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
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_instance_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_Attr_simple_formatter___lam__0___boxed), 5, 0);
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
x_8 = lean_mk_string_unchecked("Parser", 6, 6);
x_9 = lean_mk_string_unchecked("Attr", 4, 4);
x_10 = lean_mk_string_unchecked("instance", 8, 8);
lean_inc(x_10);
x_11 = l_Lean_Name_mkStr4(x_7, x_8, x_9, x_10);
x_12 = lean_box(1);
x_13 = lean_box(0);
lean_inc(x_11);
lean_inc(x_10);
x_14 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(x_14, 0, x_10);
lean_closure_set(x_14, 1, x_11);
lean_closure_set(x_14, 2, x_12);
lean_closure_set(x_14, 3, x_13);
x_15 = lean_unsigned_to_nat(1024u);
x_16 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter), 6, 1);
lean_closure_set(x_16, 0, x_10);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_alloc_closure((void*)(l_Lean_Parser_priorityParser_formatter___boxed), 6, 1);
lean_closure_set(x_18, 0, x_17);
x_19 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_19, 0, x_6);
lean_closure_set(x_19, 1, x_18);
x_20 = lean_alloc_closure((void*)(l_Lean_Parser_optional_formatter), 6, 1);
lean_closure_set(x_20, 0, x_19);
x_21 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_21, 0, x_16);
lean_closure_set(x_21, 1, x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(x_22, 0, x_11);
lean_closure_set(x_22, 1, x_15);
lean_closure_set(x_22, 2, x_21);
x_23 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_14, x_22, x_1, x_2, x_3, x_4, x_5);
return x_23;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Attr_instance_formatter__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_formatterAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Attr", 4, 4);
x_6 = lean_mk_string_unchecked("instance", 8, 8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("formatter", 9, 9);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Attr_instance_formatter), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_instance_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_Attr_simple_parenthesizer___lam__0___boxed), 5, 0);
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
x_8 = lean_mk_string_unchecked("Parser", 6, 6);
x_9 = lean_mk_string_unchecked("Attr", 4, 4);
x_10 = lean_mk_string_unchecked("instance", 8, 8);
lean_inc(x_10);
x_11 = l_Lean_Name_mkStr4(x_7, x_8, x_9, x_10);
x_12 = lean_box(1);
x_13 = lean_box(0);
lean_inc(x_11);
lean_inc(x_10);
x_14 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(x_14, 0, x_10);
lean_closure_set(x_14, 1, x_11);
lean_closure_set(x_14, 2, x_12);
lean_closure_set(x_14, 3, x_13);
x_15 = lean_unsigned_to_nat(1024u);
x_16 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___boxed), 6, 1);
lean_closure_set(x_16, 0, x_10);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_alloc_closure((void*)(l_Lean_Parser_priorityParser_parenthesizer), 6, 1);
lean_closure_set(x_18, 0, x_17);
x_19 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_19, 0, x_6);
lean_closure_set(x_19, 1, x_18);
x_20 = lean_alloc_closure((void*)(l_Lean_Parser_optional_parenthesizer), 6, 1);
lean_closure_set(x_20, 0, x_19);
x_21 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_21, 0, x_16);
lean_closure_set(x_21, 1, x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer), 8, 3);
lean_closure_set(x_22, 0, x_11);
lean_closure_set(x_22, 1, x_15);
lean_closure_set(x_22, 2, x_21);
x_23 = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(x_14, x_22, x_1, x_2, x_3, x_4, x_5);
return x_23;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Attr_instance_parenthesizer__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Attr", 4, 4);
x_6 = lean_mk_string_unchecked("instance", 8, 8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("parenthesizer", 13, 13);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Attr_instance_parenthesizer), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
static lean_object* _init_l_Lean_Parser_Attr_default__instance() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Attr", 4, 4);
x_4 = lean_mk_string_unchecked("default_instance", 16, 16);
lean_inc(x_4);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_box(1);
x_7 = lean_box(0);
x_8 = lean_unbox(x_6);
x_9 = lean_unbox(x_7);
lean_inc(x_5);
x_10 = l_Lean_Parser_mkAntiquot(x_4, x_5, x_8, x_9);
x_11 = lean_unsigned_to_nat(1024u);
x_12 = lean_unbox(x_7);
x_13 = l_Lean_Parser_nonReservedSymbol(x_4, x_12);
lean_dec(x_4);
x_14 = l_Lean_Parser_skip;
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_mk_string_unchecked("prio", 4, 4);
x_17 = l_Lean_Name_mkStr1(x_16);
x_18 = l_Lean_Parser_categoryParser(x_17, x_15);
x_19 = l_Lean_Parser_andthen(x_14, x_18);
x_20 = l_Lean_Parser_optional(x_19);
x_21 = l_Lean_Parser_andthen(x_13, x_20);
lean_inc(x_5);
x_22 = l_Lean_Parser_leadingNode(x_5, x_11, x_21);
x_23 = l_Lean_Parser_withAntiquot(x_10, x_22);
x_24 = l_Lean_Parser_withCache(x_5, x_23);
return x_24;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Attr_default__instance__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = lean_mk_string_unchecked("attr", 4, 4);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Attr", 4, 4);
x_7 = lean_mk_string_unchecked("default_instance", 16, 16);
x_8 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_7);
x_9 = l_Lean_Parser_Attr_default__instance;
x_10 = lean_unsigned_to_nat(1000u);
x_11 = l_Lean_Parser_addBuiltinLeadingParser(x_3, x_8, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Attr_default__instance_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Attr", 4, 4);
x_5 = lean_mk_string_unchecked("default_instance", 16, 16);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(45u);
x_8 = lean_unsigned_to_nat(23u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(138u);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_8);
lean_ctor_set(x_12, 2, x_11);
lean_ctor_set(x_12, 3, x_10);
x_13 = lean_unsigned_to_nat(27u);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_unsigned_to_nat(43u);
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
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_default__instance_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_Attr_simple_formatter___lam__0___boxed), 5, 0);
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
x_8 = lean_mk_string_unchecked("Parser", 6, 6);
x_9 = lean_mk_string_unchecked("Attr", 4, 4);
x_10 = lean_mk_string_unchecked("default_instance", 16, 16);
lean_inc(x_10);
x_11 = l_Lean_Name_mkStr4(x_7, x_8, x_9, x_10);
x_12 = lean_box(1);
x_13 = lean_box(0);
lean_inc(x_11);
lean_inc(x_10);
x_14 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(x_14, 0, x_10);
lean_closure_set(x_14, 1, x_11);
lean_closure_set(x_14, 2, x_12);
lean_closure_set(x_14, 3, x_13);
x_15 = lean_unsigned_to_nat(1024u);
x_16 = lean_alloc_closure((void*)(l_Lean_Parser_nonReservedSymbol_formatter___boxed), 7, 2);
lean_closure_set(x_16, 0, x_10);
lean_closure_set(x_16, 1, x_13);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_alloc_closure((void*)(l_Lean_Parser_priorityParser_formatter___boxed), 6, 1);
lean_closure_set(x_18, 0, x_17);
x_19 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_19, 0, x_6);
lean_closure_set(x_19, 1, x_18);
x_20 = lean_alloc_closure((void*)(l_Lean_Parser_optional_formatter), 6, 1);
lean_closure_set(x_20, 0, x_19);
x_21 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_21, 0, x_16);
lean_closure_set(x_21, 1, x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(x_22, 0, x_11);
lean_closure_set(x_22, 1, x_15);
lean_closure_set(x_22, 2, x_21);
x_23 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_14, x_22, x_1, x_2, x_3, x_4, x_5);
return x_23;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Attr_default__instance_formatter__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_formatterAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Attr", 4, 4);
x_6 = lean_mk_string_unchecked("default_instance", 16, 16);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("formatter", 9, 9);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Attr_default__instance_formatter), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_default__instance_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_Attr_simple_parenthesizer___lam__0___boxed), 5, 0);
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
x_8 = lean_mk_string_unchecked("Parser", 6, 6);
x_9 = lean_mk_string_unchecked("Attr", 4, 4);
x_10 = lean_mk_string_unchecked("default_instance", 16, 16);
lean_inc(x_10);
x_11 = l_Lean_Name_mkStr4(x_7, x_8, x_9, x_10);
x_12 = lean_box(1);
x_13 = lean_box(0);
lean_inc(x_11);
lean_inc(x_10);
x_14 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(x_14, 0, x_10);
lean_closure_set(x_14, 1, x_11);
lean_closure_set(x_14, 2, x_12);
lean_closure_set(x_14, 3, x_13);
x_15 = lean_unsigned_to_nat(1024u);
x_16 = lean_alloc_closure((void*)(l_Lean_Parser_nonReservedSymbol_parenthesizer___boxed), 7, 2);
lean_closure_set(x_16, 0, x_10);
lean_closure_set(x_16, 1, x_13);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_alloc_closure((void*)(l_Lean_Parser_priorityParser_parenthesizer), 6, 1);
lean_closure_set(x_18, 0, x_17);
x_19 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_19, 0, x_6);
lean_closure_set(x_19, 1, x_18);
x_20 = lean_alloc_closure((void*)(l_Lean_Parser_optional_parenthesizer), 6, 1);
lean_closure_set(x_20, 0, x_19);
x_21 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_21, 0, x_16);
lean_closure_set(x_21, 1, x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer), 8, 3);
lean_closure_set(x_22, 0, x_11);
lean_closure_set(x_22, 1, x_15);
lean_closure_set(x_22, 2, x_21);
x_23 = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(x_14, x_22, x_1, x_2, x_3, x_4, x_5);
return x_23;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Attr_default__instance_parenthesizer__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Attr", 4, 4);
x_6 = lean_mk_string_unchecked("default_instance", 16, 16);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("parenthesizer", 13, 13);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Attr_default__instance_parenthesizer), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
static lean_object* _init_l_Lean_Parser_Attr_specialize() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Attr", 4, 4);
x_4 = lean_mk_string_unchecked("specialize", 10, 10);
lean_inc(x_4);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_box(1);
x_7 = lean_box(0);
x_8 = lean_unbox(x_6);
x_9 = lean_unbox(x_7);
lean_inc(x_5);
x_10 = l_Lean_Parser_mkAntiquot(x_4, x_5, x_8, x_9);
x_11 = lean_unsigned_to_nat(1024u);
x_12 = lean_unbox(x_7);
x_13 = l_Lean_Parser_nonReservedSymbol(x_4, x_12);
lean_dec(x_4);
x_14 = l_Lean_Parser_skip;
x_15 = l_Lean_Parser_ident;
x_16 = l_Lean_Parser_numLit;
x_17 = l_Lean_Parser_orelse(x_15, x_16);
x_18 = l_Lean_Parser_andthen(x_14, x_17);
x_19 = l_Lean_Parser_many(x_18);
x_20 = l_Lean_Parser_andthen(x_13, x_19);
lean_inc(x_5);
x_21 = l_Lean_Parser_leadingNode(x_5, x_11, x_20);
x_22 = l_Lean_Parser_withAntiquot(x_10, x_21);
x_23 = l_Lean_Parser_withCache(x_5, x_22);
return x_23;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Attr_specialize__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = lean_mk_string_unchecked("attr", 4, 4);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Attr", 4, 4);
x_7 = lean_mk_string_unchecked("specialize", 10, 10);
x_8 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_7);
x_9 = l_Lean_Parser_Attr_specialize;
x_10 = lean_unsigned_to_nat(1000u);
x_11 = l_Lean_Parser_addBuiltinLeadingParser(x_3, x_8, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Attr_specialize_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Attr", 4, 4);
x_5 = lean_mk_string_unchecked("specialize", 10, 10);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(46u);
x_8 = lean_unsigned_to_nat(23u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(134u);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_8);
lean_ctor_set(x_12, 2, x_11);
lean_ctor_set(x_12, 3, x_10);
x_13 = lean_unsigned_to_nat(27u);
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
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_specialize_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_Attr_simple_formatter___lam__0___boxed), 5, 0);
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
x_8 = lean_mk_string_unchecked("Parser", 6, 6);
x_9 = lean_mk_string_unchecked("Attr", 4, 4);
x_10 = lean_mk_string_unchecked("specialize", 10, 10);
lean_inc(x_10);
x_11 = l_Lean_Name_mkStr4(x_7, x_8, x_9, x_10);
x_12 = lean_box(1);
x_13 = lean_box(0);
lean_inc(x_11);
lean_inc(x_10);
x_14 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(x_14, 0, x_10);
lean_closure_set(x_14, 1, x_11);
lean_closure_set(x_14, 2, x_12);
lean_closure_set(x_14, 3, x_13);
x_15 = lean_unsigned_to_nat(1024u);
x_16 = lean_alloc_closure((void*)(l_Lean_Parser_nonReservedSymbol_formatter___boxed), 7, 2);
lean_closure_set(x_16, 0, x_10);
lean_closure_set(x_16, 1, x_13);
x_17 = lean_alloc_closure((void*)(l_Lean_Parser_ident_formatter), 5, 0);
x_18 = lean_alloc_closure((void*)(l_Lean_Parser_numLit_formatter), 5, 0);
x_19 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter), 7, 2);
lean_closure_set(x_19, 0, x_17);
lean_closure_set(x_19, 1, x_18);
x_20 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_20, 0, x_6);
lean_closure_set(x_20, 1, x_19);
x_21 = lean_alloc_closure((void*)(l_Lean_Parser_many_formatter), 6, 1);
lean_closure_set(x_21, 0, x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_22, 0, x_16);
lean_closure_set(x_22, 1, x_21);
x_23 = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(x_23, 0, x_11);
lean_closure_set(x_23, 1, x_15);
lean_closure_set(x_23, 2, x_22);
x_24 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_14, x_23, x_1, x_2, x_3, x_4, x_5);
return x_24;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Attr_specialize_formatter__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_formatterAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Attr", 4, 4);
x_6 = lean_mk_string_unchecked("specialize", 10, 10);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("formatter", 9, 9);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Attr_specialize_formatter), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_specialize_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_Attr_simple_parenthesizer___lam__0___boxed), 5, 0);
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
x_8 = lean_mk_string_unchecked("Parser", 6, 6);
x_9 = lean_mk_string_unchecked("Attr", 4, 4);
x_10 = lean_mk_string_unchecked("specialize", 10, 10);
lean_inc(x_10);
x_11 = l_Lean_Name_mkStr4(x_7, x_8, x_9, x_10);
x_12 = lean_box(1);
x_13 = lean_box(0);
lean_inc(x_11);
lean_inc(x_10);
x_14 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(x_14, 0, x_10);
lean_closure_set(x_14, 1, x_11);
lean_closure_set(x_14, 2, x_12);
lean_closure_set(x_14, 3, x_13);
x_15 = lean_unsigned_to_nat(1024u);
x_16 = lean_alloc_closure((void*)(l_Lean_Parser_nonReservedSymbol_parenthesizer___boxed), 7, 2);
lean_closure_set(x_16, 0, x_10);
lean_closure_set(x_16, 1, x_13);
x_17 = lean_alloc_closure((void*)(l_Lean_Parser_ident_parenthesizer), 5, 0);
x_18 = lean_alloc_closure((void*)(l_Lean_Parser_numLit_parenthesizer), 5, 0);
x_19 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer), 7, 2);
lean_closure_set(x_19, 0, x_17);
lean_closure_set(x_19, 1, x_18);
x_20 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_20, 0, x_6);
lean_closure_set(x_20, 1, x_19);
x_21 = lean_alloc_closure((void*)(l_Lean_Parser_many_parenthesizer), 6, 1);
lean_closure_set(x_21, 0, x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_22, 0, x_16);
lean_closure_set(x_22, 1, x_21);
x_23 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer), 8, 3);
lean_closure_set(x_23, 0, x_11);
lean_closure_set(x_23, 1, x_15);
lean_closure_set(x_23, 2, x_22);
x_24 = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(x_14, x_23, x_1, x_2, x_3, x_4, x_5);
return x_24;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Attr_specialize_parenthesizer__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Attr", 4, 4);
x_6 = lean_mk_string_unchecked("specialize", 10, 10);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("parenthesizer", 13, 13);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Attr_specialize_parenthesizer), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
static lean_object* _init_l_Lean_Parser_Attr_externEntry() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Attr", 4, 4);
x_4 = lean_mk_string_unchecked("externEntry", 11, 11);
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
x_12 = l_Lean_Parser_ident;
x_13 = l_Lean_Parser_skip;
x_14 = l_Lean_Parser_andthen(x_12, x_13);
x_15 = l_Lean_Parser_optional(x_14);
x_16 = lean_mk_string_unchecked("inline ", 7, 7);
x_17 = lean_unbox(x_7);
x_18 = l_Lean_Parser_nonReservedSymbol(x_16, x_17);
lean_dec(x_16);
x_19 = l_Lean_Parser_optional(x_18);
x_20 = l_Lean_Parser_strLit;
x_21 = l_Lean_Parser_andthen(x_19, x_20);
x_22 = l_Lean_Parser_andthen(x_15, x_21);
lean_inc(x_5);
x_23 = l_Lean_Parser_leadingNode(x_5, x_11, x_22);
x_24 = l_Lean_Parser_withAntiquot(x_10, x_23);
x_25 = l_Lean_Parser_withCache(x_5, x_24);
return x_25;
}
}
static lean_object* _init_l_Lean_Parser_Attr_extern() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Attr", 4, 4);
x_4 = lean_mk_string_unchecked("extern", 6, 6);
lean_inc(x_4);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_box(1);
x_7 = lean_box(0);
x_8 = lean_unbox(x_6);
x_9 = lean_unbox(x_7);
lean_inc(x_5);
x_10 = l_Lean_Parser_mkAntiquot(x_4, x_5, x_8, x_9);
x_11 = lean_unsigned_to_nat(1024u);
x_12 = lean_unbox(x_7);
x_13 = l_Lean_Parser_nonReservedSymbol(x_4, x_12);
lean_dec(x_4);
x_14 = l_Lean_Parser_skip;
x_15 = l_Lean_Parser_numLit;
x_16 = l_Lean_Parser_andthen(x_14, x_15);
x_17 = l_Lean_Parser_optional(x_16);
x_18 = l_Lean_Parser_Attr_externEntry;
x_19 = l_Lean_Parser_andthen(x_14, x_18);
x_20 = l_Lean_Parser_many(x_19);
x_21 = l_Lean_Parser_andthen(x_17, x_20);
x_22 = l_Lean_Parser_andthen(x_13, x_21);
lean_inc(x_5);
x_23 = l_Lean_Parser_leadingNode(x_5, x_11, x_22);
x_24 = l_Lean_Parser_withAntiquot(x_10, x_23);
x_25 = l_Lean_Parser_withCache(x_5, x_24);
return x_25;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Attr_extern__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = lean_mk_string_unchecked("attr", 4, 4);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Attr", 4, 4);
x_7 = lean_mk_string_unchecked("extern", 6, 6);
x_8 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_7);
x_9 = l_Lean_Parser_Attr_extern;
x_10 = lean_unsigned_to_nat(1000u);
x_11 = l_Lean_Parser_addBuiltinLeadingParser(x_3, x_8, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Attr_extern_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Attr", 4, 4);
x_5 = lean_mk_string_unchecked("extern", 6, 6);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(50u);
x_8 = lean_unsigned_to_nat(23u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(51u);
x_11 = lean_unsigned_to_nat(93u);
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
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_externEntry_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_Attr_simple_formatter___lam__0___boxed), 5, 0);
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
x_8 = lean_mk_string_unchecked("Parser", 6, 6);
x_9 = lean_mk_string_unchecked("Attr", 4, 4);
x_10 = lean_mk_string_unchecked("externEntry", 11, 11);
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
x_16 = lean_alloc_closure((void*)(l_Lean_Parser_ident_formatter), 5, 0);
x_17 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_17, 0, x_16);
lean_closure_set(x_17, 1, x_6);
x_18 = lean_alloc_closure((void*)(l_Lean_Parser_optional_formatter), 6, 1);
lean_closure_set(x_18, 0, x_17);
x_19 = lean_mk_string_unchecked("inline ", 7, 7);
x_20 = lean_alloc_closure((void*)(l_Lean_Parser_nonReservedSymbol_formatter___boxed), 7, 2);
lean_closure_set(x_20, 0, x_19);
lean_closure_set(x_20, 1, x_13);
x_21 = lean_alloc_closure((void*)(l_Lean_Parser_optional_formatter), 6, 1);
lean_closure_set(x_21, 0, x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_Parser_strLit_formatter), 5, 0);
x_23 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_23, 0, x_21);
lean_closure_set(x_23, 1, x_22);
x_24 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_24, 0, x_18);
lean_closure_set(x_24, 1, x_23);
x_25 = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(x_25, 0, x_11);
lean_closure_set(x_25, 1, x_15);
lean_closure_set(x_25, 2, x_24);
x_26 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_14, x_25, x_1, x_2, x_3, x_4, x_5);
return x_26;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Attr_externEntry_formatter__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_formatterAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Attr", 4, 4);
x_6 = lean_mk_string_unchecked("externEntry", 11, 11);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("formatter", 9, 9);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Attr_externEntry_formatter), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_extern_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_Attr_simple_formatter___lam__0___boxed), 5, 0);
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
x_8 = lean_mk_string_unchecked("Parser", 6, 6);
x_9 = lean_mk_string_unchecked("Attr", 4, 4);
x_10 = lean_mk_string_unchecked("extern", 6, 6);
lean_inc(x_10);
x_11 = l_Lean_Name_mkStr4(x_7, x_8, x_9, x_10);
x_12 = lean_box(1);
x_13 = lean_box(0);
lean_inc(x_11);
lean_inc(x_10);
x_14 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(x_14, 0, x_10);
lean_closure_set(x_14, 1, x_11);
lean_closure_set(x_14, 2, x_12);
lean_closure_set(x_14, 3, x_13);
x_15 = lean_unsigned_to_nat(1024u);
x_16 = lean_alloc_closure((void*)(l_Lean_Parser_nonReservedSymbol_formatter___boxed), 7, 2);
lean_closure_set(x_16, 0, x_10);
lean_closure_set(x_16, 1, x_13);
x_17 = lean_alloc_closure((void*)(l_Lean_Parser_numLit_formatter), 5, 0);
lean_inc(x_6);
x_18 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_18, 0, x_6);
lean_closure_set(x_18, 1, x_17);
x_19 = lean_alloc_closure((void*)(l_Lean_Parser_optional_formatter), 6, 1);
lean_closure_set(x_19, 0, x_18);
x_20 = lean_alloc_closure((void*)(l_Lean_Parser_Attr_externEntry_formatter), 5, 0);
x_21 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_21, 0, x_6);
lean_closure_set(x_21, 1, x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_Parser_many_formatter), 6, 1);
lean_closure_set(x_22, 0, x_21);
x_23 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_23, 0, x_19);
lean_closure_set(x_23, 1, x_22);
x_24 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_24, 0, x_16);
lean_closure_set(x_24, 1, x_23);
x_25 = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(x_25, 0, x_11);
lean_closure_set(x_25, 1, x_15);
lean_closure_set(x_25, 2, x_24);
x_26 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_14, x_25, x_1, x_2, x_3, x_4, x_5);
return x_26;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Attr_extern_formatter__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_formatterAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Attr", 4, 4);
x_6 = lean_mk_string_unchecked("extern", 6, 6);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("formatter", 9, 9);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Attr_extern_formatter), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_externEntry_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_Attr_simple_parenthesizer___lam__0___boxed), 5, 0);
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
x_8 = lean_mk_string_unchecked("Parser", 6, 6);
x_9 = lean_mk_string_unchecked("Attr", 4, 4);
x_10 = lean_mk_string_unchecked("externEntry", 11, 11);
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
x_16 = lean_alloc_closure((void*)(l_Lean_Parser_ident_parenthesizer), 5, 0);
x_17 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_17, 0, x_16);
lean_closure_set(x_17, 1, x_6);
x_18 = lean_alloc_closure((void*)(l_Lean_Parser_optional_parenthesizer), 6, 1);
lean_closure_set(x_18, 0, x_17);
x_19 = lean_mk_string_unchecked("inline ", 7, 7);
x_20 = lean_alloc_closure((void*)(l_Lean_Parser_nonReservedSymbol_parenthesizer___boxed), 7, 2);
lean_closure_set(x_20, 0, x_19);
lean_closure_set(x_20, 1, x_13);
x_21 = lean_alloc_closure((void*)(l_Lean_Parser_optional_parenthesizer), 6, 1);
lean_closure_set(x_21, 0, x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_Parser_strLit_parenthesizer), 5, 0);
x_23 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_23, 0, x_21);
lean_closure_set(x_23, 1, x_22);
x_24 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_24, 0, x_18);
lean_closure_set(x_24, 1, x_23);
x_25 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer), 8, 3);
lean_closure_set(x_25, 0, x_11);
lean_closure_set(x_25, 1, x_15);
lean_closure_set(x_25, 2, x_24);
x_26 = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(x_14, x_25, x_1, x_2, x_3, x_4, x_5);
return x_26;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Attr_externEntry_parenthesizer__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Attr", 4, 4);
x_6 = lean_mk_string_unchecked("externEntry", 11, 11);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("parenthesizer", 13, 13);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Attr_externEntry_parenthesizer), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_extern_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_Attr_simple_parenthesizer___lam__0___boxed), 5, 0);
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
x_8 = lean_mk_string_unchecked("Parser", 6, 6);
x_9 = lean_mk_string_unchecked("Attr", 4, 4);
x_10 = lean_mk_string_unchecked("extern", 6, 6);
lean_inc(x_10);
x_11 = l_Lean_Name_mkStr4(x_7, x_8, x_9, x_10);
x_12 = lean_box(1);
x_13 = lean_box(0);
lean_inc(x_11);
lean_inc(x_10);
x_14 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(x_14, 0, x_10);
lean_closure_set(x_14, 1, x_11);
lean_closure_set(x_14, 2, x_12);
lean_closure_set(x_14, 3, x_13);
x_15 = lean_unsigned_to_nat(1024u);
x_16 = lean_alloc_closure((void*)(l_Lean_Parser_nonReservedSymbol_parenthesizer___boxed), 7, 2);
lean_closure_set(x_16, 0, x_10);
lean_closure_set(x_16, 1, x_13);
x_17 = lean_alloc_closure((void*)(l_Lean_Parser_numLit_parenthesizer), 5, 0);
lean_inc(x_6);
x_18 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_18, 0, x_6);
lean_closure_set(x_18, 1, x_17);
x_19 = lean_alloc_closure((void*)(l_Lean_Parser_optional_parenthesizer), 6, 1);
lean_closure_set(x_19, 0, x_18);
x_20 = lean_alloc_closure((void*)(l_Lean_Parser_Attr_externEntry_parenthesizer), 5, 0);
x_21 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_21, 0, x_6);
lean_closure_set(x_21, 1, x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_Parser_many_parenthesizer), 6, 1);
lean_closure_set(x_22, 0, x_21);
x_23 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_23, 0, x_19);
lean_closure_set(x_23, 1, x_22);
x_24 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_24, 0, x_16);
lean_closure_set(x_24, 1, x_23);
x_25 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer), 8, 3);
lean_closure_set(x_25, 0, x_11);
lean_closure_set(x_25, 1, x_15);
lean_closure_set(x_25, 2, x_24);
x_26 = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(x_14, x_25, x_1, x_2, x_3, x_4, x_5);
return x_26;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Attr_extern_parenthesizer__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Attr", 4, 4);
x_6 = lean_mk_string_unchecked("extern", 6, 6);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("parenthesizer", 13, 13);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Attr_extern_parenthesizer), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
static lean_object* _init_l_Lean_Parser_Attr_tactic__alt() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Attr", 4, 4);
x_4 = lean_mk_string_unchecked("tactic_alt", 10, 10);
lean_inc(x_4);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_box(1);
x_7 = lean_box(0);
x_8 = lean_unbox(x_6);
x_9 = lean_unbox(x_7);
lean_inc(x_5);
x_10 = l_Lean_Parser_mkAntiquot(x_4, x_5, x_8, x_9);
x_11 = lean_unsigned_to_nat(1024u);
x_12 = l_Lean_Parser_symbol(x_4);
lean_dec(x_4);
x_13 = l_Lean_Parser_skip;
x_14 = l_Lean_Parser_ident;
x_15 = l_Lean_Parser_andthen(x_13, x_14);
x_16 = l_Lean_Parser_andthen(x_12, x_15);
lean_inc(x_5);
x_17 = l_Lean_Parser_leadingNode(x_5, x_11, x_16);
x_18 = l_Lean_Parser_withAntiquot(x_10, x_17);
x_19 = l_Lean_Parser_withCache(x_5, x_18);
return x_19;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Attr_tactic__alt__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = lean_mk_string_unchecked("attr", 4, 4);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Attr", 4, 4);
x_7 = lean_mk_string_unchecked("tactic_alt", 10, 10);
x_8 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_7);
x_9 = l_Lean_Parser_Attr_tactic__alt;
x_10 = lean_unsigned_to_nat(1000u);
x_11 = l_Lean_Parser_addBuiltinLeadingParser(x_3, x_8, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Attr_tactic__alt_docString__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Attr", 4, 4);
x_5 = lean_mk_string_unchecked("tactic_alt", 10, 10);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_mk_string_unchecked("Declare this tactic to be an alias or alternative form of an existing tactic.\n\nThis has the following effects:\n* The alias relationship is saved\n* The docstring is taken from the original tactic, if present\n", 207, 207);
x_8 = l_Lean_addBuiltinDocString(x_6, x_7, x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Attr", 4, 4);
x_5 = lean_mk_string_unchecked("tactic_alt", 10, 10);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(60u);
x_8 = lean_unsigned_to_nat(23u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(61u);
x_11 = lean_unsigned_to_nat(34u);
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
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_tactic__alt_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_Attr_simple_formatter___lam__0___boxed), 5, 0);
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
x_8 = lean_mk_string_unchecked("Parser", 6, 6);
x_9 = lean_mk_string_unchecked("Attr", 4, 4);
x_10 = lean_mk_string_unchecked("tactic_alt", 10, 10);
lean_inc(x_10);
x_11 = l_Lean_Name_mkStr4(x_7, x_8, x_9, x_10);
x_12 = lean_box(1);
x_13 = lean_box(0);
lean_inc(x_11);
lean_inc(x_10);
x_14 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(x_14, 0, x_10);
lean_closure_set(x_14, 1, x_11);
lean_closure_set(x_14, 2, x_12);
lean_closure_set(x_14, 3, x_13);
x_15 = lean_unsigned_to_nat(1024u);
x_16 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter), 6, 1);
lean_closure_set(x_16, 0, x_10);
x_17 = lean_alloc_closure((void*)(l_Lean_Parser_ident_formatter), 5, 0);
x_18 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_18, 0, x_6);
lean_closure_set(x_18, 1, x_17);
x_19 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_19, 0, x_16);
lean_closure_set(x_19, 1, x_18);
x_20 = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(x_20, 0, x_11);
lean_closure_set(x_20, 1, x_15);
lean_closure_set(x_20, 2, x_19);
x_21 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_14, x_20, x_1, x_2, x_3, x_4, x_5);
return x_21;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Attr_tactic__alt_formatter__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_formatterAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Attr", 4, 4);
x_6 = lean_mk_string_unchecked("tactic_alt", 10, 10);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("formatter", 9, 9);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Attr_tactic__alt_formatter), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_tactic__alt_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_Attr_simple_parenthesizer___lam__0___boxed), 5, 0);
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
x_8 = lean_mk_string_unchecked("Parser", 6, 6);
x_9 = lean_mk_string_unchecked("Attr", 4, 4);
x_10 = lean_mk_string_unchecked("tactic_alt", 10, 10);
lean_inc(x_10);
x_11 = l_Lean_Name_mkStr4(x_7, x_8, x_9, x_10);
x_12 = lean_box(1);
x_13 = lean_box(0);
lean_inc(x_11);
lean_inc(x_10);
x_14 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(x_14, 0, x_10);
lean_closure_set(x_14, 1, x_11);
lean_closure_set(x_14, 2, x_12);
lean_closure_set(x_14, 3, x_13);
x_15 = lean_unsigned_to_nat(1024u);
x_16 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___boxed), 6, 1);
lean_closure_set(x_16, 0, x_10);
x_17 = lean_alloc_closure((void*)(l_Lean_Parser_ident_parenthesizer), 5, 0);
x_18 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_18, 0, x_6);
lean_closure_set(x_18, 1, x_17);
x_19 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_19, 0, x_16);
lean_closure_set(x_19, 1, x_18);
x_20 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer), 8, 3);
lean_closure_set(x_20, 0, x_11);
lean_closure_set(x_20, 1, x_15);
lean_closure_set(x_20, 2, x_19);
x_21 = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(x_14, x_20, x_1, x_2, x_3, x_4, x_5);
return x_21;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Attr_tactic__alt_parenthesizer__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Attr", 4, 4);
x_6 = lean_mk_string_unchecked("tactic_alt", 10, 10);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("parenthesizer", 13, 13);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Attr_tactic__alt_parenthesizer), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
static lean_object* _init_l_Lean_Parser_Attr_tactic__tag() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Attr", 4, 4);
x_4 = lean_mk_string_unchecked("tactic_tag", 10, 10);
lean_inc(x_4);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_box(1);
x_7 = lean_box(0);
x_8 = lean_unbox(x_6);
x_9 = lean_unbox(x_7);
lean_inc(x_5);
x_10 = l_Lean_Parser_mkAntiquot(x_4, x_5, x_8, x_9);
x_11 = lean_unsigned_to_nat(1024u);
x_12 = l_Lean_Parser_symbol(x_4);
lean_dec(x_4);
x_13 = l_Lean_Parser_skip;
x_14 = l_Lean_Parser_ident;
x_15 = l_Lean_Parser_andthen(x_13, x_14);
x_16 = l_Lean_Parser_many1(x_15);
x_17 = l_Lean_Parser_andthen(x_12, x_16);
lean_inc(x_5);
x_18 = l_Lean_Parser_leadingNode(x_5, x_11, x_17);
x_19 = l_Lean_Parser_withAntiquot(x_10, x_18);
x_20 = l_Lean_Parser_withCache(x_5, x_19);
return x_20;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Attr_tactic__tag__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = lean_mk_string_unchecked("attr", 4, 4);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Attr", 4, 4);
x_7 = lean_mk_string_unchecked("tactic_tag", 10, 10);
x_8 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_7);
x_9 = l_Lean_Parser_Attr_tactic__tag;
x_10 = lean_unsigned_to_nat(1000u);
x_11 = l_Lean_Parser_addBuiltinLeadingParser(x_3, x_8, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Attr_tactic__tag_docString__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Attr", 4, 4);
x_5 = lean_mk_string_unchecked("tactic_tag", 10, 10);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_mk_string_unchecked("Add one or more tags to a tactic.\n\nTags should be applied to the canonical names for tactics.\n", 94, 94);
x_8 = l_Lean_addBuiltinDocString(x_6, x_7, x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Attr", 4, 4);
x_5 = lean_mk_string_unchecked("tactic_tag", 10, 10);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(68u);
x_8 = lean_unsigned_to_nat(23u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(69u);
x_11 = lean_unsigned_to_nat(42u);
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
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_tactic__tag_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_Attr_simple_formatter___lam__0___boxed), 5, 0);
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
x_8 = lean_mk_string_unchecked("Parser", 6, 6);
x_9 = lean_mk_string_unchecked("Attr", 4, 4);
x_10 = lean_mk_string_unchecked("tactic_tag", 10, 10);
lean_inc(x_10);
x_11 = l_Lean_Name_mkStr4(x_7, x_8, x_9, x_10);
x_12 = lean_box(1);
x_13 = lean_box(0);
lean_inc(x_11);
lean_inc(x_10);
x_14 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(x_14, 0, x_10);
lean_closure_set(x_14, 1, x_11);
lean_closure_set(x_14, 2, x_12);
lean_closure_set(x_14, 3, x_13);
x_15 = lean_unsigned_to_nat(1024u);
x_16 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter), 6, 1);
lean_closure_set(x_16, 0, x_10);
x_17 = lean_alloc_closure((void*)(l_Lean_Parser_ident_formatter), 5, 0);
x_18 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_18, 0, x_6);
lean_closure_set(x_18, 1, x_17);
x_19 = lean_alloc_closure((void*)(l_Lean_Parser_many1_formatter), 6, 1);
lean_closure_set(x_19, 0, x_18);
x_20 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_20, 0, x_16);
lean_closure_set(x_20, 1, x_19);
x_21 = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(x_21, 0, x_11);
lean_closure_set(x_21, 1, x_15);
lean_closure_set(x_21, 2, x_20);
x_22 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_14, x_21, x_1, x_2, x_3, x_4, x_5);
return x_22;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Attr_tactic__tag_formatter__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_formatterAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Attr", 4, 4);
x_6 = lean_mk_string_unchecked("tactic_tag", 10, 10);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("formatter", 9, 9);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Attr_tactic__tag_formatter), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Attr_tactic__tag_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_Attr_simple_parenthesizer___lam__0___boxed), 5, 0);
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
x_8 = lean_mk_string_unchecked("Parser", 6, 6);
x_9 = lean_mk_string_unchecked("Attr", 4, 4);
x_10 = lean_mk_string_unchecked("tactic_tag", 10, 10);
lean_inc(x_10);
x_11 = l_Lean_Name_mkStr4(x_7, x_8, x_9, x_10);
x_12 = lean_box(1);
x_13 = lean_box(0);
lean_inc(x_11);
lean_inc(x_10);
x_14 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(x_14, 0, x_10);
lean_closure_set(x_14, 1, x_11);
lean_closure_set(x_14, 2, x_12);
lean_closure_set(x_14, 3, x_13);
x_15 = lean_unsigned_to_nat(1024u);
x_16 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___boxed), 6, 1);
lean_closure_set(x_16, 0, x_10);
x_17 = lean_alloc_closure((void*)(l_Lean_Parser_ident_parenthesizer), 5, 0);
x_18 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_18, 0, x_6);
lean_closure_set(x_18, 1, x_17);
x_19 = lean_alloc_closure((void*)(l_Lean_Parser_many1_parenthesizer), 6, 1);
lean_closure_set(x_19, 0, x_18);
x_20 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_20, 0, x_16);
lean_closure_set(x_20, 1, x_19);
x_21 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer), 8, 3);
lean_closure_set(x_21, 0, x_11);
lean_closure_set(x_21, 1, x_15);
lean_closure_set(x_21, 2, x_20);
x_22 = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(x_14, x_21, x_1, x_2, x_3, x_4, x_5);
return x_22;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Attr_tactic__tag_parenthesizer__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Attr", 4, 4);
x_6 = lean_mk_string_unchecked("tactic_tag", 10, 10);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("parenthesizer", 13, 13);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Attr_tactic__tag_parenthesizer), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
lean_object* initialize_Lean_Parser_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Parser_Extra(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Parser_Attr(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Parser_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Extra(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
if (builtin) {res = l_Lean_Parser_initFn____x40_Lean_Parser_Attr___hyg_3_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l_Lean_Parser_initFn____x40_Lean_Parser_Attr___hyg_82_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_Priority_numPrio = _init_l_Lean_Parser_Priority_numPrio();
lean_mark_persistent(l_Lean_Parser_Priority_numPrio);
if (builtin) {res = l___regBuiltin_Lean_Parser_Priority_numPrio__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Priority_numPrio_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_Attr_simple = _init_l_Lean_Parser_Attr_simple();
lean_mark_persistent(l_Lean_Parser_Attr_simple);
if (builtin) {res = l___regBuiltin_Lean_Parser_Attr_simple__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Attr_simple_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Attr_simple_formatter__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_Attr_macro = _init_l_Lean_Parser_Attr_macro();
lean_mark_persistent(l_Lean_Parser_Attr_macro);
if (builtin) {res = l___regBuiltin_Lean_Parser_Attr_macro__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Attr_macro_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Attr_macro_formatter__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Attr_macro_parenthesizer__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_Attr_export = _init_l_Lean_Parser_Attr_export();
lean_mark_persistent(l_Lean_Parser_Attr_export);
if (builtin) {res = l___regBuiltin_Lean_Parser_Attr_export__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Attr_export_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Attr_export_formatter__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Attr_export_parenthesizer__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_Attr_recursor = _init_l_Lean_Parser_Attr_recursor();
lean_mark_persistent(l_Lean_Parser_Attr_recursor);
if (builtin) {res = l___regBuiltin_Lean_Parser_Attr_recursor__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Attr_recursor_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Attr_recursor_formatter__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Attr_recursor_parenthesizer__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_Attr_class = _init_l_Lean_Parser_Attr_class();
lean_mark_persistent(l_Lean_Parser_Attr_class);
if (builtin) {res = l___regBuiltin_Lean_Parser_Attr_class__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Attr_class_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Attr_class_formatter__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Attr_class_parenthesizer__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_Attr_instance = _init_l_Lean_Parser_Attr_instance();
lean_mark_persistent(l_Lean_Parser_Attr_instance);
if (builtin) {res = l___regBuiltin_Lean_Parser_Attr_instance__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Attr_instance_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Attr_instance_formatter__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Attr_instance_parenthesizer__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_Attr_default__instance = _init_l_Lean_Parser_Attr_default__instance();
lean_mark_persistent(l_Lean_Parser_Attr_default__instance);
if (builtin) {res = l___regBuiltin_Lean_Parser_Attr_default__instance__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Attr_default__instance_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Attr_default__instance_formatter__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Attr_default__instance_parenthesizer__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_Attr_specialize = _init_l_Lean_Parser_Attr_specialize();
lean_mark_persistent(l_Lean_Parser_Attr_specialize);
if (builtin) {res = l___regBuiltin_Lean_Parser_Attr_specialize__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Attr_specialize_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Attr_specialize_formatter__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Attr_specialize_parenthesizer__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_Attr_externEntry = _init_l_Lean_Parser_Attr_externEntry();
lean_mark_persistent(l_Lean_Parser_Attr_externEntry);
l_Lean_Parser_Attr_extern = _init_l_Lean_Parser_Attr_extern();
lean_mark_persistent(l_Lean_Parser_Attr_extern);
if (builtin) {res = l___regBuiltin_Lean_Parser_Attr_extern__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Attr_extern_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Attr_externEntry_formatter__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Attr_extern_formatter__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Attr_externEntry_parenthesizer__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Attr_extern_parenthesizer__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_Attr_tactic__alt = _init_l_Lean_Parser_Attr_tactic__alt();
lean_mark_persistent(l_Lean_Parser_Attr_tactic__alt);
if (builtin) {res = l___regBuiltin_Lean_Parser_Attr_tactic__alt__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Attr_tactic__alt_docString__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Attr_tactic__alt_formatter__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Attr_tactic__alt_parenthesizer__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_Attr_tactic__tag = _init_l_Lean_Parser_Attr_tactic__tag();
lean_mark_persistent(l_Lean_Parser_Attr_tactic__tag);
if (builtin) {res = l___regBuiltin_Lean_Parser_Attr_tactic__tag__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Attr_tactic__tag_docString__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Attr_tactic__tag_formatter__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Attr_tactic__tag_parenthesizer__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
