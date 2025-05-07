// Lean compiler output
// Module: Lean.Parser.Module
// Imports: Lean.Message Lean.Parser.Command
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___Lean_MessageLog_forM___at___Lean_Parser_testParseModuleAux_parse_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_identWithPartialTrailingDot;
lean_object* l_Lean_Parser_optional_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_findSomeRevM_x3f_find___at_____private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage_lastTrailing_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Module_module;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Parser_mkAntiquot_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_topLevelCommandParserFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Module_header_parenthesizer___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_SyntaxStack_empty;
lean_object* l_Lean_PrettyPrinter_Formatter_orelse_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Parser_Module_updateTokens_spec__0(lean_object*);
lean_object* l_Lean_Parser_addParserTokens(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Error_toString(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__1(lean_object*);
lean_object* l_Lean_Parser_many_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_testParseModuleAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_leadingNode(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_categoryParser(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Parser_optional(lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Parser_Module_import;
lean_object* l_Lean_Parser_andthenFn(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_updateLeading(lean_object*);
lean_object* l_Lean_Data_Trie_instInhabited(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Parser_parseHeader_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Module_all_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Module_header_formatter__1(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lean_Parser_ParserFn_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_getTokenTable(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_skip_parenthesizer___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Module_header_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_testParseModuleAux_parse___lam__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Module_all_formatter__1(lean_object*);
lean_object* l_Lean_Parser_mkAntiquot_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isAntiquot(lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Parser_parseCommand_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Parser_isTerminalCommand(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Parser_parseCommand_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Module_private_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Parser_parseCommand_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Module_prelude_formatter__1(lean_object*);
lean_object* l_Lean_Parser_commandParser_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM___at___Lean_Parser_testParseModuleAux_parse_spec__0___boxed(lean_object*, lean_object*, lean_object*);
uint32_t lean_uint32_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_testParseModuleAux_parse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Module_private;
LEAN_EXPORT lean_object* l_Lean_Parser_Module_moduleTk_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_PrettyPrinter_parenthesizerAttribute;
LEAN_EXPORT lean_object* l_Lean_Parser_parseCommand___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_identWithPartialTrailingDot_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Parser_mkParserState(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Module_all_parenthesizer__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Module_import_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_MessageLog_forM___at___Lean_Parser_testParseModuleAux_parse_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_tokenFn(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_allErrors(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Module_moduleTk_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ppLine_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkInputContext(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Module_header_parenthesizer___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_isTerminalCommand___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Subarray_findSomeRevM_x3f_find___at_____private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage_lastTrailing_spec__0___redArg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_symbol(lean_object*);
lean_object* l_Lean_Parser_symbol_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isMissing(lean_object*);
lean_object* l_Lean_Parser_SyntaxStack_toSubarray(lean_object*);
lean_object* l_Subarray_get___redArg(lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_symbol_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_withAntiquot(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Module_all;
uint8_t l_Lean_MessageLog_hasUnreported(lean_object*);
lean_object* l_Lean_Parser_many_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailInfo(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_MessageLog_forM___at___Lean_Parser_testParseModuleAux_parse_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_MessageLog_forM___at___Lean_Parser_testParseModuleAux_parse_spec__0_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Module_updateTokens(lean_object*);
lean_object* l_IO_println___at___Lean_Environment_displayStats_spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Parser_andthen(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_testParseFile(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedModuleParserState;
lean_object* l_Lean_Parser_atomic(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Module_import_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_commandParser_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_readFile(lean_object*, lean_object*);
lean_object* l_Lean_Parser_many(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Module_private_formatter__1(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Module_moduleTk_formatter__1(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Module_import_formatter__1(lean_object*);
lean_object* l_Lean_Parser_leadingNode_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_optional_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Module_all_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_MessageLog_forM___at___Lean_Parser_testParseModuleAux_parse_spec__0_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at___Lean_Parser_ParserState_mkNode_spec__0(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Module_prelude_parenthesizer__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Module_header_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_withCache(lean_object*, lean_object*);
lean_object* l_Lean_Parser_atomic_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Parser_parseHeader_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_skip;
lean_object* l_Lean_Parser_identWithPartialTrailingDot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM___at___Lean_Parser_testParseModuleAux_parse_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI(lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
uint8_t l_Lean_Parser_SyntaxStack_isEmpty(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Module_module_formatter__1(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_testParseModuleAux_parse___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_initCacheForInput(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_MessageLog_forM___at___Lean_Parser_testParseModuleAux_parse_spec__0_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getRange_x3f(lean_object*, uint8_t);
lean_object* l_Lean_PrettyPrinter_Formatter_andthen_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_findSomeRevM_x3f_find___at_____private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage_lastTrailing_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Module_header;
LEAN_EXPORT lean_object* l_Lean_Parser_Module_prelude_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Module_header_parenthesizer__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_size___redArg(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Module_module_parenthesizer__1(lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Parser_Module_import_parenthesizer___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_MessageLog_forM___at___Lean_Parser_testParseModuleAux_parse_spec__0_spec__0_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkAntiquot(lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage_lastTrailing(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Module_moduleTk;
lean_object* l_Lean_Name_mkStr1(lean_object*);
extern lean_object* l_Lean_PrettyPrinter_formatterAttribute;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_findSomeRevM_x3f_find___at_____private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage_lastTrailing_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Parser_whitespace(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_parseHeader(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Parser_Module_private_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Char_utf8Size(uint32_t);
lean_object* lean_mk_empty_environment(uint32_t, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Module_module_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Module_prelude_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_parseCommand(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Module_import_parenthesizer__1(lean_object*);
uint8_t l_instDecidableEqPos(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Module_module_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_testParseModule(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_SyntaxStack_back(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Module_prelude;
uint32_t l_Char_ofNat(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Module_private_parenthesizer__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___Lean_MessageLog_forM___at___Lean_Parser_testParseModuleAux_parse_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Message_toString(lean_object*, uint8_t, lean_object*);
static lean_object* _init_l_Lean_Parser_Module_moduleTk() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Module", 6, 6);
x_4 = lean_mk_string_unchecked("moduleTk", 8, 8);
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
x_12 = lean_mk_string_unchecked("module", 6, 6);
x_13 = l_Lean_Parser_symbol(x_12);
lean_dec(x_12);
lean_inc(x_5);
x_14 = l_Lean_Parser_leadingNode(x_5, x_11, x_13);
x_15 = l_Lean_Parser_withAntiquot(x_10, x_14);
x_16 = l_Lean_Parser_withCache(x_5, x_15);
return x_16;
}
}
static lean_object* _init_l_Lean_Parser_Module_prelude() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Module", 6, 6);
x_4 = lean_mk_string_unchecked("prelude", 7, 7);
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
static lean_object* _init_l_Lean_Parser_Module_private() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Module", 6, 6);
x_4 = lean_mk_string_unchecked("private", 7, 7);
lean_inc(x_4);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_box(0);
x_7 = lean_unbox(x_6);
x_8 = lean_unbox(x_6);
lean_inc(x_5);
x_9 = l_Lean_Parser_mkAntiquot(x_4, x_5, x_7, x_8);
x_10 = lean_unsigned_to_nat(1024u);
x_11 = l_Lean_Parser_symbol(x_4);
lean_dec(x_4);
lean_inc(x_5);
x_12 = l_Lean_Parser_leadingNode(x_5, x_10, x_11);
x_13 = l_Lean_Parser_withAntiquot(x_9, x_12);
x_14 = l_Lean_Parser_withCache(x_5, x_13);
return x_14;
}
}
static lean_object* _init_l_Lean_Parser_Module_all() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Module", 6, 6);
x_4 = lean_mk_string_unchecked("all", 3, 3);
lean_inc(x_4);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_box(0);
x_7 = lean_unbox(x_6);
x_8 = lean_unbox(x_6);
lean_inc(x_5);
x_9 = l_Lean_Parser_mkAntiquot(x_4, x_5, x_7, x_8);
x_10 = lean_unsigned_to_nat(1024u);
x_11 = l_Lean_Parser_symbol(x_4);
lean_dec(x_4);
lean_inc(x_5);
x_12 = l_Lean_Parser_leadingNode(x_5, x_10, x_11);
x_13 = l_Lean_Parser_withAntiquot(x_9, x_12);
x_14 = l_Lean_Parser_withCache(x_5, x_13);
return x_14;
}
}
static lean_object* _init_l_Lean_Parser_Module_import() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Module", 6, 6);
x_4 = lean_mk_string_unchecked("import", 6, 6);
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
x_12 = l_Lean_Parser_Module_private;
x_13 = l_Lean_Parser_optional(x_12);
x_14 = lean_mk_string_unchecked("import ", 7, 7);
x_15 = l_Lean_Parser_symbol(x_14);
lean_dec(x_14);
x_16 = l_Lean_Parser_andthen(x_13, x_15);
x_17 = l_Lean_Parser_atomic(x_16);
x_18 = l_Lean_Parser_Module_all;
x_19 = l_Lean_Parser_optional(x_18);
x_20 = l_Lean_Parser_identWithPartialTrailingDot;
x_21 = l_Lean_Parser_andthen(x_19, x_20);
x_22 = l_Lean_Parser_andthen(x_17, x_21);
lean_inc(x_5);
x_23 = l_Lean_Parser_leadingNode(x_5, x_11, x_22);
x_24 = l_Lean_Parser_withAntiquot(x_10, x_23);
x_25 = l_Lean_Parser_withCache(x_5, x_24);
return x_25;
}
}
static lean_object* _init_l_Lean_Parser_Module_header() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Module", 6, 6);
x_4 = lean_mk_string_unchecked("header", 6, 6);
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
x_12 = l_Lean_Parser_Module_moduleTk;
x_13 = l_Lean_Parser_skip;
x_14 = l_Lean_Parser_andthen(x_13, x_13);
x_15 = l_Lean_Parser_andthen(x_12, x_14);
x_16 = l_Lean_Parser_optional(x_15);
x_17 = l_Lean_Parser_Module_prelude;
x_18 = l_Lean_Parser_andthen(x_17, x_13);
x_19 = l_Lean_Parser_optional(x_18);
x_20 = l_Lean_Parser_Module_import;
x_21 = l_Lean_Parser_andthen(x_20, x_13);
x_22 = l_Lean_Parser_many(x_21);
x_23 = l_Lean_Parser_andthen(x_22, x_13);
x_24 = l_Lean_Parser_andthen(x_19, x_23);
x_25 = l_Lean_Parser_andthen(x_16, x_24);
lean_inc(x_5);
x_26 = l_Lean_Parser_leadingNode(x_5, x_11, x_25);
x_27 = l_Lean_Parser_withAntiquot(x_10, x_26);
x_28 = l_Lean_Parser_withCache(x_5, x_27);
return x_28;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_moduleTk_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("Parser", 6, 6);
x_8 = lean_mk_string_unchecked("Module", 6, 6);
x_9 = lean_mk_string_unchecked("moduleTk", 8, 8);
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
x_15 = lean_mk_string_unchecked("module", 6, 6);
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
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Module_moduleTk_formatter__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_formatterAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Module", 6, 6);
x_6 = lean_mk_string_unchecked("moduleTk", 8, 8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("formatter", 9, 9);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Module_moduleTk_formatter), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_prelude_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("Parser", 6, 6);
x_8 = lean_mk_string_unchecked("Module", 6, 6);
x_9 = lean_mk_string_unchecked("prelude", 7, 7);
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
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Module_prelude_formatter__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_formatterAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Module", 6, 6);
x_6 = lean_mk_string_unchecked("prelude", 7, 7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("formatter", 9, 9);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Module_prelude_formatter), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_private_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("Parser", 6, 6);
x_8 = lean_mk_string_unchecked("Module", 6, 6);
x_9 = lean_mk_string_unchecked("private", 7, 7);
lean_inc(x_9);
x_10 = l_Lean_Name_mkStr4(x_6, x_7, x_8, x_9);
x_11 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
x_12 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(x_12, 0, x_9);
lean_closure_set(x_12, 1, x_10);
lean_closure_set(x_12, 2, x_11);
lean_closure_set(x_12, 3, x_11);
x_13 = lean_unsigned_to_nat(1024u);
x_14 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter), 6, 1);
lean_closure_set(x_14, 0, x_9);
x_15 = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(x_15, 0, x_10);
lean_closure_set(x_15, 1, x_13);
lean_closure_set(x_15, 2, x_14);
x_16 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_12, x_15, x_1, x_2, x_3, x_4, x_5);
return x_16;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Module_private_formatter__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_formatterAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Module", 6, 6);
x_6 = lean_mk_string_unchecked("private", 7, 7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("formatter", 9, 9);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Module_private_formatter), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_all_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("Parser", 6, 6);
x_8 = lean_mk_string_unchecked("Module", 6, 6);
x_9 = lean_mk_string_unchecked("all", 3, 3);
lean_inc(x_9);
x_10 = l_Lean_Name_mkStr4(x_6, x_7, x_8, x_9);
x_11 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
x_12 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(x_12, 0, x_9);
lean_closure_set(x_12, 1, x_10);
lean_closure_set(x_12, 2, x_11);
lean_closure_set(x_12, 3, x_11);
x_13 = lean_unsigned_to_nat(1024u);
x_14 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter), 6, 1);
lean_closure_set(x_14, 0, x_9);
x_15 = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(x_15, 0, x_10);
lean_closure_set(x_15, 1, x_13);
lean_closure_set(x_15, 2, x_14);
x_16 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_12, x_15, x_1, x_2, x_3, x_4, x_5);
return x_16;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Module_all_formatter__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_formatterAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Module", 6, 6);
x_6 = lean_mk_string_unchecked("all", 3, 3);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("formatter", 9, 9);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Module_all_formatter), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_import_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("Parser", 6, 6);
x_8 = lean_mk_string_unchecked("Module", 6, 6);
x_9 = lean_mk_string_unchecked("import", 6, 6);
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
x_15 = lean_alloc_closure((void*)(l_Lean_Parser_Module_private_formatter), 5, 0);
x_16 = lean_alloc_closure((void*)(l_Lean_Parser_optional_formatter), 6, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = lean_mk_string_unchecked("import ", 7, 7);
x_18 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter), 6, 1);
lean_closure_set(x_18, 0, x_17);
x_19 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_19, 0, x_16);
lean_closure_set(x_19, 1, x_18);
x_20 = lean_alloc_closure((void*)(l_Lean_Parser_atomic_formatter), 6, 1);
lean_closure_set(x_20, 0, x_19);
x_21 = lean_alloc_closure((void*)(l_Lean_Parser_Module_all_formatter), 5, 0);
x_22 = lean_alloc_closure((void*)(l_Lean_Parser_optional_formatter), 6, 1);
lean_closure_set(x_22, 0, x_21);
x_23 = lean_alloc_closure((void*)(l_Lean_Parser_identWithPartialTrailingDot_formatter), 5, 0);
x_24 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_24, 0, x_22);
lean_closure_set(x_24, 1, x_23);
x_25 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_25, 0, x_20);
lean_closure_set(x_25, 1, x_24);
x_26 = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(x_26, 0, x_10);
lean_closure_set(x_26, 1, x_14);
lean_closure_set(x_26, 2, x_25);
x_27 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_13, x_26, x_1, x_2, x_3, x_4, x_5);
return x_27;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Module_import_formatter__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_formatterAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Module", 6, 6);
x_6 = lean_mk_string_unchecked("import", 6, 6);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("formatter", 9, 9);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Module_import_formatter), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_header_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("Parser", 6, 6);
x_8 = lean_mk_string_unchecked("Module", 6, 6);
x_9 = lean_mk_string_unchecked("header", 6, 6);
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
x_15 = lean_alloc_closure((void*)(l_Lean_Parser_Module_moduleTk_formatter), 5, 0);
x_16 = lean_alloc_closure((void*)(l_Lean_ppLine_formatter___boxed), 5, 0);
lean_inc_n(x_16, 2);
x_17 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_17, 0, x_16);
lean_closure_set(x_17, 1, x_16);
x_18 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_18, 0, x_15);
lean_closure_set(x_18, 1, x_17);
x_19 = lean_alloc_closure((void*)(l_Lean_Parser_optional_formatter), 6, 1);
lean_closure_set(x_19, 0, x_18);
x_20 = lean_alloc_closure((void*)(l_Lean_Parser_Module_prelude_formatter), 5, 0);
lean_inc(x_16);
x_21 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_21, 0, x_20);
lean_closure_set(x_21, 1, x_16);
x_22 = lean_alloc_closure((void*)(l_Lean_Parser_optional_formatter), 6, 1);
lean_closure_set(x_22, 0, x_21);
x_23 = lean_alloc_closure((void*)(l_Lean_Parser_Module_import_formatter), 5, 0);
lean_inc(x_16);
x_24 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_24, 0, x_23);
lean_closure_set(x_24, 1, x_16);
x_25 = lean_alloc_closure((void*)(l_Lean_Parser_many_formatter), 6, 1);
lean_closure_set(x_25, 0, x_24);
x_26 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_26, 0, x_25);
lean_closure_set(x_26, 1, x_16);
x_27 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_27, 0, x_22);
lean_closure_set(x_27, 1, x_26);
x_28 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_28, 0, x_19);
lean_closure_set(x_28, 1, x_27);
x_29 = lean_alloc_closure((void*)(l_Lean_Parser_leadingNode_formatter___boxed), 8, 3);
lean_closure_set(x_29, 0, x_10);
lean_closure_set(x_29, 1, x_14);
lean_closure_set(x_29, 2, x_28);
x_30 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_13, x_29, x_1, x_2, x_3, x_4, x_5);
return x_30;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Module_header_formatter__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_formatterAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Module", 6, 6);
x_6 = lean_mk_string_unchecked("header", 6, 6);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("formatter", 9, 9);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Module_header_formatter), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_module_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("Parser", 6, 6);
x_8 = lean_mk_string_unchecked("Module", 6, 6);
x_9 = lean_mk_string_unchecked("module", 6, 6);
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
x_15 = lean_alloc_closure((void*)(l_Lean_Parser_Module_header_formatter), 5, 0);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_alloc_closure((void*)(l_Lean_Parser_commandParser_formatter___boxed), 6, 1);
lean_closure_set(x_17, 0, x_16);
x_18 = lean_alloc_closure((void*)(l_Lean_ppLine_formatter___boxed), 5, 0);
lean_inc(x_18);
x_19 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_19, 0, x_18);
lean_closure_set(x_19, 1, x_18);
x_20 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_20, 0, x_17);
lean_closure_set(x_20, 1, x_19);
x_21 = lean_alloc_closure((void*)(l_Lean_Parser_many_formatter), 6, 1);
lean_closure_set(x_21, 0, x_20);
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
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Module_module_formatter__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_formatterAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Module", 6, 6);
x_6 = lean_mk_string_unchecked("module", 6, 6);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("formatter", 9, 9);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Module_module_formatter), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_moduleTk_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("Parser", 6, 6);
x_8 = lean_mk_string_unchecked("Module", 6, 6);
x_9 = lean_mk_string_unchecked("moduleTk", 8, 8);
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
x_15 = lean_mk_string_unchecked("module", 6, 6);
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
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Module", 6, 6);
x_6 = lean_mk_string_unchecked("moduleTk", 8, 8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("parenthesizer", 13, 13);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Module_moduleTk_parenthesizer), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_prelude_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("Parser", 6, 6);
x_8 = lean_mk_string_unchecked("Module", 6, 6);
x_9 = lean_mk_string_unchecked("prelude", 7, 7);
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
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Module_prelude_parenthesizer__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Module", 6, 6);
x_6 = lean_mk_string_unchecked("prelude", 7, 7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("parenthesizer", 13, 13);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Module_prelude_parenthesizer), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_private_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("Parser", 6, 6);
x_8 = lean_mk_string_unchecked("Module", 6, 6);
x_9 = lean_mk_string_unchecked("private", 7, 7);
lean_inc(x_9);
x_10 = l_Lean_Name_mkStr4(x_6, x_7, x_8, x_9);
x_11 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
x_12 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(x_12, 0, x_9);
lean_closure_set(x_12, 1, x_10);
lean_closure_set(x_12, 2, x_11);
lean_closure_set(x_12, 3, x_11);
x_13 = lean_unsigned_to_nat(1024u);
x_14 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___boxed), 6, 1);
lean_closure_set(x_14, 0, x_9);
x_15 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer), 8, 3);
lean_closure_set(x_15, 0, x_10);
lean_closure_set(x_15, 1, x_13);
lean_closure_set(x_15, 2, x_14);
x_16 = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(x_12, x_15, x_1, x_2, x_3, x_4, x_5);
return x_16;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Module_private_parenthesizer__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Module", 6, 6);
x_6 = lean_mk_string_unchecked("private", 7, 7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("parenthesizer", 13, 13);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Module_private_parenthesizer), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_all_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("Parser", 6, 6);
x_8 = lean_mk_string_unchecked("Module", 6, 6);
x_9 = lean_mk_string_unchecked("all", 3, 3);
lean_inc(x_9);
x_10 = l_Lean_Name_mkStr4(x_6, x_7, x_8, x_9);
x_11 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
x_12 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(x_12, 0, x_9);
lean_closure_set(x_12, 1, x_10);
lean_closure_set(x_12, 2, x_11);
lean_closure_set(x_12, 3, x_11);
x_13 = lean_unsigned_to_nat(1024u);
x_14 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___boxed), 6, 1);
lean_closure_set(x_14, 0, x_9);
x_15 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer), 8, 3);
lean_closure_set(x_15, 0, x_10);
lean_closure_set(x_15, 1, x_13);
lean_closure_set(x_15, 2, x_14);
x_16 = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(x_12, x_15, x_1, x_2, x_3, x_4, x_5);
return x_16;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Module_all_parenthesizer__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Module", 6, 6);
x_6 = lean_mk_string_unchecked("all", 3, 3);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("parenthesizer", 13, 13);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Module_all_parenthesizer), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_import_parenthesizer___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_import_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("Parser", 6, 6);
x_8 = lean_mk_string_unchecked("Module", 6, 6);
x_9 = lean_mk_string_unchecked("import", 6, 6);
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
x_15 = lean_alloc_closure((void*)(l_Lean_Parser_Module_private_parenthesizer), 5, 0);
x_16 = lean_alloc_closure((void*)(l_Lean_Parser_optional_parenthesizer), 6, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = lean_mk_string_unchecked("import ", 7, 7);
x_18 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer___boxed), 6, 1);
lean_closure_set(x_18, 0, x_17);
x_19 = lean_alloc_closure((void*)(l_Lean_Parser_Module_import_parenthesizer___lam__0), 7, 2);
lean_closure_set(x_19, 0, x_16);
lean_closure_set(x_19, 1, x_18);
x_20 = lean_alloc_closure((void*)(l_Lean_Parser_Module_all_parenthesizer), 5, 0);
x_21 = lean_alloc_closure((void*)(l_Lean_Parser_optional_parenthesizer), 6, 1);
lean_closure_set(x_21, 0, x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_Parser_identWithPartialTrailingDot_parenthesizer), 5, 0);
x_23 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_23, 0, x_21);
lean_closure_set(x_23, 1, x_22);
x_24 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_24, 0, x_19);
lean_closure_set(x_24, 1, x_23);
x_25 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer), 8, 3);
lean_closure_set(x_25, 0, x_10);
lean_closure_set(x_25, 1, x_14);
lean_closure_set(x_25, 2, x_24);
x_26 = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(x_13, x_25, x_1, x_2, x_3, x_4, x_5);
return x_26;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Module_import_parenthesizer__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Module", 6, 6);
x_6 = lean_mk_string_unchecked("import", 6, 6);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("parenthesizer", 13, 13);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Module_import_parenthesizer), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_header_parenthesizer___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Parenthesizer_skip_parenthesizer___redArg(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_header_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_Module_header_parenthesizer___lam__0___boxed), 5, 0);
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
x_8 = lean_mk_string_unchecked("Parser", 6, 6);
x_9 = lean_mk_string_unchecked("Module", 6, 6);
x_10 = lean_mk_string_unchecked("header", 6, 6);
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
x_16 = lean_alloc_closure((void*)(l_Lean_Parser_Module_moduleTk_parenthesizer), 5, 0);
lean_inc_n(x_6, 2);
x_17 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_17, 0, x_6);
lean_closure_set(x_17, 1, x_6);
x_18 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_18, 0, x_16);
lean_closure_set(x_18, 1, x_17);
x_19 = lean_alloc_closure((void*)(l_Lean_Parser_optional_parenthesizer), 6, 1);
lean_closure_set(x_19, 0, x_18);
x_20 = lean_alloc_closure((void*)(l_Lean_Parser_Module_prelude_parenthesizer), 5, 0);
lean_inc(x_6);
x_21 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_21, 0, x_20);
lean_closure_set(x_21, 1, x_6);
x_22 = lean_alloc_closure((void*)(l_Lean_Parser_optional_parenthesizer), 6, 1);
lean_closure_set(x_22, 0, x_21);
x_23 = lean_alloc_closure((void*)(l_Lean_Parser_Module_import_parenthesizer), 5, 0);
lean_inc(x_6);
x_24 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_24, 0, x_23);
lean_closure_set(x_24, 1, x_6);
x_25 = lean_alloc_closure((void*)(l_Lean_Parser_many_parenthesizer), 6, 1);
lean_closure_set(x_25, 0, x_24);
x_26 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_26, 0, x_25);
lean_closure_set(x_26, 1, x_6);
x_27 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_27, 0, x_22);
lean_closure_set(x_27, 1, x_26);
x_28 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_28, 0, x_19);
lean_closure_set(x_28, 1, x_27);
x_29 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer), 8, 3);
lean_closure_set(x_29, 0, x_11);
lean_closure_set(x_29, 1, x_15);
lean_closure_set(x_29, 2, x_28);
x_30 = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(x_14, x_29, x_1, x_2, x_3, x_4, x_5);
return x_30;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_header_parenthesizer___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_Module_header_parenthesizer___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Module_header_parenthesizer__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Module", 6, 6);
x_6 = lean_mk_string_unchecked("header", 6, 6);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("parenthesizer", 13, 13);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Module_header_parenthesizer), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_module_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_Module_header_parenthesizer___lam__0___boxed), 5, 0);
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
x_8 = lean_mk_string_unchecked("Parser", 6, 6);
x_9 = lean_mk_string_unchecked("Module", 6, 6);
x_10 = lean_mk_string_unchecked("module", 6, 6);
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
x_16 = lean_alloc_closure((void*)(l_Lean_Parser_Module_header_parenthesizer), 5, 0);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_alloc_closure((void*)(l_Lean_Parser_commandParser_parenthesizer), 6, 1);
lean_closure_set(x_18, 0, x_17);
lean_inc(x_6);
x_19 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_19, 0, x_6);
lean_closure_set(x_19, 1, x_6);
x_20 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_20, 0, x_18);
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
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_Module_module_parenthesizer__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Module", 6, 6);
x_6 = lean_mk_string_unchecked("module", 6, 6);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("parenthesizer", 13, 13);
x_9 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_Module_module_parenthesizer), 5, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_9, x_10, x_1);
return x_11;
}
}
static lean_object* _init_l_Lean_Parser_Module_module() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Module", 6, 6);
x_4 = lean_mk_string_unchecked("module", 6, 6);
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
x_12 = l_Lean_Parser_Module_header;
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_mk_string_unchecked("command", 7, 7);
x_15 = l_Lean_Name_mkStr1(x_14);
x_16 = l_Lean_Parser_categoryParser(x_15, x_13);
x_17 = l_Lean_Parser_skip;
x_18 = l_Lean_Parser_andthen(x_17, x_17);
x_19 = l_Lean_Parser_andthen(x_16, x_18);
x_20 = l_Lean_Parser_many(x_19);
x_21 = l_Lean_Parser_andthen(x_12, x_20);
lean_inc(x_5);
x_22 = l_Lean_Parser_leadingNode(x_5, x_11, x_21);
x_23 = l_Lean_Parser_withAntiquot(x_10, x_22);
x_24 = l_Lean_Parser_withCache(x_5, x_23);
return x_24;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Parser_Module_updateTokens_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Data_Trie_instInhabited(lean_box(0));
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Module_updateTokens(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Parser_Module_header;
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = l_Lean_Parser_addParserTokens(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
x_5 = lean_mk_string_unchecked("Lean.Parser.Module", 18, 18);
x_6 = lean_mk_string_unchecked("Lean.Parser.Module.updateTokens", 31, 31);
x_7 = lean_unsigned_to_nat(34u);
x_8 = lean_unsigned_to_nat(26u);
x_9 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_10 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
x_11 = l_panic___at___Lean_Parser_Module_updateTokens_spec__0(x_10);
return x_11;
}
else
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_4, 0);
lean_inc(x_12);
lean_dec(x_4);
return x_12;
}
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedModuleParserState() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_1);
x_4 = lean_unbox(x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_4);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Subarray_findSomeRevM_x3f_find___at_____private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage_lastTrailing_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_2, x_6);
lean_dec(x_2);
x_8 = l_Subarray_get___redArg(x_1, x_7);
x_9 = l_Lean_Syntax_getTailInfo(x_8);
lean_dec(x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_7);
x_10 = lean_ctor_get(x_9, 2);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
else
{
lean_dec(x_9);
x_2 = x_7;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_findSomeRevM_x3f_find___at_____private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage_lastTrailing_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Subarray_findSomeRevM_x3f_find___at_____private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage_lastTrailing_spec__0___redArg(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage_lastTrailing(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Parser_SyntaxStack_toSubarray(x_1);
x_3 = l_Subarray_size___redArg(x_2);
x_4 = l_Subarray_findSomeRevM_x3f_find___at_____private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage_lastTrailing_spec__0___redArg(x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Subarray_findSomeRevM_x3f_find___at_____private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage_lastTrailing_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Subarray_findSomeRevM_x3f_find___at_____private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage_lastTrailing_spec__0___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Subarray_findSomeRevM_x3f_find___at_____private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage_lastTrailing_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Subarray_findSomeRevM_x3f_find___at_____private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage_lastTrailing_spec__0(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
lean_dec(x_1);
lean_inc(x_7);
x_8 = l_Lean_FileMap_toPosition(x_7, x_4);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_22; 
lean_dec(x_7);
x_22 = lean_box(0);
x_9 = x_22;
goto block_21;
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_3);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_3, 0);
x_25 = l_Lean_FileMap_toPosition(x_7, x_24);
lean_dec(x_24);
lean_ctor_set(x_3, 0, x_25);
x_9 = x_3;
goto block_21;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_3, 0);
lean_inc(x_26);
lean_dec(x_3);
x_27 = l_Lean_FileMap_toPosition(x_7, x_26);
lean_dec(x_26);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_9 = x_28;
goto block_21;
}
}
block_21:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; 
x_10 = lean_box(1);
x_11 = lean_box(2);
x_12 = lean_box(0);
x_13 = lean_mk_string_unchecked("", 0, 0);
x_14 = l_Lean_Parser_Error_toString(x_2);
x_15 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = l_Lean_MessageData_ofFormat(x_15);
x_17 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_17, 0, x_6);
lean_ctor_set(x_17, 1, x_8);
lean_ctor_set(x_17, 2, x_9);
lean_ctor_set(x_17, 3, x_13);
lean_ctor_set(x_17, 4, x_16);
x_18 = lean_unbox(x_10);
lean_ctor_set_uint8(x_17, sizeof(void*)*5, x_18);
x_19 = lean_unbox(x_11);
lean_ctor_set_uint8(x_17, sizeof(void*)*5 + 1, x_19);
x_20 = lean_unbox(x_12);
lean_ctor_set_uint8(x_17, sizeof(void*)*5 + 2, x_20);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = lean_box(0);
x_37 = lean_ctor_get(x_4, 0);
lean_inc(x_37);
x_38 = l_Lean_Syntax_isMissing(x_37);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = l_Lean_Syntax_getRange_x3f(x_37, x_38);
lean_dec(x_37);
if (lean_obj_tag(x_39) == 0)
{
x_24 = x_4;
x_25 = x_36;
x_26 = x_2;
goto block_35;
}
else
{
uint8_t x_40; 
lean_dec(x_2);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_39, 0);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
lean_ctor_set(x_39, 0, x_43);
x_24 = x_4;
x_25 = x_39;
x_26 = x_42;
goto block_35;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_39, 0);
lean_inc(x_44);
lean_dec(x_39);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_24 = x_4;
x_25 = x_47;
x_26 = x_45;
goto block_35;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_37);
lean_dec(x_3);
x_48 = lean_box(0);
x_49 = l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___lam__0(x_1, x_4, x_36, x_2, x_48);
lean_dec(x_2);
return x_49;
}
block_23:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_5, 2);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_9);
lean_ctor_set(x_11, 2, x_10);
x_12 = l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage_lastTrailing(x_3);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
x_14 = l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___lam__0(x_1, x_11, x_6, x_8, x_13);
lean_dec(x_8);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_ctor_get(x_15, 2);
lean_inc(x_16);
x_17 = l_instDecidableEqPos(x_16, x_8);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_15);
x_18 = lean_box(0);
x_19 = l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___lam__0(x_1, x_11, x_6, x_8, x_18);
lean_dec(x_8);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_8);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_dec(x_15);
x_21 = lean_box(0);
x_22 = l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___lam__0(x_1, x_11, x_6, x_20, x_21);
lean_dec(x_20);
return x_22;
}
}
}
block_35:
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_24, 0);
lean_inc(x_27);
switch (lean_obj_tag(x_27)) {
case 2:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
x_29 = lean_mk_string_unchecked("unexpected token '", 18, 18);
x_30 = lean_string_append(x_29, x_28);
lean_dec(x_28);
x_31 = lean_mk_string_unchecked("'", 1, 1);
x_32 = lean_string_append(x_30, x_31);
lean_dec(x_31);
x_5 = x_24;
x_6 = x_25;
x_7 = x_27;
x_8 = x_26;
x_9 = x_32;
goto block_23;
}
case 3:
{
lean_object* x_33; 
x_33 = lean_mk_string_unchecked("unexpected identifier", 21, 21);
x_5 = x_24;
x_6 = x_25;
x_7 = x_27;
x_8 = x_26;
x_9 = x_33;
goto block_23;
}
default: 
{
lean_object* x_34; 
x_34 = lean_mk_string_unchecked("unexpected token", 16, 16);
x_5 = x_24;
x_6 = x_25;
x_7 = x_27;
x_8 = x_26;
x_9 = x_34;
goto block_23;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Parser_parseHeader_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_4, x_3);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; 
x_9 = lean_array_uget(x_2, x_4);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
lean_inc(x_1);
x_14 = l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage(x_1, x_11, x_12, x_13);
x_15 = l_Lean_MessageLog_add(x_14, x_5);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_usize_of_nat(x_16);
x_18 = lean_usize_add(x_4, x_17);
x_4 = x_18;
x_5 = x_15;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parseHeader(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_13; uint32_t x_14; lean_object* x_15; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_uint32_of_nat(x_13);
x_15 = lean_mk_empty_environment(x_14, x_2);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_59; uint8_t x_60; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_alloc_closure((void*)(l_Lean_Parser_whitespace), 2, 0);
x_19 = l_Lean_Parser_Module_header;
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
x_21 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_21, 0, x_18);
lean_closure_set(x_21, 1, x_20);
lean_inc(x_16);
x_22 = l_Lean_Parser_getTokenTable(x_16);
x_23 = l_Lean_Parser_Module_updateTokens(x_22);
x_24 = lean_box(0);
x_25 = lean_box(0);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_27, 0, x_16);
lean_ctor_set(x_27, 1, x_24);
lean_ctor_set(x_27, 2, x_25);
lean_ctor_set(x_27, 3, x_26);
x_28 = lean_ctor_get(x_1, 0);
lean_inc(x_28);
x_29 = l_Lean_Parser_mkParserState(x_28);
lean_dec(x_28);
lean_inc(x_1);
x_30 = l_Lean_Parser_ParserFn_run(x_21, x_1, x_27, x_23, x_29);
x_59 = lean_ctor_get(x_30, 0);
lean_inc(x_59);
x_60 = l_Lean_Parser_SyntaxStack_isEmpty(x_59);
if (x_60 == 0)
{
lean_object* x_61; 
x_61 = l_Lean_Parser_SyntaxStack_back(x_59);
lean_dec(x_59);
x_31 = x_61;
goto block_58;
}
else
{
lean_object* x_62; 
lean_dec(x_59);
x_62 = lean_box(0);
x_31 = x_62;
goto block_58;
}
block_58:
{
lean_object* x_32; lean_object* x_33; size_t x_34; lean_object* x_35; lean_object* x_36; size_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; size_t x_45; size_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_32 = lean_unsigned_to_nat(2u);
x_33 = lean_unsigned_to_nat(5u);
x_34 = lean_usize_of_nat(x_33);
x_35 = lean_usize_to_nat(x_34);
x_36 = lean_nat_pow(x_32, x_35);
lean_dec(x_35);
x_37 = lean_usize_of_nat(x_36);
lean_dec(x_36);
x_38 = lean_usize_to_nat(x_37);
x_39 = lean_mk_empty_array_with_capacity(x_38);
lean_dec(x_38);
lean_inc(x_39);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_41 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
lean_ctor_set(x_41, 2, x_13);
lean_ctor_set(x_41, 3, x_13);
lean_ctor_set_usize(x_41, 4, x_34);
x_42 = lean_box(0);
lean_inc(x_41);
x_43 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_41);
lean_ctor_set(x_43, 2, x_42);
lean_inc(x_30);
x_44 = l_Lean_Parser_ParserState_allErrors(x_30);
x_45 = lean_array_size(x_44);
x_46 = lean_usize_of_nat(x_13);
x_47 = l_Array_forIn_x27Unsafe_loop___at___Lean_Parser_parseHeader_spec__0(x_1, x_44, x_45, x_46, x_43, x_17);
lean_dec(x_44);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_ctor_get(x_30, 2);
lean_inc(x_50);
x_51 = lean_ctor_get(x_30, 4);
lean_inc(x_51);
lean_dec(x_30);
x_52 = lean_box(0);
x_53 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at___Lean_Parser_ParserState_mkNode_spec__0(x_51, x_52);
if (x_53 == 0)
{
lean_object* x_54; uint8_t x_55; 
x_54 = lean_box(1);
x_55 = lean_unbox(x_54);
x_3 = x_49;
x_4 = x_48;
x_5 = x_50;
x_6 = x_31;
x_7 = x_55;
goto block_12;
}
else
{
lean_object* x_56; uint8_t x_57; 
x_56 = lean_box(0);
x_57 = lean_unbox(x_56);
x_3 = x_49;
x_4 = x_48;
x_5 = x_50;
x_6 = x_31;
x_7 = x_57;
goto block_12;
}
}
}
else
{
uint8_t x_63; 
lean_dec(x_1);
x_63 = !lean_is_exclusive(x_15);
if (x_63 == 0)
{
return x_15;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_15, 0);
x_65 = lean_ctor_get(x_15, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_15);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
block_12:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set_uint8(x_8, sizeof(void*)*1, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_4);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Parser_parseHeader_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Array_forIn_x27Unsafe_loop___at___Lean_Parser_parseHeader_spec__0(x_1, x_2, x_7, x_8, x_5, x_6);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_2 = lean_mk_string_unchecked("", 0, 0);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_string_utf8_byte_size(x_2);
lean_inc(x_2);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
lean_inc(x_1);
lean_inc(x_5);
x_6 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_1);
lean_ctor_set(x_6, 2, x_5);
lean_ctor_set(x_6, 3, x_1);
x_7 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_2);
x_8 = lean_mk_string_unchecked("Lean", 4, 4);
x_9 = lean_mk_string_unchecked("Parser", 6, 6);
x_10 = lean_mk_string_unchecked("Command", 7, 7);
x_11 = lean_mk_string_unchecked("eoi", 3, 3);
x_12 = l_Lean_Name_mkStr4(x_8, x_9, x_10, x_11);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_mk_empty_array_with_capacity(x_13);
x_15 = lean_array_push(x_14, x_7);
x_16 = lean_box(2);
x_17 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_12);
lean_ctor_set(x_17, 2, x_15);
return x_17;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_isTerminalCommand(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_mk_string_unchecked("Lean", 4, 4);
x_11 = lean_mk_string_unchecked("Parser", 6, 6);
x_12 = lean_mk_string_unchecked("Command", 7, 7);
x_13 = lean_mk_string_unchecked("exit", 4, 4);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_14 = l_Lean_Name_mkStr4(x_10, x_11, x_12, x_13);
lean_inc(x_1);
x_15 = l_Lean_Syntax_isOfKind(x_1, x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_mk_string_unchecked("import", 6, 6);
x_17 = l_Lean_Name_mkStr4(x_10, x_11, x_12, x_16);
lean_inc(x_1);
x_18 = l_Lean_Syntax_isOfKind(x_1, x_17);
lean_dec(x_17);
x_2 = x_18;
goto block_9;
}
else
{
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_2 = x_15;
goto block_9;
}
block_9:
{
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Command", 7, 7);
x_6 = lean_mk_string_unchecked("eoi", 3, 3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = l_Lean_Syntax_isOfKind(x_1, x_7);
lean_dec(x_7);
return x_8;
}
else
{
lean_dec(x_1);
return x_2;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_isTerminalCommand___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Parser_isTerminalCommand(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_4 = l_Lean_Parser_SyntaxStack_empty;
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = l_Lean_Parser_initCacheForInput(x_6);
lean_dec(x_6);
x_8 = lean_box(0);
x_9 = lean_mk_empty_array_with_capacity(x_5);
lean_inc(x_3);
x_10 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_5);
lean_ctor_set(x_10, 2, x_3);
lean_ctor_set(x_10, 3, x_7);
lean_ctor_set(x_10, 4, x_8);
lean_ctor_set(x_10, 5, x_9);
x_11 = lean_box(0);
x_12 = lean_alloc_closure((void*)(l_Lean_Parser_tokenFn), 3, 1);
lean_closure_set(x_12, 0, x_11);
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
x_14 = l_Lean_Parser_getTokenTable(x_13);
x_15 = l_Lean_Parser_ParserFn_run(x_12, x_1, x_2, x_14, x_10);
x_16 = lean_ctor_get(x_15, 4);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
lean_dec(x_3);
x_17 = lean_ctor_get(x_15, 2);
lean_inc(x_17);
lean_dec(x_15);
return x_17;
}
else
{
lean_object* x_18; uint32_t x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_16);
lean_dec(x_15);
x_18 = lean_unsigned_to_nat(32u);
x_19 = l_Char_ofNat(x_18);
x_20 = l_Char_utf8Size(x_19);
x_21 = lean_nat_add(x_3, x_20);
lean_dec(x_20);
lean_dec(x_3);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_topLevelCommandParserFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_mk_string_unchecked("command", 7, 7);
x_5 = l_Lean_Name_mkStr1(x_4);
x_6 = l_Lean_Parser_categoryParser(x_5, x_3);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_apply_2(x_7, x_1, x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Parser_parseCommand_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_4, x_3);
if (x_6 == 0)
{
lean_dec(x_1);
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; 
x_7 = lean_array_uget(x_2, x_4);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
lean_inc(x_1);
x_12 = l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage(x_1, x_9, x_10, x_11);
x_13 = l_Lean_MessageLog_add(x_12, x_5);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_usize_of_nat(x_14);
x_16 = lean_usize_add(x_4, x_15);
x_4 = x_16;
x_5 = x_13;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Parser_parseCommand_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_13 = lean_ctor_get(x_3, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_3, 1);
lean_inc(x_14);
lean_dec(x_3);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
x_19 = lean_string_utf8_at_end(x_18, x_15);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; size_t x_34; size_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_60; lean_object* x_61; uint8_t x_62; uint8_t x_70; uint8_t x_84; uint8_t x_93; 
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_21 = lean_alloc_closure((void*)(l_Lean_Parser_whitespace), 2, 0);
x_22 = lean_alloc_closure((void*)(l_Lean_Parser_topLevelCommandParserFn), 2, 0);
x_23 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_23, 0, x_21);
lean_closure_set(x_23, 1, x_22);
x_24 = lean_ctor_get(x_2, 0);
lean_inc(x_24);
x_25 = l_Lean_Parser_getTokenTable(x_24);
x_26 = l_Lean_Parser_SyntaxStack_empty;
x_27 = lean_unsigned_to_nat(0u);
x_28 = l_Lean_Parser_initCacheForInput(x_18);
lean_dec(x_18);
x_29 = lean_box(0);
x_30 = lean_mk_empty_array_with_capacity(x_27);
lean_inc(x_15);
x_31 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_31, 0, x_26);
lean_ctor_set(x_31, 1, x_27);
lean_ctor_set(x_31, 2, x_15);
lean_ctor_set(x_31, 3, x_28);
lean_ctor_set(x_31, 4, x_29);
lean_ctor_set(x_31, 5, x_30);
lean_inc(x_2);
lean_inc(x_1);
x_32 = l_Lean_Parser_ParserFn_run(x_23, x_1, x_2, x_25, x_31);
x_33 = lean_ctor_get(x_32, 5);
lean_inc(x_33);
x_34 = lean_array_size(x_33);
x_35 = lean_usize_of_nat(x_27);
lean_inc(x_1);
x_36 = l_Array_forIn_x27Unsafe_loop___at___Lean_Parser_parseCommand_spec__0(x_1, x_33, x_34, x_35, x_13);
lean_dec(x_33);
x_37 = lean_ctor_get(x_32, 2);
lean_inc(x_37);
x_93 = lean_unbox(x_17);
if (x_93 == 0)
{
uint8_t x_94; 
x_94 = lean_unbox(x_17);
x_84 = x_94;
goto block_92;
}
else
{
lean_object* x_95; uint8_t x_96; 
x_95 = lean_ctor_get(x_32, 0);
lean_inc(x_95);
x_96 = l_Lean_Parser_SyntaxStack_isEmpty(x_95);
lean_dec(x_95);
if (x_96 == 0)
{
uint8_t x_97; 
x_97 = lean_unbox(x_17);
x_84 = x_97;
goto block_92;
}
else
{
x_84 = x_19;
goto block_92;
}
}
block_51:
{
lean_object* x_44; lean_object* x_45; 
lean_inc(x_39);
lean_inc(x_1);
x_44 = l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage(x_1, x_37, x_39, x_42);
x_45 = l_Lean_MessageLog_add(x_44, x_38);
if (x_41 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_43);
lean_dec(x_2);
lean_dec(x_1);
x_46 = lean_box(1);
x_47 = l_Lean_Parser_SyntaxStack_back(x_39);
lean_dec(x_39);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_40);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_45);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
else
{
lean_dec(x_39);
x_4 = x_40;
x_5 = x_45;
x_6 = x_43;
goto block_12;
}
}
block_59:
{
if (x_55 == 0)
{
x_38 = x_52;
x_39 = x_53;
x_40 = x_54;
x_41 = x_58;
x_42 = x_56;
x_43 = x_57;
goto block_51;
}
else
{
if (x_58 == 0)
{
x_38 = x_52;
x_39 = x_53;
x_40 = x_54;
x_41 = x_58;
x_42 = x_56;
x_43 = x_57;
goto block_51;
}
else
{
lean_dec(x_56);
lean_dec(x_53);
lean_dec(x_37);
x_4 = x_54;
x_5 = x_52;
x_6 = x_57;
goto block_12;
}
}
}
block_69:
{
lean_object* x_63; uint8_t x_64; 
x_63 = lean_ctor_get(x_32, 0);
lean_inc(x_63);
lean_dec(x_32);
x_64 = l_Lean_Parser_SyntaxStack_isEmpty(x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = l_Lean_Parser_SyntaxStack_back(x_63);
x_66 = l_Lean_Syntax_getPos_x3f(x_65, x_64);
lean_dec(x_65);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; uint8_t x_68; 
x_67 = lean_box(1);
x_68 = lean_unbox(x_67);
x_52 = x_36;
x_53 = x_63;
x_54 = x_61;
x_55 = x_62;
x_56 = x_60;
x_57 = x_20;
x_58 = x_68;
goto block_59;
}
else
{
lean_dec(x_66);
x_52 = x_36;
x_53 = x_63;
x_54 = x_61;
x_55 = x_62;
x_56 = x_60;
x_57 = x_20;
x_58 = x_64;
goto block_59;
}
}
else
{
x_52 = x_36;
x_53 = x_63;
x_54 = x_61;
x_55 = x_62;
x_56 = x_60;
x_57 = x_20;
x_58 = x_64;
goto block_59;
}
}
block_83:
{
lean_object* x_71; 
x_71 = lean_ctor_get(x_32, 4);
lean_inc(x_71);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_2);
lean_dec(x_1);
x_72 = lean_ctor_get(x_32, 0);
lean_inc(x_72);
lean_dec(x_32);
x_73 = l_Lean_Parser_SyntaxStack_back(x_72);
lean_dec(x_72);
x_74 = lean_box(x_70);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_73);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_37);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_36);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
else
{
lean_object* x_78; uint8_t x_79; 
x_78 = lean_ctor_get(x_71, 0);
lean_inc(x_78);
lean_dec(x_71);
x_79 = l_instDecidableEqPos(x_37, x_15);
lean_dec(x_15);
if (x_79 == 0)
{
uint8_t x_80; 
x_80 = lean_unbox(x_17);
lean_dec(x_17);
lean_inc(x_37);
x_60 = x_78;
x_61 = x_37;
x_62 = x_80;
goto block_69;
}
else
{
lean_object* x_81; uint8_t x_82; 
lean_inc(x_37);
lean_inc(x_2);
lean_inc(x_1);
x_81 = l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput(x_1, x_2, x_37);
x_82 = lean_unbox(x_17);
lean_dec(x_17);
x_60 = x_78;
x_61 = x_81;
x_62 = x_82;
goto block_69;
}
}
}
block_92:
{
if (x_84 == 0)
{
x_70 = x_84;
goto block_83;
}
else
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_85 = lean_ctor_get(x_32, 0);
lean_inc(x_85);
x_86 = l_Lean_Parser_SyntaxStack_back(x_85);
lean_dec(x_85);
x_87 = l_Lean_Syntax_isAntiquot(x_86);
lean_dec(x_86);
if (x_87 == 0)
{
x_70 = x_87;
goto block_83;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_32);
lean_dec(x_15);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_17);
lean_ctor_set(x_88, 1, x_20);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_37);
lean_ctor_set(x_89, 1, x_88);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_36);
lean_ctor_set(x_90, 1, x_89);
x_3 = x_90;
goto _start;
}
}
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_2);
lean_dec(x_1);
lean_inc(x_15);
x_98 = l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI(x_15);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_17);
lean_ctor_set(x_99, 1, x_98);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_15);
lean_ctor_set(x_100, 1, x_99);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_13);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
block_12:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_box(1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_9);
x_3 = x_10;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parseCommand(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get_uint8(x_3, sizeof(void*)*1);
x_7 = lean_box(0);
x_8 = lean_box(x_6);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
lean_inc(x_5);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Lean_Loop_forIn_loop___at___Lean_Parser_parseCommand_spec__1(x_1, x_2, x_11);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec(x_12);
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_13, 0);
x_18 = lean_ctor_get(x_13, 1);
lean_dec(x_18);
x_19 = !lean_is_exclusive(x_14);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_14, 0);
x_21 = lean_ctor_get(x_14, 1);
x_22 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_22, 0, x_17);
x_23 = lean_unbox(x_20);
lean_dec(x_20);
lean_ctor_set_uint8(x_22, sizeof(void*)*1, x_23);
lean_ctor_set(x_14, 1, x_15);
lean_ctor_set(x_14, 0, x_22);
lean_ctor_set(x_13, 0, x_21);
return x_13;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_14, 0);
x_25 = lean_ctor_get(x_14, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_14);
x_26 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_26, 0, x_17);
x_27 = lean_unbox(x_24);
lean_dec(x_24);
lean_ctor_set_uint8(x_26, sizeof(void*)*1, x_27);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_15);
lean_ctor_set(x_13, 1, x_28);
lean_ctor_set(x_13, 0, x_25);
return x_13;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; 
x_29 = lean_ctor_get(x_13, 0);
lean_inc(x_29);
lean_dec(x_13);
x_30 = lean_ctor_get(x_14, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_14, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_32 = x_14;
} else {
 lean_dec_ref(x_14);
 x_32 = lean_box(0);
}
x_33 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_33, 0, x_29);
x_34 = lean_unbox(x_30);
lean_dec(x_30);
lean_ctor_set_uint8(x_33, sizeof(void*)*1, x_34);
if (lean_is_scalar(x_32)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_32;
}
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_15);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_31);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Parser_parseCommand_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_forIn_x27Unsafe_loop___at___Lean_Parser_parseCommand_spec__0(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parseCommand___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_parseCommand(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_MessageLog_forM___at___Lean_Parser_testParseModuleAux_parse_spec__0_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_3, x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
x_8 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_9 = l_Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_MessageLog_forM___at___Lean_Parser_testParseModuleAux_parse_spec__0_spec__0_spec__0(x_1, x_8, x_6);
lean_dec(x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_usize_of_nat(x_12);
x_14 = lean_usize_add(x_3, x_13);
x_3 = x_14;
x_5 = x_10;
x_6 = x_11;
goto _start;
}
else
{
lean_dec(x_1);
return x_9;
}
}
else
{
lean_object* x_16; 
lean_dec(x_1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_5);
lean_ctor_set(x_16, 1, x_6);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_MessageLog_forM___at___Lean_Parser_testParseModuleAux_parse_spec__0_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_3, x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
x_8 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_9 = lean_apply_2(x_1, x_8, x_6);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_usize_of_nat(x_12);
x_14 = lean_usize_add(x_3, x_13);
x_3 = x_14;
x_5 = x_10;
x_6 = x_11;
goto _start;
}
else
{
lean_dec(x_1);
return x_9;
}
}
else
{
lean_object* x_16; 
lean_dec(x_1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_5);
lean_ctor_set(x_16, 1, x_6);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_MessageLog_forM___at___Lean_Parser_testParseModuleAux_parse_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_array_get_size(x_4);
x_7 = lean_box(0);
x_8 = lean_nat_dec_lt(x_5, x_6);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_3);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = lean_nat_dec_le(x_6, x_6);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
else
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_usize_of_nat(x_5);
x_13 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_14 = l_Array_foldlMUnsafe_fold___at___Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_MessageLog_forM___at___Lean_Parser_testParseModuleAux_parse_spec__0_spec__0_spec__0_spec__0(x_1, x_4, x_12, x_13, x_7, x_3);
return x_14;
}
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_2, 0);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_get_size(x_15);
x_18 = lean_box(0);
x_19 = lean_nat_dec_lt(x_16, x_17);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_17);
lean_dec(x_1);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_3);
return x_20;
}
else
{
uint8_t x_21; 
x_21 = lean_nat_dec_le(x_17, x_17);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_17);
lean_dec(x_1);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_18);
lean_ctor_set(x_22, 1, x_3);
return x_22;
}
else
{
size_t x_23; size_t x_24; lean_object* x_25; 
x_23 = lean_usize_of_nat(x_16);
x_24 = lean_usize_of_nat(x_17);
lean_dec(x_17);
x_25 = l_Array_foldlMUnsafe_fold___at___Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_MessageLog_forM___at___Lean_Parser_testParseModuleAux_parse_spec__0_spec__0_spec__0_spec__1(x_1, x_15, x_23, x_24, x_18, x_3);
return x_25;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___Lean_MessageLog_forM___at___Lean_Parser_testParseModuleAux_parse_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_1);
x_5 = l_Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_MessageLog_forM___at___Lean_Parser_testParseModuleAux_parse_spec__0_spec__0_spec__0(x_1, x_4, x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_7 = lean_ctor_get(x_5, 1);
x_8 = lean_ctor_get(x_5, 0);
lean_dec(x_8);
x_9 = lean_ctor_get(x_2, 1);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_get_size(x_9);
x_12 = lean_box(0);
x_13 = lean_nat_dec_lt(x_10, x_11);
if (x_13 == 0)
{
lean_dec(x_11);
lean_dec(x_1);
lean_ctor_set(x_5, 0, x_12);
return x_5;
}
else
{
uint8_t x_14; 
x_14 = lean_nat_dec_le(x_11, x_11);
if (x_14 == 0)
{
lean_dec(x_11);
lean_dec(x_1);
lean_ctor_set(x_5, 0, x_12);
return x_5;
}
else
{
size_t x_15; size_t x_16; lean_object* x_17; 
lean_free_object(x_5);
x_15 = lean_usize_of_nat(x_10);
x_16 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_17 = l_Array_foldlMUnsafe_fold___at___Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_MessageLog_forM___at___Lean_Parser_testParseModuleAux_parse_spec__0_spec__0_spec__0_spec__1(x_1, x_9, x_15, x_16, x_12, x_7);
return x_17;
}
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_18 = lean_ctor_get(x_5, 1);
lean_inc(x_18);
lean_dec(x_5);
x_19 = lean_ctor_get(x_2, 1);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_array_get_size(x_19);
x_22 = lean_box(0);
x_23 = lean_nat_dec_lt(x_20, x_21);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_21);
lean_dec(x_1);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_18);
return x_24;
}
else
{
uint8_t x_25; 
x_25 = lean_nat_dec_le(x_21, x_21);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_21);
lean_dec(x_1);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_22);
lean_ctor_set(x_26, 1, x_18);
return x_26;
}
else
{
size_t x_27; size_t x_28; lean_object* x_29; 
x_27 = lean_usize_of_nat(x_20);
x_28 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_29 = l_Array_foldlMUnsafe_fold___at___Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_MessageLog_forM___at___Lean_Parser_testParseModuleAux_parse_spec__0_spec__0_spec__0_spec__1(x_1, x_19, x_27, x_28, x_22, x_18);
return x_29;
}
}
}
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM___at___Lean_Parser_testParseModuleAux_parse_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_Lean_PersistentArray_forM___at___Lean_MessageLog_forM___at___Lean_Parser_testParseModuleAux_parse_spec__0_spec__0(x_2, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_testParseModuleAux_parse___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = l_Lean_Message_toString(x_2, x_1, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_IO_println___at___Lean_Environment_displayStats_spec__2(x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_testParseModuleAux_parse(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = lean_box(0);
x_8 = lean_box(0);
x_9 = lean_box(0);
lean_inc(x_1);
x_10 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_7);
lean_ctor_set(x_10, 2, x_8);
lean_ctor_set(x_10, 3, x_9);
lean_inc(x_2);
x_11 = l_Lean_Parser_parseCommand(x_2, x_10, x_3, x_4);
lean_dec(x_3);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_34; 
x_15 = lean_ctor_get(x_12, 0);
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
x_34 = l_Lean_Parser_isTerminalCommand(x_13);
if (x_34 == 0)
{
lean_object* x_35; 
lean_free_object(x_12);
x_35 = lean_array_push(x_5, x_13);
x_3 = x_15;
x_4 = x_16;
x_5 = x_35;
goto _start;
}
else
{
uint8_t x_37; 
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_2);
lean_dec(x_1);
x_37 = l_Lean_MessageLog_hasUnreported(x_16);
if (x_37 == 0)
{
if (x_34 == 0)
{
lean_free_object(x_12);
lean_dec(x_5);
x_17 = x_34;
goto block_33;
}
else
{
lean_dec(x_16);
lean_ctor_set(x_12, 1, x_6);
lean_ctor_set(x_12, 0, x_5);
return x_12;
}
}
else
{
lean_object* x_38; uint8_t x_39; 
lean_free_object(x_12);
lean_dec(x_5);
x_38 = lean_box(0);
x_39 = lean_unbox(x_38);
x_17 = x_39;
goto block_33;
}
}
block_33:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_box(x_17);
x_19 = lean_alloc_closure((void*)(l_Lean_Parser_testParseModuleAux_parse___lam__0___boxed), 3, 1);
lean_closure_set(x_19, 0, x_18);
x_20 = l_Lean_MessageLog_forM___at___Lean_Parser_testParseModuleAux_parse_spec__0(x_16, x_19, x_6);
lean_dec(x_16);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
x_23 = lean_mk_string_unchecked("failed to parse file", 20, 20);
x_24 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set_tag(x_20, 1);
lean_ctor_set(x_20, 0, x_24);
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_dec(x_20);
x_26 = lean_mk_string_unchecked("failed to parse file", 20, 20);
x_27 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_25);
return x_28;
}
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_20);
if (x_29 == 0)
{
return x_20;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_20, 0);
x_31 = lean_ctor_get(x_20, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_20);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
else
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; uint8_t x_56; 
x_40 = lean_ctor_get(x_12, 0);
x_41 = lean_ctor_get(x_12, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_12);
lean_inc(x_13);
x_56 = l_Lean_Parser_isTerminalCommand(x_13);
if (x_56 == 0)
{
lean_object* x_57; 
x_57 = lean_array_push(x_5, x_13);
x_3 = x_40;
x_4 = x_41;
x_5 = x_57;
goto _start;
}
else
{
uint8_t x_59; 
lean_dec(x_40);
lean_dec(x_13);
lean_dec(x_2);
lean_dec(x_1);
x_59 = l_Lean_MessageLog_hasUnreported(x_41);
if (x_59 == 0)
{
if (x_56 == 0)
{
lean_dec(x_5);
x_42 = x_56;
goto block_55;
}
else
{
lean_object* x_60; 
lean_dec(x_41);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_5);
lean_ctor_set(x_60, 1, x_6);
return x_60;
}
}
else
{
lean_object* x_61; uint8_t x_62; 
lean_dec(x_5);
x_61 = lean_box(0);
x_62 = lean_unbox(x_61);
x_42 = x_62;
goto block_55;
}
}
block_55:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_box(x_42);
x_44 = lean_alloc_closure((void*)(l_Lean_Parser_testParseModuleAux_parse___lam__0___boxed), 3, 1);
lean_closure_set(x_44, 0, x_43);
x_45 = l_Lean_MessageLog_forM___at___Lean_Parser_testParseModuleAux_parse_spec__0(x_41, x_44, x_6);
lean_dec(x_41);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_47 = x_45;
} else {
 lean_dec_ref(x_45);
 x_47 = lean_box(0);
}
x_48 = lean_mk_string_unchecked("failed to parse file", 20, 20);
x_49 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_49, 0, x_48);
if (lean_is_scalar(x_47)) {
 x_50 = lean_alloc_ctor(1, 2, 0);
} else {
 x_50 = x_47;
 lean_ctor_set_tag(x_50, 1);
}
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_46);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_45, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_45, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_53 = x_45;
} else {
 lean_dec_ref(x_45);
 x_53 = lean_box(0);
}
if (lean_is_scalar(x_53)) {
 x_54 = lean_alloc_ctor(1, 2, 0);
} else {
 x_54 = x_53;
}
lean_ctor_set(x_54, 0, x_51);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_MessageLog_forM___at___Lean_Parser_testParseModuleAux_parse_spec__0_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Array_foldlMUnsafe_fold___at___Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_MessageLog_forM___at___Lean_Parser_testParseModuleAux_parse_spec__0_spec__0_spec__0_spec__0(x_1, x_2, x_7, x_8, x_5, x_6);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_MessageLog_forM___at___Lean_Parser_testParseModuleAux_parse_spec__0_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Array_foldlMUnsafe_fold___at___Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_MessageLog_forM___at___Lean_Parser_testParseModuleAux_parse_spec__0_spec__0_spec__0_spec__1(x_1, x_2, x_7, x_8, x_5, x_6);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_MessageLog_forM___at___Lean_Parser_testParseModuleAux_parse_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_MessageLog_forM___at___Lean_Parser_testParseModuleAux_parse_spec__0_spec__0_spec__0(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___Lean_MessageLog_forM___at___Lean_Parser_testParseModuleAux_parse_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentArray_forM___at___Lean_MessageLog_forM___at___Lean_Parser_testParseModuleAux_parse_spec__0_spec__0(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM___at___Lean_Parser_testParseModuleAux_parse_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_MessageLog_forM___at___Lean_Parser_testParseModuleAux_parse_spec__0(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_testParseModuleAux_parse___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_Parser_testParseModuleAux_parse___lam__0(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_testParseModuleAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_testParseModuleAux_parse(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_testParseModule(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_box(1);
x_6 = lean_unbox(x_5);
x_7 = l_Lean_Parser_mkInputContext(x_3, x_2, x_6);
lean_inc(x_7);
x_8 = l_Lean_Parser_parseHeader(x_7, x_4);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_mk_empty_array_with_capacity(x_15);
x_17 = l_Lean_Parser_testParseModuleAux_parse(x_1, x_7, x_13, x_14, x_16, x_11);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_mk_string_unchecked("Lean", 4, 4);
x_21 = lean_mk_string_unchecked("Parser", 6, 6);
x_22 = lean_mk_string_unchecked("Module", 6, 6);
x_23 = lean_mk_string_unchecked("module", 6, 6);
x_24 = l_Lean_Name_mkStr4(x_20, x_21, x_22, x_23);
x_25 = lean_mk_string_unchecked("null", 4, 4);
x_26 = l_Lean_Name_mkStr1(x_25);
x_27 = lean_box(2);
x_28 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
lean_ctor_set(x_28, 2, x_19);
x_29 = lean_unsigned_to_nat(2u);
x_30 = lean_mk_empty_array_with_capacity(x_29);
x_31 = lean_array_push(x_30, x_12);
x_32 = lean_array_push(x_31, x_28);
x_33 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_33, 0, x_27);
lean_ctor_set(x_33, 1, x_24);
lean_ctor_set(x_33, 2, x_32);
x_34 = l_Lean_Syntax_updateLeading(x_33);
lean_ctor_set(x_17, 0, x_34);
return x_17;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_35 = lean_ctor_get(x_17, 0);
x_36 = lean_ctor_get(x_17, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_17);
x_37 = lean_mk_string_unchecked("Lean", 4, 4);
x_38 = lean_mk_string_unchecked("Parser", 6, 6);
x_39 = lean_mk_string_unchecked("Module", 6, 6);
x_40 = lean_mk_string_unchecked("module", 6, 6);
x_41 = l_Lean_Name_mkStr4(x_37, x_38, x_39, x_40);
x_42 = lean_mk_string_unchecked("null", 4, 4);
x_43 = l_Lean_Name_mkStr1(x_42);
x_44 = lean_box(2);
x_45 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
lean_ctor_set(x_45, 2, x_35);
x_46 = lean_unsigned_to_nat(2u);
x_47 = lean_mk_empty_array_with_capacity(x_46);
x_48 = lean_array_push(x_47, x_12);
x_49 = lean_array_push(x_48, x_45);
x_50 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_50, 0, x_44);
lean_ctor_set(x_50, 1, x_41);
lean_ctor_set(x_50, 2, x_49);
x_51 = l_Lean_Syntax_updateLeading(x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_36);
return x_52;
}
}
else
{
uint8_t x_53; 
lean_dec(x_12);
x_53 = !lean_is_exclusive(x_17);
if (x_53 == 0)
{
return x_17;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_17, 0);
x_55 = lean_ctor_get(x_17, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_17);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_7);
lean_dec(x_1);
x_57 = !lean_is_exclusive(x_8);
if (x_57 == 0)
{
return x_8;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_8, 0);
x_59 = lean_ctor_get(x_8, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_8);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_testParseFile(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_readFile(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_Lean_Parser_testParseModule(x_1, x_2, x_5, x_6);
return x_7;
}
else
{
uint8_t x_8; 
lean_dec(x_2);
lean_dec(x_1);
x_8 = !lean_is_exclusive(x_4);
if (x_8 == 0)
{
return x_4;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_4);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
}
}
lean_object* initialize_Lean_Message(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Parser_Command(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Parser_Module(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Message(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Command(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Module_moduleTk = _init_l_Lean_Parser_Module_moduleTk();
lean_mark_persistent(l_Lean_Parser_Module_moduleTk);
l_Lean_Parser_Module_prelude = _init_l_Lean_Parser_Module_prelude();
lean_mark_persistent(l_Lean_Parser_Module_prelude);
l_Lean_Parser_Module_private = _init_l_Lean_Parser_Module_private();
lean_mark_persistent(l_Lean_Parser_Module_private);
l_Lean_Parser_Module_all = _init_l_Lean_Parser_Module_all();
lean_mark_persistent(l_Lean_Parser_Module_all);
l_Lean_Parser_Module_import = _init_l_Lean_Parser_Module_import();
lean_mark_persistent(l_Lean_Parser_Module_import);
l_Lean_Parser_Module_header = _init_l_Lean_Parser_Module_header();
lean_mark_persistent(l_Lean_Parser_Module_header);
if (builtin) {res = l___regBuiltin_Lean_Parser_Module_moduleTk_formatter__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Module_prelude_formatter__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Module_private_formatter__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Module_all_formatter__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Module_import_formatter__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Module_header_formatter__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Module_module_formatter__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Module_moduleTk_parenthesizer__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Module_prelude_parenthesizer__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Module_private_parenthesizer__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Module_all_parenthesizer__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Module_import_parenthesizer__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Module_header_parenthesizer__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Parser_Module_module_parenthesizer__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_Module_module = _init_l_Lean_Parser_Module_module();
lean_mark_persistent(l_Lean_Parser_Module_module);
l_Lean_Parser_instInhabitedModuleParserState = _init_l_Lean_Parser_instInhabitedModuleParserState();
lean_mark_persistent(l_Lean_Parser_instInhabitedModuleParserState);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
