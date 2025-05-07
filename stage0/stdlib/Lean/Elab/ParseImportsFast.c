// Lean compiler output
// Module: Lean.Elab.ParseImportsFast
// Imports: Lean.Parser.Module
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_printImportsJson_spec__0(size_t, size_t, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore_go___at___Lean_ParseImports_main_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_isIdCont___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore_go___at___Lean_ParseImports_main_spec__0___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeWhile___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeWhile___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore_go___at___Lean_ParseImports_main_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonImport___lam__0____x40_Lean_Elab_ParseImportsFast___hyg_1380_(lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToJsonImport__1;
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_mkEOIError___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_andthen(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore_go___at___Lean_ParseImports_main_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_setImportAll___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_keyword___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_moduleIdent_parse(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_moduleIdent___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_isIdRestFast___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportsResult____x40_Lean_Elab_ParseImportsFast___hyg_1680__spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_mkError___boxed(lean_object*, lean_object*);
extern uint32_t l_Lean_idBeginEscape;
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_setPos___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_ParseImportsFast_0__Lean_toJsonParseImportsResult____x40_Lean_Elab_ParseImportsFast___hyg_1467__spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_setIsExported___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_pushImport(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore_go___at___Lean_ParseImports_main_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_setIsExported(uint8_t, lean_object*, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1625__spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_setImportAll___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___at___Lean_ParseImports_moduleIdent_parse_spec__1___boxed(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
uint32_t lean_uint32_of_nat(lean_object*);
lean_object* l_Array_empty(lean_object*);
LEAN_EXPORT uint8_t l_Lean_ParseImports_takeWhile___lam__0(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportsResult____x40_Lean_Elab_ParseImportsFast___hyg_1680_(lean_object*);
lean_object* l_Array_shrink___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_whitespace(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_instAndThenParser___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_setImportAll(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_finishCommentBlock_eoi___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_flatMapTR_go___at_____private_Lean_Server_Rpc_Basic_0__Lean_Lsp_toJsonRpcRef____x40_Lean_Server_Rpc_Basic___hyg_173__spec__0(lean_object*, lean_object*);
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_next___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_ParseImports_isIdCont(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore_go___at___Lean_ParseImports_main_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_setIsExported___redArg(uint8_t, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_printImportsJson_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_finishCommentBlock___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at_____private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1625__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___at___Lean_ParseImports_moduleIdent_parse_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_many(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonImport___lam__0____x40_Lean_Elab_ParseImportsFast___hyg_1380____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_keyword(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonParseImportsResult____x40_Lean_Elab_ParseImportsFast___hyg_1467_(lean_object*);
lean_object* l_IO_println___at___Lean_Environment_displayStats_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore_go___at___Lean_ParseImports_main_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_many___at___Lean_ParseImports_many___at___Lean_ParseImports_main_spec__5_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_mkEOIError(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonImport____x40_Lean_Elab_ParseImportsFast___hyg_1380_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_setIsExported___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_readFile(lean_object*, lean_object*);
uint8_t l_Lean_isLetterLike(uint32_t);
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_next_x27___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_instAndThenParser;
extern uint32_t l_Lean_idEndEscape;
LEAN_EXPORT lean_object* l_Lean_instToJsonParseImportsResult;
LEAN_EXPORT lean_object* l_Lean_ParseImports_instInhabitedParser;
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_next_x27(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_next_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_isIdRestCold___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___at___Lean_ParseImports_moduleIdent_parse_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_mkError(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___at___Lean_ParseImports_whitespace_spec__0(lean_object*, lean_object*);
uint8_t l_Lean_isSubScriptAlnum(uint32_t);
LEAN_EXPORT lean_object* l_Lean_ParseImports_finishCommentBlock_eoi(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_many___at___Lean_ParseImports_main_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore_go___at___Lean_ParseImports_main_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_parseImports_x27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1625_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore_go___at___Lean_ParseImports_main_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_keyword___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore_go___at___Lean_ParseImports_main_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___at___Lean_ParseImports_whitespace_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore_go___at___Lean_ParseImports_main_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_finishCommentBlock(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_main(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_moduleIdent(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToJsonPrintImportsResult;
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore_go___at___Lean_ParseImports_main_spec__0___lam__0(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1625__spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT uint8_t l_Lean_ParseImports_isIdRestCold(uint32_t);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportsResult____x40_Lean_Elab_ParseImportsFast___hyg_1680__spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___at___Lean_ParseImports_moduleIdent_parse_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_next(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_instInhabitedParser___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_ParseImportsFast_0__Lean_toJsonParseImportsResult____x40_Lean_Elab_ParseImportsFast___hyg_1467__spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_instInhabitedParser___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_setImportAll___redArg(uint8_t, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_ParseImports_instInhabitedState;
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore_go___at___Lean_ParseImports_main_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_moduleIdent___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore_go___at___Lean_ParseImports_main_spec__3___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore_go___at___Lean_ParseImports_main_spec__1___lam__0(uint8_t, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_setPos(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeWhile(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore_go___at___Lean_ParseImports_main_spec__3___lam__0(lean_object*, lean_object*);
uint8_t l_instDecidableEqChar(uint32_t, uint32_t);
LEAN_EXPORT lean_object* lean_print_imports_json(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_whitespace___boxed(lean_object*, lean_object*);
uint32_t l_Char_ofNat(lean_object*);
LEAN_EXPORT uint8_t l_Lean_ParseImports_isIdRestFast(uint32_t);
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_next_x27___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToJsonPrintImportResult;
static lean_object* _init_l_Lean_ParseImports_instInhabitedState() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_7; uint8_t x_8; 
x_1 = l_Array_empty(lean_box(0));
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_box(0);
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
x_6 = lean_unbox(x_4);
lean_ctor_set_uint8(x_5, sizeof(void*)*3, x_6);
x_7 = lean_unbox(x_4);
lean_ctor_set_uint8(x_5, sizeof(void*)*3 + 1, x_7);
x_8 = lean_unbox(x_4);
lean_ctor_set_uint8(x_5, sizeof(void*)*3 + 2, x_8);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_instInhabitedParser___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_2);
return x_2;
}
}
static lean_object* _init_l_Lean_ParseImports_instInhabitedParser() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_ParseImports_instInhabitedParser___lam__0___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_instInhabitedParser___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_ParseImports_instInhabitedParser___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_setPos(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_6; uint8_t x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 2);
x_5 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_6 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 1);
x_7 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 2);
lean_inc(x_4);
lean_inc(x_3);
x_8 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_2);
lean_ctor_set(x_8, 2, x_4);
lean_ctor_set_uint8(x_8, sizeof(void*)*3, x_5);
lean_ctor_set_uint8(x_8, sizeof(void*)*3 + 1, x_6);
lean_ctor_set_uint8(x_8, sizeof(void*)*3 + 2, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_setPos___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_ParseImports_State_setPos(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_mkError(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_2);
x_6 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_7 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 1);
x_8 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 2);
lean_inc(x_4);
lean_inc(x_3);
x_9 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_4);
lean_ctor_set(x_9, 2, x_5);
lean_ctor_set_uint8(x_9, sizeof(void*)*3, x_6);
lean_ctor_set_uint8(x_9, sizeof(void*)*3 + 1, x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*3 + 2, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_mkError___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_ParseImports_State_mkError(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_mkEOIError(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_2);
x_6 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_7 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 1);
x_8 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 2);
lean_inc(x_4);
lean_inc(x_3);
x_9 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_4);
lean_ctor_set(x_9, 2, x_5);
lean_ctor_set_uint8(x_9, sizeof(void*)*3, x_6);
lean_ctor_set_uint8(x_9, sizeof(void*)*3 + 1, x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*3 + 2, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_mkEOIError___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_ParseImports_State_mkEOIError(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_next(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_string_utf8_next(x_2, x_3);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_8 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 1);
x_9 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 2);
lean_inc(x_6);
lean_inc(x_4);
x_10 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_5);
lean_ctor_set(x_10, 2, x_6);
lean_ctor_set_uint8(x_10, sizeof(void*)*3, x_7);
lean_ctor_set_uint8(x_10, sizeof(void*)*3 + 1, x_8);
lean_ctor_set_uint8(x_10, sizeof(void*)*3 + 2, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_next___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_ParseImports_State_next(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_next_x27___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_string_utf8_next_fast(x_2, x_3);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_8 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 1);
x_9 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 2);
lean_inc(x_6);
lean_inc(x_4);
x_10 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_5);
lean_ctor_set(x_10, 2, x_6);
lean_ctor_set_uint8(x_10, sizeof(void*)*3, x_7);
lean_ctor_set_uint8(x_10, sizeof(void*)*3 + 1, x_8);
lean_ctor_set_uint8(x_10, sizeof(void*)*3 + 2, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_next_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_string_utf8_next_fast(x_2, x_3);
x_7 = lean_ctor_get(x_1, 2);
x_8 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_9 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 1);
x_10 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 2);
lean_inc(x_7);
lean_inc(x_5);
x_11 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_6);
lean_ctor_set(x_11, 2, x_7);
lean_ctor_set_uint8(x_11, sizeof(void*)*3, x_8);
lean_ctor_set_uint8(x_11, sizeof(void*)*3 + 1, x_9);
lean_ctor_set_uint8(x_11, sizeof(void*)*3 + 2, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_next_x27___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_ParseImports_State_next_x27___redArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_next_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_ParseImports_State_next_x27(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_finishCommentBlock_eoi(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("unterminated comment", 20, 20);
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_2);
x_6 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_7 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 1);
x_8 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 2);
lean_inc(x_4);
lean_inc(x_3);
x_9 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_4);
lean_ctor_set(x_9, 2, x_5);
lean_ctor_set_uint8(x_9, sizeof(void*)*3, x_6);
lean_ctor_set_uint8(x_9, sizeof(void*)*3 + 1, x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*3 + 2, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_finishCommentBlock_eoi___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_ParseImports_finishCommentBlock_eoi(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_finishCommentBlock(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_5 = lean_string_utf8_at_end(x_2, x_4);
if (x_5 == 0)
{
uint32_t x_6; lean_object* x_7; lean_object* x_8; uint32_t x_9; uint8_t x_10; 
x_6 = lean_string_utf8_get_fast(x_2, x_4);
x_7 = lean_string_utf8_next_fast(x_2, x_4);
lean_dec(x_4);
x_8 = lean_unsigned_to_nat(45u);
x_9 = l_Char_ofNat(x_8);
x_10 = l_instDecidableEqChar(x_6, x_9);
if (x_10 == 0)
{
lean_object* x_11; uint32_t x_12; uint8_t x_13; 
x_11 = lean_unsigned_to_nat(47u);
x_12 = l_Char_ofNat(x_11);
x_13 = l_instDecidableEqChar(x_6, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_3, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_3, 2);
lean_inc(x_15);
x_16 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_17 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 1);
x_18 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 2);
lean_dec(x_3);
x_19 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_19, 0, x_14);
lean_ctor_set(x_19, 1, x_7);
lean_ctor_set(x_19, 2, x_15);
lean_ctor_set_uint8(x_19, sizeof(void*)*3, x_16);
lean_ctor_set_uint8(x_19, sizeof(void*)*3 + 1, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*3 + 2, x_18);
x_3 = x_19;
goto _start;
}
else
{
uint8_t x_21; 
x_21 = lean_string_utf8_at_end(x_2, x_7);
if (x_21 == 0)
{
uint32_t x_22; uint8_t x_23; 
x_22 = lean_string_utf8_get_fast(x_2, x_7);
x_23 = l_instDecidableEqChar(x_22, x_9);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_3, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_3, 2);
lean_inc(x_25);
x_26 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_27 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 1);
x_28 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 2);
lean_dec(x_3);
x_29 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_29, 0, x_24);
lean_ctor_set(x_29, 1, x_7);
lean_ctor_set(x_29, 2, x_25);
lean_ctor_set_uint8(x_29, sizeof(void*)*3, x_26);
lean_ctor_set_uint8(x_29, sizeof(void*)*3 + 1, x_27);
lean_ctor_set_uint8(x_29, sizeof(void*)*3 + 2, x_28);
x_3 = x_29;
goto _start;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; lean_object* x_39; 
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_add(x_1, x_31);
lean_dec(x_1);
x_33 = lean_ctor_get(x_3, 0);
lean_inc(x_33);
x_34 = lean_string_utf8_next_fast(x_2, x_7);
lean_dec(x_7);
x_35 = lean_ctor_get(x_3, 2);
lean_inc(x_35);
x_36 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_37 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 1);
x_38 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 2);
lean_dec(x_3);
x_39 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_39, 0, x_33);
lean_ctor_set(x_39, 1, x_34);
lean_ctor_set(x_39, 2, x_35);
lean_ctor_set_uint8(x_39, sizeof(void*)*3, x_36);
lean_ctor_set_uint8(x_39, sizeof(void*)*3 + 1, x_37);
lean_ctor_set_uint8(x_39, sizeof(void*)*3 + 2, x_38);
x_1 = x_32;
x_3 = x_39;
goto _start;
}
}
else
{
lean_object* x_41; 
lean_dec(x_7);
lean_dec(x_1);
x_41 = l_Lean_ParseImports_finishCommentBlock_eoi(x_3);
lean_dec(x_3);
return x_41;
}
}
}
else
{
uint8_t x_42; 
x_42 = lean_string_utf8_at_end(x_2, x_7);
if (x_42 == 0)
{
uint32_t x_43; lean_object* x_44; uint32_t x_45; uint8_t x_46; 
x_43 = lean_string_utf8_get_fast(x_2, x_7);
x_44 = lean_unsigned_to_nat(47u);
x_45 = l_Char_ofNat(x_44);
x_46 = l_instDecidableEqChar(x_43, x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; lean_object* x_53; 
x_47 = lean_ctor_get(x_3, 0);
lean_inc(x_47);
x_48 = lean_string_utf8_next_fast(x_2, x_7);
lean_dec(x_7);
x_49 = lean_ctor_get(x_3, 2);
lean_inc(x_49);
x_50 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_51 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 1);
x_52 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 2);
lean_dec(x_3);
x_53 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_53, 0, x_47);
lean_ctor_set(x_53, 1, x_48);
lean_ctor_set(x_53, 2, x_49);
lean_ctor_set_uint8(x_53, sizeof(void*)*3, x_50);
lean_ctor_set_uint8(x_53, sizeof(void*)*3 + 1, x_51);
lean_ctor_set_uint8(x_53, sizeof(void*)*3 + 2, x_52);
x_3 = x_53;
goto _start;
}
else
{
lean_object* x_55; uint8_t x_56; 
x_55 = lean_unsigned_to_nat(1u);
x_56 = lean_nat_dec_eq(x_1, x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; uint8_t x_62; uint8_t x_63; lean_object* x_64; 
x_57 = lean_nat_sub(x_1, x_55);
lean_dec(x_1);
x_58 = lean_ctor_get(x_3, 0);
lean_inc(x_58);
x_59 = lean_string_utf8_next_fast(x_2, x_7);
lean_dec(x_7);
x_60 = lean_ctor_get(x_3, 2);
lean_inc(x_60);
x_61 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_62 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 1);
x_63 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 2);
lean_dec(x_3);
x_64 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_64, 0, x_58);
lean_ctor_set(x_64, 1, x_59);
lean_ctor_set(x_64, 2, x_60);
lean_ctor_set_uint8(x_64, sizeof(void*)*3, x_61);
lean_ctor_set_uint8(x_64, sizeof(void*)*3 + 1, x_62);
lean_ctor_set_uint8(x_64, sizeof(void*)*3 + 2, x_63);
x_1 = x_57;
x_3 = x_64;
goto _start;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; uint8_t x_70; uint8_t x_71; lean_object* x_72; 
lean_dec(x_1);
x_66 = lean_ctor_get(x_3, 0);
lean_inc(x_66);
x_67 = lean_string_utf8_next(x_2, x_7);
lean_dec(x_7);
x_68 = lean_ctor_get(x_3, 2);
lean_inc(x_68);
x_69 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_70 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 1);
x_71 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 2);
lean_dec(x_3);
x_72 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_72, 0, x_66);
lean_ctor_set(x_72, 1, x_67);
lean_ctor_set(x_72, 2, x_68);
lean_ctor_set_uint8(x_72, sizeof(void*)*3, x_69);
lean_ctor_set_uint8(x_72, sizeof(void*)*3 + 1, x_70);
lean_ctor_set_uint8(x_72, sizeof(void*)*3 + 2, x_71);
return x_72;
}
}
}
else
{
lean_object* x_73; 
lean_dec(x_7);
lean_dec(x_1);
x_73 = l_Lean_ParseImports_finishCommentBlock_eoi(x_3);
lean_dec(x_3);
return x_73;
}
}
}
else
{
lean_object* x_74; 
lean_dec(x_4);
lean_dec(x_1);
x_74 = l_Lean_ParseImports_finishCommentBlock_eoi(x_3);
lean_dec(x_3);
return x_74;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_finishCommentBlock___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_ParseImports_finishCommentBlock(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_5 = lean_string_utf8_at_end(x_2, x_4);
if (x_5 == 0)
{
uint32_t x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_string_utf8_get_fast(x_2, x_4);
x_7 = lean_box_uint32(x_6);
lean_inc(x_1);
x_8 = lean_apply_1(x_1, x_7);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
x_11 = lean_string_utf8_next_fast(x_2, x_4);
lean_dec(x_4);
x_12 = lean_ctor_get(x_3, 2);
lean_inc(x_12);
x_13 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_14 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 1);
x_15 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 2);
lean_dec(x_3);
x_16 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_16, 0, x_10);
lean_ctor_set(x_16, 1, x_11);
lean_ctor_set(x_16, 2, x_12);
lean_ctor_set_uint8(x_16, sizeof(void*)*3, x_13);
lean_ctor_set_uint8(x_16, sizeof(void*)*3 + 1, x_14);
lean_ctor_set_uint8(x_16, sizeof(void*)*3 + 2, x_15);
x_3 = x_16;
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
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_ParseImports_takeUntil(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_ParseImports_takeWhile___lam__0(lean_object* x_1, uint32_t x_2) {
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
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeWhile(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_Lean_ParseImports_takeWhile___lam__0___boxed), 2, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = l_Lean_ParseImports_takeUntil(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeWhile___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_4 = l_Lean_ParseImports_takeWhile___lam__0(x_1, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeWhile___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_ParseImports_takeWhile(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_andthen(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
lean_inc(x_3);
x_5 = lean_apply_2(x_1, x_3, x_4);
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = lean_apply_2(x_2, x_3, x_5);
return x_7;
}
else
{
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_instAndThenParser___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
lean_inc(x_3);
x_5 = lean_apply_2(x_1, x_3, x_4);
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = lean_apply_3(x_2, x_7, x_3, x_5);
return x_8;
}
else
{
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
}
static lean_object* _init_l_Lean_ParseImports_instAndThenParser() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_ParseImports_instAndThenParser___lam__0), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___at___Lean_ParseImports_whitespace_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_4 = lean_string_utf8_at_end(x_1, x_3);
if (x_4 == 0)
{
uint32_t x_5; lean_object* x_6; uint32_t x_7; uint8_t x_8; 
x_5 = lean_string_utf8_get_fast(x_1, x_3);
x_6 = lean_unsigned_to_nat(10u);
x_7 = l_Char_ofNat(x_6);
x_8 = l_instDecidableEqChar(x_5, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
x_10 = lean_string_utf8_next_fast(x_1, x_3);
lean_dec(x_3);
x_11 = lean_ctor_get(x_2, 2);
lean_inc(x_11);
x_12 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_13 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 1);
x_14 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 2);
lean_dec(x_2);
x_15 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_15, 0, x_9);
lean_ctor_set(x_15, 1, x_10);
lean_ctor_set(x_15, 2, x_11);
lean_ctor_set_uint8(x_15, sizeof(void*)*3, x_12);
lean_ctor_set_uint8(x_15, sizeof(void*)*3 + 1, x_13);
lean_ctor_set_uint8(x_15, sizeof(void*)*3 + 2, x_14);
x_2 = x_15;
goto _start;
}
else
{
lean_dec(x_3);
return x_2;
}
}
else
{
lean_dec(x_3);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_whitespace(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_13; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_13 = lean_string_utf8_at_end(x_1, x_3);
if (x_13 == 0)
{
uint32_t x_14; uint8_t x_15; uint8_t x_56; lean_object* x_64; uint32_t x_65; uint8_t x_66; 
x_14 = lean_string_utf8_get_fast(x_1, x_3);
x_64 = lean_unsigned_to_nat(9u);
x_65 = l_Char_ofNat(x_64);
x_66 = l_instDecidableEqChar(x_14, x_65);
if (x_66 == 0)
{
lean_object* x_67; uint32_t x_68; uint8_t x_69; 
x_67 = lean_unsigned_to_nat(32u);
x_68 = l_Char_ofNat(x_67);
x_69 = l_instDecidableEqChar(x_14, x_68);
if (x_69 == 0)
{
x_56 = x_66;
goto block_63;
}
else
{
x_56 = x_69;
goto block_63;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; uint8_t x_74; uint8_t x_75; lean_object* x_76; 
x_70 = lean_mk_string_unchecked("tabs are not allowed; please configure your editor to expand them", 65, 65);
x_71 = lean_ctor_get(x_2, 0);
lean_inc(x_71);
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_70);
x_73 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_74 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 1);
x_75 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 2);
lean_dec(x_2);
x_76 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_76, 0, x_71);
lean_ctor_set(x_76, 1, x_3);
lean_ctor_set(x_76, 2, x_72);
lean_ctor_set_uint8(x_76, sizeof(void*)*3, x_73);
lean_ctor_set_uint8(x_76, sizeof(void*)*3 + 1, x_74);
lean_ctor_set_uint8(x_76, sizeof(void*)*3 + 2, x_75);
return x_76;
}
block_55:
{
if (x_15 == 0)
{
lean_object* x_16; uint32_t x_17; uint8_t x_18; 
x_16 = lean_unsigned_to_nat(45u);
x_17 = l_Char_ofNat(x_16);
x_18 = l_instDecidableEqChar(x_14, x_17);
if (x_18 == 0)
{
lean_object* x_19; uint32_t x_20; uint8_t x_21; 
x_19 = lean_unsigned_to_nat(47u);
x_20 = l_Char_ofNat(x_19);
x_21 = l_instDecidableEqChar(x_14, x_20);
if (x_21 == 0)
{
lean_dec(x_3);
return x_2;
}
else
{
lean_object* x_22; uint32_t x_23; uint8_t x_24; 
x_22 = lean_string_utf8_next_fast(x_1, x_3);
lean_dec(x_3);
x_23 = lean_string_utf8_get(x_1, x_22);
x_24 = l_instDecidableEqChar(x_23, x_17);
if (x_24 == 0)
{
lean_dec(x_22);
return x_2;
}
else
{
lean_object* x_25; uint32_t x_26; uint8_t x_27; 
x_25 = lean_string_utf8_next(x_1, x_22);
lean_dec(x_22);
x_26 = lean_string_utf8_get(x_1, x_25);
x_27 = l_instDecidableEqChar(x_26, x_17);
if (x_27 == 0)
{
lean_object* x_28; uint32_t x_29; uint8_t x_30; 
x_28 = lean_unsigned_to_nat(33u);
x_29 = l_Char_ofNat(x_28);
x_30 = l_instDecidableEqChar(x_26, x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_ctor_get(x_2, 0);
lean_inc(x_32);
x_33 = lean_string_utf8_next(x_1, x_25);
lean_dec(x_25);
x_34 = lean_ctor_get(x_2, 2);
lean_inc(x_34);
x_35 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_36 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 1);
x_37 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 2);
lean_dec(x_2);
x_38 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_38, 0, x_32);
lean_ctor_set(x_38, 1, x_33);
lean_ctor_set(x_38, 2, x_34);
lean_ctor_set_uint8(x_38, sizeof(void*)*3, x_35);
lean_ctor_set_uint8(x_38, sizeof(void*)*3 + 1, x_36);
lean_ctor_set_uint8(x_38, sizeof(void*)*3 + 2, x_37);
x_39 = l_Lean_ParseImports_finishCommentBlock(x_31, x_1, x_38);
x_40 = lean_ctor_get(x_39, 2);
lean_inc(x_40);
if (lean_obj_tag(x_40) == 0)
{
x_2 = x_39;
goto _start;
}
else
{
lean_dec(x_40);
return x_39;
}
}
else
{
lean_dec(x_25);
return x_2;
}
}
else
{
lean_dec(x_25);
return x_2;
}
}
}
}
else
{
lean_object* x_42; uint32_t x_43; uint8_t x_44; 
x_42 = lean_string_utf8_next_fast(x_1, x_3);
lean_dec(x_3);
x_43 = lean_string_utf8_get(x_1, x_42);
x_44 = l_instDecidableEqChar(x_43, x_17);
if (x_44 == 0)
{
lean_dec(x_42);
return x_2;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_45 = lean_ctor_get(x_2, 0);
lean_inc(x_45);
x_46 = lean_string_utf8_next(x_1, x_42);
lean_dec(x_42);
x_47 = lean_ctor_get(x_2, 2);
lean_inc(x_47);
x_48 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_49 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 1);
x_50 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 2);
lean_dec(x_2);
x_51 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_51, 0, x_45);
lean_ctor_set(x_51, 1, x_46);
lean_ctor_set(x_51, 2, x_47);
lean_ctor_set_uint8(x_51, sizeof(void*)*3, x_48);
lean_ctor_set_uint8(x_51, sizeof(void*)*3 + 1, x_49);
lean_ctor_set_uint8(x_51, sizeof(void*)*3 + 2, x_50);
x_52 = l_Lean_ParseImports_takeUntil___at___Lean_ParseImports_whitespace_spec__0(x_1, x_51);
x_53 = lean_ctor_get(x_52, 2);
lean_inc(x_53);
if (lean_obj_tag(x_53) == 0)
{
x_2 = x_52;
goto _start;
}
else
{
lean_dec(x_53);
return x_52;
}
}
}
}
else
{
goto block_12;
}
}
block_63:
{
if (x_56 == 0)
{
lean_object* x_57; uint32_t x_58; uint8_t x_59; 
x_57 = lean_unsigned_to_nat(13u);
x_58 = l_Char_ofNat(x_57);
x_59 = l_instDecidableEqChar(x_14, x_58);
if (x_59 == 0)
{
lean_object* x_60; uint32_t x_61; uint8_t x_62; 
x_60 = lean_unsigned_to_nat(10u);
x_61 = l_Char_ofNat(x_60);
x_62 = l_instDecidableEqChar(x_14, x_61);
x_15 = x_62;
goto block_55;
}
else
{
x_15 = x_59;
goto block_55;
}
}
else
{
goto block_12;
}
}
}
else
{
lean_dec(x_3);
return x_2;
}
block_12:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_string_utf8_next(x_1, x_3);
lean_dec(x_3);
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
x_7 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_8 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 1);
x_9 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 2);
lean_dec(x_2);
x_10 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_5);
lean_ctor_set(x_10, 2, x_6);
lean_ctor_set_uint8(x_10, sizeof(void*)*3, x_7);
lean_ctor_set_uint8(x_10, sizeof(void*)*3 + 1, x_8);
lean_ctor_set_uint8(x_10, sizeof(void*)*3 + 2, x_9);
x_2 = x_10;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___at___Lean_ParseImports_whitespace_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_ParseImports_takeUntil___at___Lean_ParseImports_whitespace_spec__0(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_whitespace___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_ParseImports_whitespace(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_string_utf8_at_end(x_1, x_6);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = lean_string_utf8_at_end(x_4, x_7);
if (x_9 == 0)
{
uint32_t x_10; uint32_t x_11; uint8_t x_12; 
x_10 = lean_string_utf8_get_fast(x_1, x_6);
x_11 = lean_string_utf8_get_fast(x_4, x_7);
x_12 = l_instDecidableEqChar(x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_13 = lean_apply_2(x_2, x_4, x_5);
return x_13;
}
else
{
if (x_9 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_string_utf8_next_fast(x_1, x_6);
lean_dec(x_6);
x_15 = lean_string_utf8_next_fast(x_4, x_7);
lean_dec(x_7);
x_6 = x_14;
x_7 = x_15;
goto _start;
}
else
{
lean_object* x_17; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_17 = lean_apply_2(x_2, x_4, x_5);
return x_17;
}
}
}
else
{
lean_object* x_18; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_18 = lean_apply_2(x_2, x_4, x_5);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_6);
lean_dec(x_2);
x_19 = lean_ctor_get(x_5, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_5, 2);
lean_inc(x_20);
x_21 = lean_ctor_get_uint8(x_5, sizeof(void*)*3);
x_22 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 1);
x_23 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 2);
lean_dec(x_5);
x_24 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_24, 0, x_19);
lean_ctor_set(x_24, 1, x_7);
lean_ctor_set(x_24, 2, x_20);
lean_ctor_set_uint8(x_24, sizeof(void*)*3, x_21);
lean_ctor_set_uint8(x_24, sizeof(void*)*3 + 1, x_22);
lean_ctor_set_uint8(x_24, sizeof(void*)*3 + 2, x_23);
x_25 = l_Lean_ParseImports_whitespace(x_4, x_24);
x_26 = lean_apply_2(x_3, x_4, x_25);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_ParseImports_keywordCore_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
x_8 = l_Lean_ParseImports_keywordCore_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_ParseImports_keywordCore(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_keyword___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_4 = lean_mk_string_unchecked("`", 1, 1);
x_5 = lean_string_append(x_4, x_1);
x_6 = lean_mk_string_unchecked("` expected", 10, 10);
x_7 = lean_string_append(x_5, x_6);
lean_dec(x_6);
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_ctor_get(x_3, 1);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_7);
x_11 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_12 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 1);
x_13 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 2);
lean_inc(x_9);
lean_inc(x_8);
x_14 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_9);
lean_ctor_set(x_14, 2, x_10);
lean_ctor_set_uint8(x_14, sizeof(void*)*3, x_11);
lean_ctor_set_uint8(x_14, sizeof(void*)*3 + 1, x_12);
lean_ctor_set_uint8(x_14, sizeof(void*)*3 + 2, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_keyword(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_inc(x_1);
x_4 = lean_alloc_closure((void*)(l_Lean_ParseImports_keyword___lam__0___boxed), 3, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = lean_alloc_closure((void*)(l_Lean_ParseImports_instInhabitedParser___lam__0___boxed), 2, 0);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
x_8 = l_Lean_ParseImports_keywordCore_go(x_1, x_4, x_5, x_2, x_3, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_keyword___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_ParseImports_keyword___lam__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_ParseImports_isIdCont(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint32_t x_4; lean_object* x_5; uint32_t x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_2, 1);
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
x_10 = lean_string_utf8_get_fast(x_1, x_8);
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
LEAN_EXPORT lean_object* l_Lean_ParseImports_isIdCont___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_ParseImports_isIdCont(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_pushImport(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_array_push(x_3, x_1);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
x_7 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_8 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 1);
x_9 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 2);
lean_dec(x_2);
x_10 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_5);
lean_ctor_set(x_10, 2, x_6);
lean_ctor_set_uint8(x_10, sizeof(void*)*3, x_7);
lean_ctor_set_uint8(x_10, sizeof(void*)*3 + 1, x_8);
lean_ctor_set_uint8(x_10, sizeof(void*)*3 + 2, x_9);
return x_10;
}
}
LEAN_EXPORT uint8_t l_Lean_ParseImports_isIdRestCold(uint32_t x_1) {
_start:
{
uint8_t x_2; lean_object* x_12; uint32_t x_13; uint8_t x_14; 
x_12 = lean_unsigned_to_nat(95u);
x_13 = l_Char_ofNat(x_12);
x_14 = l_instDecidableEqChar(x_1, x_13);
if (x_14 == 0)
{
lean_object* x_15; uint32_t x_16; uint8_t x_17; 
x_15 = lean_unsigned_to_nat(39u);
x_16 = l_Char_ofNat(x_15);
x_17 = l_instDecidableEqChar(x_1, x_16);
x_2 = x_17;
goto block_11;
}
else
{
x_2 = x_14;
goto block_11;
}
block_11:
{
if (x_2 == 0)
{
lean_object* x_3; uint32_t x_4; uint8_t x_5; 
x_3 = lean_unsigned_to_nat(33u);
x_4 = l_Char_ofNat(x_3);
x_5 = l_instDecidableEqChar(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint32_t x_7; uint8_t x_8; 
x_6 = lean_unsigned_to_nat(63u);
x_7 = l_Char_ofNat(x_6);
x_8 = l_instDecidableEqChar(x_1, x_7);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = l_Lean_isLetterLike(x_1);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = l_Lean_isSubScriptAlnum(x_1);
return x_10;
}
else
{
return x_9;
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
LEAN_EXPORT lean_object* l_Lean_ParseImports_isIdRestCold___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Lean_ParseImports_isIdRestCold(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_ParseImports_isIdRestFast(uint32_t x_1) {
_start:
{
uint8_t x_2; uint8_t x_12; uint8_t x_29; uint8_t x_37; lean_object* x_45; uint32_t x_46; uint8_t x_47; 
x_45 = lean_unsigned_to_nat(65u);
x_46 = lean_uint32_of_nat(x_45);
x_47 = lean_uint32_dec_le(x_46, x_1);
if (x_47 == 0)
{
x_37 = x_47;
goto block_44;
}
else
{
lean_object* x_48; uint32_t x_49; uint8_t x_50; 
x_48 = lean_unsigned_to_nat(90u);
x_49 = lean_uint32_of_nat(x_48);
x_50 = lean_uint32_dec_le(x_1, x_49);
x_37 = x_50;
goto block_44;
}
block_11:
{
if (x_2 == 0)
{
lean_object* x_3; uint32_t x_4; uint8_t x_5; 
x_3 = lean_unsigned_to_nat(33u);
x_4 = l_Char_ofNat(x_3);
x_5 = l_instDecidableEqChar(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint32_t x_7; uint8_t x_8; 
x_6 = lean_unsigned_to_nat(63u);
x_7 = l_Char_ofNat(x_6);
x_8 = l_instDecidableEqChar(x_1, x_7);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = l_Lean_isLetterLike(x_1);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = l_Lean_isSubScriptAlnum(x_1);
return x_10;
}
else
{
return x_9;
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
block_28:
{
if (x_12 == 0)
{
lean_object* x_13; uint32_t x_14; uint8_t x_15; 
x_13 = lean_unsigned_to_nat(46u);
x_14 = l_Char_ofNat(x_13);
x_15 = l_instDecidableEqChar(x_1, x_14);
if (x_15 == 0)
{
lean_object* x_16; uint32_t x_17; uint8_t x_18; 
x_16 = lean_unsigned_to_nat(10u);
x_17 = l_Char_ofNat(x_16);
x_18 = l_instDecidableEqChar(x_1, x_17);
if (x_18 == 0)
{
lean_object* x_19; uint32_t x_20; uint8_t x_21; 
x_19 = lean_unsigned_to_nat(32u);
x_20 = l_Char_ofNat(x_19);
x_21 = l_instDecidableEqChar(x_1, x_20);
if (x_21 == 0)
{
lean_object* x_22; uint32_t x_23; uint8_t x_24; 
x_22 = lean_unsigned_to_nat(95u);
x_23 = l_Char_ofNat(x_22);
x_24 = l_instDecidableEqChar(x_1, x_23);
if (x_24 == 0)
{
lean_object* x_25; uint32_t x_26; uint8_t x_27; 
x_25 = lean_unsigned_to_nat(39u);
x_26 = l_Char_ofNat(x_25);
x_27 = l_instDecidableEqChar(x_1, x_26);
x_2 = x_27;
goto block_11;
}
else
{
x_2 = x_24;
goto block_11;
}
}
else
{
return x_12;
}
}
else
{
return x_12;
}
}
else
{
return x_12;
}
}
else
{
return x_12;
}
}
block_36:
{
if (x_29 == 0)
{
lean_object* x_30; uint32_t x_31; uint8_t x_32; 
x_30 = lean_unsigned_to_nat(48u);
x_31 = lean_uint32_of_nat(x_30);
x_32 = lean_uint32_dec_le(x_31, x_1);
if (x_32 == 0)
{
x_12 = x_32;
goto block_28;
}
else
{
lean_object* x_33; uint32_t x_34; uint8_t x_35; 
x_33 = lean_unsigned_to_nat(57u);
x_34 = lean_uint32_of_nat(x_33);
x_35 = lean_uint32_dec_le(x_1, x_34);
x_12 = x_35;
goto block_28;
}
}
else
{
return x_29;
}
}
block_44:
{
if (x_37 == 0)
{
lean_object* x_38; uint32_t x_39; uint8_t x_40; 
x_38 = lean_unsigned_to_nat(97u);
x_39 = lean_uint32_of_nat(x_38);
x_40 = lean_uint32_dec_le(x_39, x_1);
if (x_40 == 0)
{
x_29 = x_40;
goto block_36;
}
else
{
lean_object* x_41; uint32_t x_42; uint8_t x_43; 
x_41 = lean_unsigned_to_nat(122u);
x_42 = lean_uint32_of_nat(x_41);
x_43 = lean_uint32_dec_le(x_1, x_42);
x_29 = x_43;
goto block_36;
}
}
else
{
return x_37;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_isIdRestFast___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Lean_ParseImports_isIdRestFast(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___at___Lean_ParseImports_moduleIdent_parse_spec__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_18; 
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
x_18 = lean_string_utf8_at_end(x_4, x_7);
if (x_18 == 0)
{
uint32_t x_19; uint32_t x_20; uint8_t x_21; uint32_t x_22; uint8_t x_23; uint8_t x_33; uint8_t x_50; uint8_t x_58; lean_object* x_66; uint32_t x_67; uint8_t x_68; 
x_19 = lean_string_utf8_get_fast(x_2, x_6);
x_20 = l_Lean_idBeginEscape;
x_21 = l_instDecidableEqChar(x_19, x_20);
x_22 = lean_string_utf8_get_fast(x_4, x_7);
x_66 = lean_unsigned_to_nat(65u);
x_67 = lean_uint32_of_nat(x_66);
x_68 = lean_uint32_dec_le(x_67, x_22);
if (x_68 == 0)
{
x_58 = x_68;
goto block_65;
}
else
{
lean_object* x_69; uint32_t x_70; uint8_t x_71; 
x_69 = lean_unsigned_to_nat(90u);
x_70 = lean_uint32_of_nat(x_69);
x_71 = lean_uint32_dec_le(x_22, x_70);
x_58 = x_71;
goto block_65;
}
block_32:
{
if (x_23 == 0)
{
lean_object* x_24; uint32_t x_25; uint8_t x_26; 
x_24 = lean_unsigned_to_nat(33u);
x_25 = l_Char_ofNat(x_24);
x_26 = l_instDecidableEqChar(x_22, x_25);
if (x_26 == 0)
{
lean_object* x_27; uint32_t x_28; uint8_t x_29; 
x_27 = lean_unsigned_to_nat(63u);
x_28 = l_Char_ofNat(x_27);
x_29 = l_instDecidableEqChar(x_22, x_28);
if (x_29 == 0)
{
uint8_t x_30; 
x_30 = l_Lean_isLetterLike(x_22);
if (x_30 == 0)
{
uint8_t x_31; 
x_31 = l_Lean_isSubScriptAlnum(x_22);
if (x_31 == 0)
{
x_8 = x_1;
goto block_17;
}
else
{
x_8 = x_21;
goto block_17;
}
}
else
{
if (x_30 == 0)
{
x_8 = x_1;
goto block_17;
}
else
{
x_8 = x_21;
goto block_17;
}
}
}
else
{
if (x_29 == 0)
{
x_8 = x_1;
goto block_17;
}
else
{
x_8 = x_21;
goto block_17;
}
}
}
else
{
if (x_26 == 0)
{
x_8 = x_1;
goto block_17;
}
else
{
x_8 = x_21;
goto block_17;
}
}
}
else
{
x_8 = x_21;
goto block_17;
}
}
block_49:
{
if (x_33 == 0)
{
lean_object* x_34; uint32_t x_35; uint8_t x_36; 
x_34 = lean_unsigned_to_nat(46u);
x_35 = l_Char_ofNat(x_34);
x_36 = l_instDecidableEqChar(x_22, x_35);
if (x_36 == 0)
{
lean_object* x_37; uint32_t x_38; uint8_t x_39; 
x_37 = lean_unsigned_to_nat(10u);
x_38 = l_Char_ofNat(x_37);
x_39 = l_instDecidableEqChar(x_22, x_38);
if (x_39 == 0)
{
lean_object* x_40; uint32_t x_41; uint8_t x_42; 
x_40 = lean_unsigned_to_nat(32u);
x_41 = l_Char_ofNat(x_40);
x_42 = l_instDecidableEqChar(x_22, x_41);
if (x_42 == 0)
{
lean_object* x_43; uint32_t x_44; uint8_t x_45; 
x_43 = lean_unsigned_to_nat(95u);
x_44 = l_Char_ofNat(x_43);
x_45 = l_instDecidableEqChar(x_22, x_44);
if (x_45 == 0)
{
lean_object* x_46; uint32_t x_47; uint8_t x_48; 
x_46 = lean_unsigned_to_nat(39u);
x_47 = l_Char_ofNat(x_46);
x_48 = l_instDecidableEqChar(x_22, x_47);
x_23 = x_48;
goto block_32;
}
else
{
x_23 = x_45;
goto block_32;
}
}
else
{
x_8 = x_42;
goto block_17;
}
}
else
{
x_8 = x_39;
goto block_17;
}
}
else
{
x_8 = x_36;
goto block_17;
}
}
else
{
x_8 = x_21;
goto block_17;
}
}
block_57:
{
if (x_50 == 0)
{
lean_object* x_51; uint32_t x_52; uint8_t x_53; 
x_51 = lean_unsigned_to_nat(48u);
x_52 = lean_uint32_of_nat(x_51);
x_53 = lean_uint32_dec_le(x_52, x_22);
if (x_53 == 0)
{
x_33 = x_53;
goto block_49;
}
else
{
lean_object* x_54; uint32_t x_55; uint8_t x_56; 
x_54 = lean_unsigned_to_nat(57u);
x_55 = lean_uint32_of_nat(x_54);
x_56 = lean_uint32_dec_le(x_22, x_55);
x_33 = x_56;
goto block_49;
}
}
else
{
x_8 = x_21;
goto block_17;
}
}
block_65:
{
if (x_58 == 0)
{
lean_object* x_59; uint32_t x_60; uint8_t x_61; 
x_59 = lean_unsigned_to_nat(97u);
x_60 = lean_uint32_of_nat(x_59);
x_61 = lean_uint32_dec_le(x_60, x_22);
if (x_61 == 0)
{
x_50 = x_61;
goto block_57;
}
else
{
lean_object* x_62; uint32_t x_63; uint8_t x_64; 
x_62 = lean_unsigned_to_nat(122u);
x_63 = lean_uint32_of_nat(x_62);
x_64 = lean_uint32_dec_le(x_22, x_63);
x_50 = x_64;
goto block_57;
}
}
else
{
x_8 = x_21;
goto block_17;
}
}
}
else
{
lean_dec(x_7);
return x_5;
}
block_17:
{
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
x_10 = lean_string_utf8_next_fast(x_4, x_7);
lean_dec(x_7);
x_11 = lean_ctor_get(x_5, 2);
lean_inc(x_11);
x_12 = lean_ctor_get_uint8(x_5, sizeof(void*)*3);
x_13 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 1);
x_14 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 2);
lean_dec(x_5);
x_15 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_15, 0, x_9);
lean_ctor_set(x_15, 1, x_10);
lean_ctor_set(x_15, 2, x_11);
lean_ctor_set_uint8(x_15, sizeof(void*)*3, x_12);
lean_ctor_set_uint8(x_15, sizeof(void*)*3 + 1, x_13);
lean_ctor_set_uint8(x_15, sizeof(void*)*3 + 2, x_14);
x_5 = x_15;
goto _start;
}
else
{
lean_dec(x_7);
return x_5;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___at___Lean_ParseImports_moduleIdent_parse_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_4 = lean_string_utf8_at_end(x_1, x_3);
if (x_4 == 0)
{
uint32_t x_5; uint32_t x_6; uint8_t x_7; 
x_5 = lean_string_utf8_get_fast(x_1, x_3);
x_6 = l_Lean_idEndEscape;
x_7 = l_instDecidableEqChar(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
x_9 = lean_string_utf8_next_fast(x_1, x_3);
lean_dec(x_3);
x_10 = lean_ctor_get(x_2, 2);
lean_inc(x_10);
x_11 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_12 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 1);
x_13 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 2);
lean_dec(x_2);
x_14 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_9);
lean_ctor_set(x_14, 2, x_10);
lean_ctor_set_uint8(x_14, sizeof(void*)*3, x_11);
lean_ctor_set_uint8(x_14, sizeof(void*)*3 + 1, x_12);
lean_ctor_set_uint8(x_14, sizeof(void*)*3 + 2, x_13);
x_2 = x_14;
goto _start;
}
else
{
lean_dec(x_3);
return x_2;
}
}
else
{
lean_dec(x_3);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_moduleIdent_parse(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_4, 1);
lean_inc(x_19);
x_20 = lean_string_utf8_at_end(x_1, x_19);
if (x_20 == 0)
{
uint32_t x_21; uint32_t x_22; lean_object* x_23; lean_object* x_24; uint32_t x_25; lean_object* x_26; uint8_t x_27; uint8_t x_28; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint32_t x_38; lean_object* x_39; uint8_t x_40; uint8_t x_41; uint8_t x_50; uint8_t x_51; uint8_t x_77; uint8_t x_86; uint8_t x_92; 
x_21 = lean_string_utf8_get_fast(x_1, x_19);
x_22 = l_Lean_idBeginEscape;
x_50 = l_instDecidableEqChar(x_21, x_22);
if (x_50 == 0)
{
lean_object* x_100; uint32_t x_101; uint8_t x_102; 
x_100 = lean_unsigned_to_nat(65u);
x_101 = lean_uint32_of_nat(x_100);
x_102 = lean_uint32_dec_le(x_101, x_21);
if (x_102 == 0)
{
x_92 = x_102;
goto block_99;
}
else
{
lean_object* x_103; uint32_t x_104; uint8_t x_105; 
x_103 = lean_unsigned_to_nat(90u);
x_104 = lean_uint32_of_nat(x_103);
x_105 = lean_uint32_dec_le(x_21, x_104);
x_92 = x_105;
goto block_99;
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; uint8_t x_110; uint8_t x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; 
x_106 = lean_string_utf8_next_fast(x_1, x_19);
lean_dec(x_19);
x_107 = lean_ctor_get(x_4, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_4, 2);
lean_inc(x_108);
x_109 = lean_ctor_get_uint8(x_4, sizeof(void*)*3);
x_110 = lean_ctor_get_uint8(x_4, sizeof(void*)*3 + 1);
x_111 = lean_ctor_get_uint8(x_4, sizeof(void*)*3 + 2);
lean_dec(x_4);
lean_inc(x_106);
x_112 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_112, 0, x_107);
lean_ctor_set(x_112, 1, x_106);
lean_ctor_set(x_112, 2, x_108);
lean_ctor_set_uint8(x_112, sizeof(void*)*3, x_109);
lean_ctor_set_uint8(x_112, sizeof(void*)*3 + 1, x_110);
lean_ctor_set_uint8(x_112, sizeof(void*)*3 + 2, x_111);
x_113 = l_Lean_ParseImports_takeUntil___at___Lean_ParseImports_moduleIdent_parse_spec__1(x_1, x_112);
x_114 = lean_ctor_get(x_113, 1);
lean_inc(x_114);
x_115 = lean_string_utf8_at_end(x_1, x_114);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; uint8_t x_120; uint8_t x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; uint32_t x_131; lean_object* x_132; uint32_t x_133; uint8_t x_134; 
x_116 = lean_ctor_get(x_113, 0);
lean_inc(x_116);
x_117 = lean_string_utf8_next_fast(x_1, x_114);
x_118 = lean_ctor_get(x_113, 2);
lean_inc(x_118);
x_119 = lean_ctor_get_uint8(x_113, sizeof(void*)*3);
x_120 = lean_ctor_get_uint8(x_113, sizeof(void*)*3 + 1);
x_121 = lean_ctor_get_uint8(x_113, sizeof(void*)*3 + 2);
lean_dec(x_113);
lean_inc(x_118);
lean_inc(x_117);
lean_inc(x_116);
x_122 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_122, 0, x_116);
lean_ctor_set(x_122, 1, x_117);
lean_ctor_set(x_122, 2, x_118);
lean_ctor_set_uint8(x_122, sizeof(void*)*3, x_119);
lean_ctor_set_uint8(x_122, sizeof(void*)*3 + 1, x_120);
lean_ctor_set_uint8(x_122, sizeof(void*)*3 + 2, x_121);
x_123 = lean_string_utf8_extract(x_1, x_106, x_114);
lean_dec(x_114);
lean_dec(x_106);
x_124 = l_Lean_Name_str___override(x_3, x_123);
x_131 = lean_string_utf8_get(x_1, x_117);
x_132 = lean_unsigned_to_nat(46u);
x_133 = l_Char_ofNat(x_132);
x_134 = l_instDecidableEqChar(x_131, x_133);
if (x_134 == 0)
{
x_125 = x_134;
goto block_130;
}
else
{
lean_object* x_135; uint8_t x_136; 
x_135 = lean_string_utf8_next(x_1, x_117);
x_136 = lean_string_utf8_at_end(x_1, x_135);
if (x_136 == 0)
{
uint32_t x_137; uint8_t x_138; uint8_t x_145; lean_object* x_153; uint32_t x_154; uint8_t x_155; 
x_137 = lean_string_utf8_get_fast(x_1, x_135);
lean_dec(x_135);
x_153 = lean_unsigned_to_nat(65u);
x_154 = lean_uint32_of_nat(x_153);
x_155 = lean_uint32_dec_le(x_154, x_137);
if (x_155 == 0)
{
x_145 = x_155;
goto block_152;
}
else
{
lean_object* x_156; uint32_t x_157; uint8_t x_158; 
x_156 = lean_unsigned_to_nat(90u);
x_157 = lean_uint32_of_nat(x_156);
x_158 = lean_uint32_dec_le(x_137, x_157);
x_145 = x_158;
goto block_152;
}
block_144:
{
if (x_138 == 0)
{
lean_object* x_139; uint32_t x_140; uint8_t x_141; 
x_139 = lean_unsigned_to_nat(95u);
x_140 = l_Char_ofNat(x_139);
x_141 = l_instDecidableEqChar(x_137, x_140);
if (x_141 == 0)
{
uint8_t x_142; 
x_142 = l_Lean_isLetterLike(x_137);
if (x_142 == 0)
{
uint8_t x_143; 
x_143 = l_instDecidableEqChar(x_137, x_22);
x_125 = x_143;
goto block_130;
}
else
{
x_125 = x_134;
goto block_130;
}
}
else
{
x_125 = x_134;
goto block_130;
}
}
else
{
x_125 = x_134;
goto block_130;
}
}
block_152:
{
if (x_145 == 0)
{
lean_object* x_146; uint32_t x_147; uint8_t x_148; 
x_146 = lean_unsigned_to_nat(97u);
x_147 = lean_uint32_of_nat(x_146);
x_148 = lean_uint32_dec_le(x_147, x_137);
if (x_148 == 0)
{
x_138 = x_148;
goto block_144;
}
else
{
lean_object* x_149; uint32_t x_150; uint8_t x_151; 
x_149 = lean_unsigned_to_nat(122u);
x_150 = lean_uint32_of_nat(x_149);
x_151 = lean_uint32_dec_le(x_137, x_150);
x_138 = x_151;
goto block_144;
}
}
else
{
x_125 = x_134;
goto block_130;
}
}
}
else
{
lean_dec(x_135);
x_125 = x_115;
goto block_130;
}
}
block_130:
{
if (x_125 == 0)
{
lean_object* x_126; 
lean_dec(x_118);
lean_dec(x_117);
lean_dec(x_116);
x_126 = lean_apply_3(x_2, x_124, x_1, x_122);
return x_126;
}
else
{
lean_object* x_127; lean_object* x_128; 
lean_dec(x_122);
x_127 = lean_string_utf8_next(x_1, x_117);
lean_dec(x_117);
x_128 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_128, 0, x_116);
lean_ctor_set(x_128, 1, x_127);
lean_ctor_set(x_128, 2, x_118);
lean_ctor_set_uint8(x_128, sizeof(void*)*3, x_119);
lean_ctor_set_uint8(x_128, sizeof(void*)*3 + 1, x_120);
lean_ctor_set_uint8(x_128, sizeof(void*)*3 + 2, x_121);
x_3 = x_124;
x_4 = x_128;
goto _start;
}
}
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; uint8_t x_163; uint8_t x_164; lean_object* x_165; 
lean_dec(x_106);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_159 = lean_mk_string_unchecked("unterminated identifier escape", 30, 30);
x_160 = lean_ctor_get(x_113, 0);
lean_inc(x_160);
x_161 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_161, 0, x_159);
x_162 = lean_ctor_get_uint8(x_113, sizeof(void*)*3);
x_163 = lean_ctor_get_uint8(x_113, sizeof(void*)*3 + 1);
x_164 = lean_ctor_get_uint8(x_113, sizeof(void*)*3 + 2);
lean_dec(x_113);
x_165 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_165, 0, x_160);
lean_ctor_set(x_165, 1, x_114);
lean_ctor_set(x_165, 2, x_161);
lean_ctor_set_uint8(x_165, sizeof(void*)*3, x_162);
lean_ctor_set_uint8(x_165, sizeof(void*)*3 + 1, x_163);
lean_ctor_set_uint8(x_165, sizeof(void*)*3 + 2, x_164);
return x_165;
}
}
block_34:
{
if (x_28 == 0)
{
lean_object* x_29; uint32_t x_30; uint8_t x_31; 
x_29 = lean_unsigned_to_nat(95u);
x_30 = l_Char_ofNat(x_29);
x_31 = l_instDecidableEqChar(x_25, x_30);
if (x_31 == 0)
{
uint8_t x_32; 
x_32 = l_Lean_isLetterLike(x_25);
if (x_32 == 0)
{
uint8_t x_33; 
x_33 = l_instDecidableEqChar(x_25, x_22);
x_5 = x_23;
x_6 = x_24;
x_7 = x_26;
x_8 = x_33;
goto block_18;
}
else
{
x_5 = x_23;
x_6 = x_24;
x_7 = x_26;
x_8 = x_27;
goto block_18;
}
}
else
{
x_5 = x_23;
x_6 = x_24;
x_7 = x_26;
x_8 = x_27;
goto block_18;
}
}
else
{
x_5 = x_23;
x_6 = x_24;
x_7 = x_26;
x_8 = x_27;
goto block_18;
}
}
block_49:
{
if (x_41 == 0)
{
lean_object* x_42; uint32_t x_43; uint32_t x_44; uint8_t x_45; 
x_42 = lean_unsigned_to_nat(97u);
x_43 = lean_uint32_of_nat(x_42);
x_44 = lean_string_utf8_get_fast(x_1, x_35);
lean_dec(x_35);
x_45 = lean_uint32_dec_le(x_43, x_44);
if (x_45 == 0)
{
x_23 = x_36;
x_24 = x_37;
x_25 = x_38;
x_26 = x_39;
x_27 = x_40;
x_28 = x_45;
goto block_34;
}
else
{
lean_object* x_46; uint32_t x_47; uint8_t x_48; 
x_46 = lean_unsigned_to_nat(122u);
x_47 = lean_uint32_of_nat(x_46);
x_48 = lean_uint32_dec_le(x_44, x_47);
x_23 = x_36;
x_24 = x_37;
x_25 = x_38;
x_26 = x_39;
x_27 = x_40;
x_28 = x_48;
goto block_34;
}
}
else
{
lean_dec(x_35);
x_5 = x_36;
x_6 = x_37;
x_7 = x_39;
x_8 = x_40;
goto block_18;
}
}
block_76:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint32_t x_63; lean_object* x_64; uint32_t x_65; uint8_t x_66; 
x_52 = lean_ctor_get(x_4, 0);
lean_inc(x_52);
x_53 = lean_string_utf8_next_fast(x_1, x_19);
x_54 = lean_ctor_get(x_4, 2);
lean_inc(x_54);
x_55 = lean_ctor_get_uint8(x_4, sizeof(void*)*3);
x_56 = lean_ctor_get_uint8(x_4, sizeof(void*)*3 + 1);
x_57 = lean_ctor_get_uint8(x_4, sizeof(void*)*3 + 2);
x_58 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_58, 0, x_52);
lean_ctor_set(x_58, 1, x_53);
lean_ctor_set(x_58, 2, x_54);
lean_ctor_set_uint8(x_58, sizeof(void*)*3, x_55);
lean_ctor_set_uint8(x_58, sizeof(void*)*3 + 1, x_56);
lean_ctor_set_uint8(x_58, sizeof(void*)*3 + 2, x_57);
x_59 = l_Lean_ParseImports_takeUntil___at___Lean_ParseImports_moduleIdent_parse_spec__0(x_51, x_1, x_4, x_1, x_58);
lean_dec(x_4);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
x_61 = lean_string_utf8_extract(x_1, x_19, x_60);
lean_dec(x_19);
x_62 = l_Lean_Name_str___override(x_3, x_61);
x_63 = lean_string_utf8_get(x_1, x_60);
x_64 = lean_unsigned_to_nat(46u);
x_65 = l_Char_ofNat(x_64);
x_66 = l_instDecidableEqChar(x_63, x_65);
if (x_66 == 0)
{
x_5 = x_60;
x_6 = x_59;
x_7 = x_62;
x_8 = x_66;
goto block_18;
}
else
{
lean_object* x_67; uint8_t x_68; 
x_67 = lean_string_utf8_next(x_1, x_60);
x_68 = lean_string_utf8_at_end(x_1, x_67);
if (x_68 == 0)
{
uint32_t x_69; lean_object* x_70; uint32_t x_71; uint8_t x_72; 
x_69 = lean_string_utf8_get_fast(x_1, x_67);
x_70 = lean_unsigned_to_nat(65u);
x_71 = lean_uint32_of_nat(x_70);
x_72 = lean_uint32_dec_le(x_71, x_69);
if (x_72 == 0)
{
x_35 = x_67;
x_36 = x_60;
x_37 = x_59;
x_38 = x_69;
x_39 = x_62;
x_40 = x_66;
x_41 = x_72;
goto block_49;
}
else
{
lean_object* x_73; uint32_t x_74; uint8_t x_75; 
x_73 = lean_unsigned_to_nat(90u);
x_74 = lean_uint32_of_nat(x_73);
x_75 = lean_uint32_dec_le(x_69, x_74);
x_35 = x_67;
x_36 = x_60;
x_37 = x_59;
x_38 = x_69;
x_39 = x_62;
x_40 = x_66;
x_41 = x_75;
goto block_49;
}
}
else
{
lean_dec(x_67);
x_5 = x_60;
x_6 = x_59;
x_7 = x_62;
x_8 = x_50;
goto block_18;
}
}
}
block_85:
{
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; uint8_t x_82; uint8_t x_83; lean_object* x_84; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_78 = lean_mk_string_unchecked("expected identifier", 19, 19);
x_79 = lean_ctor_get(x_4, 0);
lean_inc(x_79);
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_78);
x_81 = lean_ctor_get_uint8(x_4, sizeof(void*)*3);
x_82 = lean_ctor_get_uint8(x_4, sizeof(void*)*3 + 1);
x_83 = lean_ctor_get_uint8(x_4, sizeof(void*)*3 + 2);
lean_dec(x_4);
x_84 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_84, 0, x_79);
lean_ctor_set(x_84, 1, x_19);
lean_ctor_set(x_84, 2, x_80);
lean_ctor_set_uint8(x_84, sizeof(void*)*3, x_81);
lean_ctor_set_uint8(x_84, sizeof(void*)*3 + 1, x_82);
lean_ctor_set_uint8(x_84, sizeof(void*)*3 + 2, x_83);
return x_84;
}
else
{
x_51 = x_77;
goto block_76;
}
}
block_91:
{
if (x_86 == 0)
{
lean_object* x_87; uint32_t x_88; uint8_t x_89; 
x_87 = lean_unsigned_to_nat(95u);
x_88 = l_Char_ofNat(x_87);
x_89 = l_instDecidableEqChar(x_21, x_88);
if (x_89 == 0)
{
uint8_t x_90; 
x_90 = l_Lean_isLetterLike(x_21);
x_77 = x_90;
goto block_85;
}
else
{
x_77 = x_89;
goto block_85;
}
}
else
{
x_51 = x_86;
goto block_76;
}
}
block_99:
{
if (x_92 == 0)
{
lean_object* x_93; uint32_t x_94; uint8_t x_95; 
x_93 = lean_unsigned_to_nat(97u);
x_94 = lean_uint32_of_nat(x_93);
x_95 = lean_uint32_dec_le(x_94, x_21);
if (x_95 == 0)
{
x_86 = x_95;
goto block_91;
}
else
{
lean_object* x_96; uint32_t x_97; uint8_t x_98; 
x_96 = lean_unsigned_to_nat(122u);
x_97 = lean_uint32_of_nat(x_96);
x_98 = lean_uint32_dec_le(x_21, x_97);
x_86 = x_98;
goto block_91;
}
}
else
{
x_51 = x_92;
goto block_76;
}
}
}
else
{
lean_object* x_166; 
lean_dec(x_19);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_166 = l_Lean_ParseImports_State_mkEOIError(x_4);
lean_dec(x_4);
return x_166;
}
block_18:
{
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_5);
x_9 = lean_apply_3(x_2, x_7, x_1, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
x_11 = lean_string_utf8_next(x_1, x_5);
lean_dec(x_5);
x_12 = lean_ctor_get(x_6, 2);
lean_inc(x_12);
x_13 = lean_ctor_get_uint8(x_6, sizeof(void*)*3);
x_14 = lean_ctor_get_uint8(x_6, sizeof(void*)*3 + 1);
x_15 = lean_ctor_get_uint8(x_6, sizeof(void*)*3 + 2);
lean_dec(x_6);
x_16 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_16, 0, x_10);
lean_ctor_set(x_16, 1, x_11);
lean_ctor_set(x_16, 2, x_12);
lean_ctor_set_uint8(x_16, sizeof(void*)*3, x_13);
lean_ctor_set_uint8(x_16, sizeof(void*)*3 + 1, x_14);
lean_ctor_set_uint8(x_16, sizeof(void*)*3 + 2, x_15);
x_3 = x_7;
x_4 = x_16;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___at___Lean_ParseImports_moduleIdent_parse_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l_Lean_ParseImports_takeUntil___at___Lean_ParseImports_moduleIdent_parse_spec__0(x_6, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___at___Lean_ParseImports_moduleIdent_parse_spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_ParseImports_takeUntil___at___Lean_ParseImports_moduleIdent_parse_spec__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_moduleIdent___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 2);
x_5 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 1);
x_6 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set_uint8(x_6, sizeof(void*)*1, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*1 + 1, x_5);
x_7 = l_Lean_ParseImports_State_pushImport(x_6, x_3);
x_8 = l_Lean_ParseImports_whitespace(x_2, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_moduleIdent(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_alloc_closure((void*)(l_Lean_ParseImports_moduleIdent___lam__0___boxed), 3, 0);
x_4 = lean_box(0);
x_5 = l_Lean_ParseImports_moduleIdent_parse(x_1, x_3, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_moduleIdent___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_ParseImports_moduleIdent___lam__0(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_many(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
lean_inc(x_1);
lean_inc(x_3);
lean_inc(x_2);
x_4 = lean_apply_2(x_1, x_2, x_3);
x_5 = lean_ctor_get(x_4, 2);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_dec(x_3);
x_3 = x_4;
goto _start;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; 
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_array_get_size(x_7);
lean_dec(x_7);
x_10 = lean_ctor_get(x_4, 0);
lean_inc(x_10);
lean_dec(x_4);
x_11 = l_Array_shrink___redArg(x_10, x_9);
lean_dec(x_9);
x_12 = lean_box(0);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_8);
lean_ctor_set(x_14, 2, x_12);
x_15 = lean_unbox(x_13);
lean_ctor_set_uint8(x_14, sizeof(void*)*3, x_15);
x_16 = lean_unbox(x_13);
lean_ctor_set_uint8(x_14, sizeof(void*)*3 + 1, x_16);
x_17 = lean_unbox(x_13);
lean_ctor_set_uint8(x_14, sizeof(void*)*3 + 2, x_17);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_setIsExported___redArg(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_7 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 2);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_8 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_4);
lean_ctor_set(x_8, 2, x_5);
lean_ctor_set_uint8(x_8, sizeof(void*)*3, x_6);
lean_ctor_set_uint8(x_8, sizeof(void*)*3 + 1, x_1);
lean_ctor_set_uint8(x_8, sizeof(void*)*3 + 2, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_setIsExported(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_ParseImports_setIsExported___redArg(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_setIsExported___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_ParseImports_setIsExported___redArg(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_setIsExported___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_ParseImports_setIsExported(x_4, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_setImportAll___redArg(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_7 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 1);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_8 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_4);
lean_ctor_set(x_8, 2, x_5);
lean_ctor_set_uint8(x_8, sizeof(void*)*3, x_6);
lean_ctor_set_uint8(x_8, sizeof(void*)*3 + 1, x_7);
lean_ctor_set_uint8(x_8, sizeof(void*)*3 + 2, x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_setImportAll(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_ParseImports_setImportAll___redArg(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_setImportAll___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_ParseImports_setImportAll___redArg(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_setImportAll___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_ParseImports_setImportAll(x_4, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore_go___at___Lean_ParseImports_main_spec__0___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; lean_object* x_9; uint8_t x_10; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_box(1);
x_7 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 1);
x_8 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 2);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_9 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_4);
lean_ctor_set(x_9, 2, x_5);
x_10 = lean_unbox(x_6);
lean_ctor_set_uint8(x_9, sizeof(void*)*3, x_10);
lean_ctor_set_uint8(x_9, sizeof(void*)*3 + 1, x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*3 + 2, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore_go___at___Lean_ParseImports_main_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_string_utf8_at_end(x_1, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = lean_string_utf8_at_end(x_2, x_5);
if (x_7 == 0)
{
uint32_t x_8; uint32_t x_9; uint8_t x_10; 
x_8 = lean_string_utf8_get_fast(x_1, x_4);
x_9 = lean_string_utf8_get_fast(x_2, x_5);
x_10 = l_instDecidableEqChar(x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_4);
x_11 = l_Lean_ParseImports_keywordCore_go___at___Lean_ParseImports_main_spec__0___lam__0(x_2, x_3);
return x_11;
}
else
{
if (x_7 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_string_utf8_next_fast(x_1, x_4);
lean_dec(x_4);
x_13 = lean_string_utf8_next_fast(x_2, x_5);
lean_dec(x_5);
x_4 = x_12;
x_5 = x_13;
goto _start;
}
else
{
lean_object* x_15; 
lean_dec(x_5);
lean_dec(x_4);
x_15 = l_Lean_ParseImports_keywordCore_go___at___Lean_ParseImports_main_spec__0___lam__0(x_2, x_3);
return x_15;
}
}
}
else
{
lean_object* x_16; 
lean_dec(x_5);
lean_dec(x_4);
x_16 = l_Lean_ParseImports_keywordCore_go___at___Lean_ParseImports_main_spec__0___lam__0(x_2, x_3);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_4);
x_17 = lean_ctor_get(x_3, 0);
x_18 = lean_ctor_get(x_3, 2);
x_19 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_20 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 1);
x_21 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 2);
lean_inc(x_18);
lean_inc(x_17);
x_22 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_22, 0, x_17);
lean_ctor_set(x_22, 1, x_5);
lean_ctor_set(x_22, 2, x_18);
lean_ctor_set_uint8(x_22, sizeof(void*)*3, x_19);
lean_ctor_set_uint8(x_22, sizeof(void*)*3 + 1, x_20);
lean_ctor_set_uint8(x_22, sizeof(void*)*3 + 2, x_21);
x_23 = l_Lean_ParseImports_whitespace(x_2, x_22);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore_go___at___Lean_ParseImports_main_spec__1___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_4 = lean_mk_string_unchecked("Init", 4, 4);
x_5 = l_Lean_Name_mkStr1(x_4);
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set_uint8(x_7, sizeof(void*)*1, x_1);
x_8 = lean_unbox(x_6);
lean_ctor_set_uint8(x_7, sizeof(void*)*1 + 1, x_8);
x_9 = l_Lean_ParseImports_State_pushImport(x_7, x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore_go___at___Lean_ParseImports_main_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_string_utf8_at_end(x_1, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = lean_string_utf8_at_end(x_2, x_5);
if (x_7 == 0)
{
uint32_t x_8; uint32_t x_9; uint8_t x_10; 
x_8 = lean_string_utf8_get_fast(x_1, x_4);
x_9 = lean_string_utf8_get_fast(x_2, x_5);
x_10 = l_instDecidableEqChar(x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_4);
x_11 = l_Lean_ParseImports_keywordCore_go___at___Lean_ParseImports_main_spec__1___lam__0(x_6, x_2, x_3);
return x_11;
}
else
{
if (x_7 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_string_utf8_next_fast(x_1, x_4);
lean_dec(x_4);
x_13 = lean_string_utf8_next_fast(x_2, x_5);
lean_dec(x_5);
x_4 = x_12;
x_5 = x_13;
goto _start;
}
else
{
lean_object* x_15; 
lean_dec(x_5);
lean_dec(x_4);
x_15 = l_Lean_ParseImports_keywordCore_go___at___Lean_ParseImports_main_spec__1___lam__0(x_6, x_2, x_3);
return x_15;
}
}
}
else
{
lean_object* x_16; 
lean_dec(x_5);
lean_dec(x_4);
x_16 = l_Lean_ParseImports_keywordCore_go___at___Lean_ParseImports_main_spec__1___lam__0(x_6, x_2, x_3);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_4);
x_17 = lean_ctor_get(x_3, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_3, 2);
lean_inc(x_18);
x_19 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_20 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 1);
x_21 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 2);
lean_dec(x_3);
x_22 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_22, 0, x_17);
lean_ctor_set(x_22, 1, x_5);
lean_ctor_set(x_22, 2, x_18);
lean_ctor_set_uint8(x_22, sizeof(void*)*3, x_19);
lean_ctor_set_uint8(x_22, sizeof(void*)*3 + 1, x_20);
lean_ctor_set_uint8(x_22, sizeof(void*)*3 + 2, x_21);
x_23 = l_Lean_ParseImports_whitespace(x_2, x_22);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore_go___at___Lean_ParseImports_main_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_string_utf8_at_end(x_1, x_4);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_box(1);
x_8 = lean_string_utf8_at_end(x_2, x_5);
if (x_8 == 0)
{
uint32_t x_9; uint32_t x_10; uint8_t x_11; 
x_9 = lean_string_utf8_get_fast(x_1, x_4);
x_10 = lean_string_utf8_get_fast(x_2, x_5);
x_11 = l_instDecidableEqChar(x_9, x_10);
if (x_11 == 0)
{
uint8_t x_12; lean_object* x_13; 
lean_dec(x_5);
lean_dec(x_4);
x_12 = lean_unbox(x_7);
x_13 = l_Lean_ParseImports_setIsExported___redArg(x_12, x_3);
return x_13;
}
else
{
if (x_8 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_string_utf8_next_fast(x_1, x_4);
lean_dec(x_4);
x_15 = lean_string_utf8_next_fast(x_2, x_5);
lean_dec(x_5);
x_4 = x_14;
x_5 = x_15;
goto _start;
}
else
{
uint8_t x_17; lean_object* x_18; 
lean_dec(x_5);
lean_dec(x_4);
x_17 = lean_unbox(x_7);
x_18 = l_Lean_ParseImports_setIsExported___redArg(x_17, x_3);
return x_18;
}
}
}
else
{
uint8_t x_19; lean_object* x_20; 
lean_dec(x_5);
lean_dec(x_4);
x_19 = lean_unbox(x_7);
x_20 = l_Lean_ParseImports_setIsExported___redArg(x_19, x_3);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; 
lean_dec(x_4);
x_21 = lean_box(0);
x_22 = lean_ctor_get(x_3, 0);
x_23 = lean_ctor_get(x_3, 2);
x_24 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_25 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 1);
x_26 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 2);
lean_inc(x_23);
lean_inc(x_22);
x_27 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_27, 0, x_22);
lean_ctor_set(x_27, 1, x_5);
lean_ctor_set(x_27, 2, x_23);
lean_ctor_set_uint8(x_27, sizeof(void*)*3, x_24);
lean_ctor_set_uint8(x_27, sizeof(void*)*3 + 1, x_25);
lean_ctor_set_uint8(x_27, sizeof(void*)*3 + 2, x_26);
x_28 = l_Lean_ParseImports_whitespace(x_2, x_27);
x_29 = lean_unbox(x_21);
x_30 = l_Lean_ParseImports_setIsExported___redArg(x_29, x_28);
lean_dec(x_28);
return x_30;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore_go___at___Lean_ParseImports_main_spec__3___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_3 = lean_mk_string_unchecked("`import` expected", 17, 17);
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_3);
x_7 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_8 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 1);
x_9 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 2);
lean_inc(x_5);
lean_inc(x_4);
x_10 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_5);
lean_ctor_set(x_10, 2, x_6);
lean_ctor_set_uint8(x_10, sizeof(void*)*3, x_7);
lean_ctor_set_uint8(x_10, sizeof(void*)*3 + 1, x_8);
lean_ctor_set_uint8(x_10, sizeof(void*)*3 + 2, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore_go___at___Lean_ParseImports_main_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_string_utf8_at_end(x_1, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = lean_string_utf8_at_end(x_2, x_5);
if (x_7 == 0)
{
uint32_t x_8; uint32_t x_9; uint8_t x_10; 
x_8 = lean_string_utf8_get_fast(x_1, x_4);
x_9 = lean_string_utf8_get_fast(x_2, x_5);
x_10 = l_instDecidableEqChar(x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_4);
x_11 = l_Lean_ParseImports_keywordCore_go___at___Lean_ParseImports_main_spec__3___lam__0(x_2, x_3);
return x_11;
}
else
{
if (x_7 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_string_utf8_next_fast(x_1, x_4);
lean_dec(x_4);
x_13 = lean_string_utf8_next_fast(x_2, x_5);
lean_dec(x_5);
x_4 = x_12;
x_5 = x_13;
goto _start;
}
else
{
lean_object* x_15; 
lean_dec(x_5);
lean_dec(x_4);
x_15 = l_Lean_ParseImports_keywordCore_go___at___Lean_ParseImports_main_spec__3___lam__0(x_2, x_3);
return x_15;
}
}
}
else
{
lean_object* x_16; 
lean_dec(x_5);
lean_dec(x_4);
x_16 = l_Lean_ParseImports_keywordCore_go___at___Lean_ParseImports_main_spec__3___lam__0(x_2, x_3);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_4);
x_17 = lean_ctor_get(x_3, 0);
x_18 = lean_ctor_get(x_3, 2);
x_19 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_20 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 1);
x_21 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 2);
lean_inc(x_18);
lean_inc(x_17);
x_22 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_22, 0, x_17);
lean_ctor_set(x_22, 1, x_5);
lean_ctor_set(x_22, 2, x_18);
lean_ctor_set_uint8(x_22, sizeof(void*)*3, x_19);
lean_ctor_set_uint8(x_22, sizeof(void*)*3 + 1, x_20);
lean_ctor_set_uint8(x_22, sizeof(void*)*3 + 2, x_21);
x_23 = l_Lean_ParseImports_whitespace(x_2, x_22);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore_go___at___Lean_ParseImports_main_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_string_utf8_at_end(x_1, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = lean_string_utf8_at_end(x_2, x_5);
if (x_7 == 0)
{
uint32_t x_8; uint32_t x_9; uint8_t x_10; 
x_8 = lean_string_utf8_get_fast(x_1, x_4);
x_9 = lean_string_utf8_get_fast(x_2, x_5);
x_10 = l_instDecidableEqChar(x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_4);
x_11 = l_Lean_ParseImports_setImportAll___redArg(x_6, x_3);
return x_11;
}
else
{
if (x_7 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_string_utf8_next_fast(x_1, x_4);
lean_dec(x_4);
x_13 = lean_string_utf8_next_fast(x_2, x_5);
lean_dec(x_5);
x_4 = x_12;
x_5 = x_13;
goto _start;
}
else
{
lean_object* x_15; 
lean_dec(x_5);
lean_dec(x_4);
x_15 = l_Lean_ParseImports_setImportAll___redArg(x_6, x_3);
return x_15;
}
}
}
else
{
lean_object* x_16; 
lean_dec(x_5);
lean_dec(x_4);
x_16 = l_Lean_ParseImports_setImportAll___redArg(x_6, x_3);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_4);
x_17 = lean_ctor_get(x_3, 0);
x_18 = lean_ctor_get(x_3, 2);
x_19 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_20 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 1);
x_21 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 2);
lean_inc(x_18);
lean_inc(x_17);
x_22 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_22, 0, x_17);
lean_ctor_set(x_22, 1, x_5);
lean_ctor_set(x_22, 2, x_18);
lean_ctor_set_uint8(x_22, sizeof(void*)*3, x_19);
lean_ctor_set_uint8(x_22, sizeof(void*)*3 + 1, x_20);
lean_ctor_set_uint8(x_22, sizeof(void*)*3 + 2, x_21);
x_23 = l_Lean_ParseImports_whitespace(x_2, x_22);
x_24 = l_Lean_ParseImports_setImportAll___redArg(x_6, x_23);
lean_dec(x_23);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_many___at___Lean_ParseImports_many___at___Lean_ParseImports_main_spec__5_spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_3 = lean_mk_string_unchecked("private", 7, 7);
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_ctor_get(x_2, 1);
lean_inc(x_20);
x_21 = l_Lean_ParseImports_keywordCore_go___at___Lean_ParseImports_main_spec__2(x_3, x_1, x_2, x_19, x_20);
lean_dec(x_3);
x_22 = lean_ctor_get(x_21, 2);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_mk_string_unchecked("import", 6, 6);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
x_25 = l_Lean_ParseImports_keywordCore_go___at___Lean_ParseImports_main_spec__3(x_23, x_1, x_21, x_19, x_24);
lean_dec(x_21);
lean_dec(x_23);
x_26 = lean_ctor_get(x_25, 2);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_mk_string_unchecked("all", 3, 3);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
x_29 = l_Lean_ParseImports_keywordCore_go___at___Lean_ParseImports_main_spec__4(x_27, x_1, x_25, x_19, x_28);
lean_dec(x_25);
lean_dec(x_27);
x_30 = lean_ctor_get(x_29, 2);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; 
lean_inc(x_1);
x_31 = l_Lean_ParseImports_moduleIdent(x_1, x_29);
x_5 = x_31;
goto block_18;
}
else
{
lean_dec(x_30);
x_5 = x_29;
goto block_18;
}
}
else
{
lean_dec(x_26);
x_5 = x_25;
goto block_18;
}
}
else
{
lean_dec(x_22);
x_5 = x_21;
goto block_18;
}
block_18:
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_dec(x_4);
lean_dec(x_2);
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; 
lean_dec(x_6);
lean_dec(x_1);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_array_get_size(x_4);
lean_dec(x_4);
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
lean_dec(x_5);
x_11 = l_Array_shrink___redArg(x_10, x_9);
lean_dec(x_9);
x_12 = lean_box(0);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_8);
lean_ctor_set(x_14, 2, x_12);
x_15 = lean_unbox(x_13);
lean_ctor_set_uint8(x_14, sizeof(void*)*3, x_15);
x_16 = lean_unbox(x_13);
lean_ctor_set_uint8(x_14, sizeof(void*)*3 + 1, x_16);
x_17 = lean_unbox(x_13);
lean_ctor_set_uint8(x_14, sizeof(void*)*3 + 2, x_17);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_many___at___Lean_ParseImports_main_spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_3 = lean_mk_string_unchecked("private", 7, 7);
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_ctor_get(x_2, 1);
lean_inc(x_20);
x_21 = l_Lean_ParseImports_keywordCore_go___at___Lean_ParseImports_main_spec__2(x_3, x_1, x_2, x_19, x_20);
lean_dec(x_3);
x_22 = lean_ctor_get(x_21, 2);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_mk_string_unchecked("import", 6, 6);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
x_25 = l_Lean_ParseImports_keywordCore_go___at___Lean_ParseImports_main_spec__3(x_23, x_1, x_21, x_19, x_24);
lean_dec(x_21);
lean_dec(x_23);
x_26 = lean_ctor_get(x_25, 2);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_mk_string_unchecked("all", 3, 3);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
x_29 = l_Lean_ParseImports_keywordCore_go___at___Lean_ParseImports_main_spec__4(x_27, x_1, x_25, x_19, x_28);
lean_dec(x_25);
lean_dec(x_27);
x_30 = lean_ctor_get(x_29, 2);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; 
lean_inc(x_1);
x_31 = l_Lean_ParseImports_moduleIdent(x_1, x_29);
x_5 = x_31;
goto block_18;
}
else
{
lean_dec(x_30);
x_5 = x_29;
goto block_18;
}
}
else
{
lean_dec(x_26);
x_5 = x_25;
goto block_18;
}
}
else
{
lean_dec(x_22);
x_5 = x_21;
goto block_18;
}
block_18:
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_2);
x_7 = l_Lean_ParseImports_many___at___Lean_ParseImports_many___at___Lean_ParseImports_main_spec__5_spec__5(x_1, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; 
lean_dec(x_6);
lean_dec(x_1);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_array_get_size(x_4);
lean_dec(x_4);
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
lean_dec(x_5);
x_11 = l_Array_shrink___redArg(x_10, x_9);
lean_dec(x_9);
x_12 = lean_box(0);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_8);
lean_ctor_set(x_14, 2, x_12);
x_15 = lean_unbox(x_13);
lean_ctor_set_uint8(x_14, sizeof(void*)*3, x_15);
x_16 = lean_unbox(x_13);
lean_ctor_set_uint8(x_14, sizeof(void*)*3 + 1, x_16);
x_17 = lean_unbox(x_13);
lean_ctor_set_uint8(x_14, sizeof(void*)*3 + 2, x_17);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_mk_string_unchecked("module", 6, 6);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = l_Lean_ParseImports_keywordCore_go___at___Lean_ParseImports_main_spec__0(x_3, x_1, x_2, x_4, x_5);
lean_dec(x_2);
lean_dec(x_3);
x_7 = lean_ctor_get(x_6, 2);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_mk_string_unchecked("prelude", 7, 7);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
x_10 = l_Lean_ParseImports_keywordCore_go___at___Lean_ParseImports_main_spec__1(x_8, x_1, x_6, x_4, x_9);
lean_dec(x_8);
x_11 = lean_ctor_get(x_10, 2);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = l_Lean_ParseImports_many___at___Lean_ParseImports_main_spec__5(x_1, x_10);
return x_12;
}
else
{
lean_dec(x_11);
lean_dec(x_1);
return x_10;
}
}
else
{
lean_dec(x_7);
lean_dec(x_1);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore_go___at___Lean_ParseImports_main_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_ParseImports_keywordCore_go___at___Lean_ParseImports_main_spec__0___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore_go___at___Lean_ParseImports_main_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_ParseImports_keywordCore_go___at___Lean_ParseImports_main_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore_go___at___Lean_ParseImports_main_spec__1___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_ParseImports_keywordCore_go___at___Lean_ParseImports_main_spec__1___lam__0(x_4, x_2, x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore_go___at___Lean_ParseImports_main_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_ParseImports_keywordCore_go___at___Lean_ParseImports_main_spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore_go___at___Lean_ParseImports_main_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_ParseImports_keywordCore_go___at___Lean_ParseImports_main_spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore_go___at___Lean_ParseImports_main_spec__3___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_ParseImports_keywordCore_go___at___Lean_ParseImports_main_spec__3___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore_go___at___Lean_ParseImports_main_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_ParseImports_keywordCore_go___at___Lean_ParseImports_main_spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore_go___at___Lean_ParseImports_main_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_ParseImports_keywordCore_go___at___Lean_ParseImports_main_spec__4(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonImport___lam__0____x40_Lean_Elab_ParseImportsFast___hyg_1380_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonImport____x40_Lean_Elab_ParseImportsFast___hyg_1380_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonImport___lam__0____x40_Lean_Elab_ParseImportsFast___hyg_1380____boxed), 1, 0);
x_3 = lean_mk_string_unchecked("module", 6, 6);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_box(1);
x_6 = lean_unbox(x_5);
x_7 = l_Lean_Name_toString(x_4, x_6, x_2);
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_mk_string_unchecked("importAll", 9, 9);
x_13 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_14 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_14, 0, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_10);
x_17 = lean_mk_string_unchecked("isExported", 10, 10);
x_18 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 1);
lean_dec(x_1);
x_19 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_19, 0, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_10);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_16);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_11);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_unsigned_to_nat(0u);
x_27 = lean_mk_empty_array_with_capacity(x_26);
x_28 = l_List_flatMapTR_go___at_____private_Lean_Server_Rpc_Basic_0__Lean_Lsp_toJsonRpcRef____x40_Lean_Server_Rpc_Basic___hyg_173__spec__0(x_25, x_27);
x_29 = l_Lean_Json_mkObj(x_28);
return x_29;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonImport___lam__0____x40_Lean_Elab_ParseImportsFast___hyg_1380____boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonImport___lam__0____x40_Lean_Elab_ParseImportsFast___hyg_1380_(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instToJsonImport__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonImport____x40_Lean_Elab_ParseImportsFast___hyg_1380_), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_ParseImportsFast_0__Lean_toJsonParseImportsResult____x40_Lean_Elab_ParseImportsFast___hyg_1467__spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_8 = l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonImport____x40_Lean_Elab_ParseImportsFast___hyg_1380_(x_5);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonParseImportsResult____x40_Lean_Elab_ParseImportsFast___hyg_1467_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; size_t x_4; lean_object* x_5; size_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_2 = lean_mk_string_unchecked("imports", 7, 7);
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_array_size(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_usize_of_nat(x_5);
x_7 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_ParseImportsFast_0__Lean_toJsonParseImportsResult____x40_Lean_Elab_ParseImportsFast___hyg_1467__spec__0(x_4, x_6, x_3);
x_8 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_mk_string_unchecked("isModule", 8, 8);
x_13 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_14 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_14, 0, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_10);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_11);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_mk_empty_array_with_capacity(x_5);
x_21 = l_List_flatMapTR_go___at_____private_Lean_Server_Rpc_Basic_0__Lean_Lsp_toJsonRpcRef____x40_Lean_Server_Rpc_Basic___hyg_173__spec__0(x_19, x_20);
x_22 = l_Lean_Json_mkObj(x_21);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_ParseImportsFast_0__Lean_toJsonParseImportsResult____x40_Lean_Elab_ParseImportsFast___hyg_1467__spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_ParseImportsFast_0__Lean_toJsonParseImportsResult____x40_Lean_Elab_ParseImportsFast___hyg_1467__spec__0(x_4, x_5, x_3);
return x_6;
}
}
static lean_object* _init_l_Lean_instToJsonParseImportsResult() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonParseImportsResult____x40_Lean_Elab_ParseImportsFast___hyg_1467_), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_parseImports_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_mk_empty_array_with_capacity(x_4);
x_6 = lean_box(0);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_4);
lean_ctor_set(x_8, 2, x_6);
x_9 = lean_unbox(x_7);
lean_ctor_set_uint8(x_8, sizeof(void*)*3, x_9);
x_10 = lean_unbox(x_7);
lean_ctor_set_uint8(x_8, sizeof(void*)*3 + 1, x_10);
x_11 = lean_unbox(x_7);
lean_ctor_set_uint8(x_8, sizeof(void*)*3 + 2, x_11);
x_12 = l_Lean_ParseImports_whitespace(x_1, x_8);
x_13 = l_Lean_ParseImports_main(x_1, x_12);
x_14 = lean_ctor_get(x_13, 2);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_2);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
x_16 = lean_ctor_get_uint8(x_13, sizeof(void*)*3);
lean_dec(x_13);
x_17 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set_uint8(x_17, sizeof(void*)*1, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_3);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_13);
x_19 = !lean_is_exclusive(x_14);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_14, 0);
x_21 = lean_mk_string_unchecked(": ", 2, 2);
x_22 = lean_string_append(x_2, x_21);
lean_dec(x_21);
x_23 = lean_string_append(x_22, x_20);
lean_dec(x_20);
lean_ctor_set_tag(x_14, 18);
lean_ctor_set(x_14, 0, x_23);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_14);
lean_ctor_set(x_24, 1, x_3);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_14, 0);
lean_inc(x_25);
lean_dec(x_14);
x_26 = lean_mk_string_unchecked(": ", 2, 2);
x_27 = lean_string_append(x_2, x_26);
lean_dec(x_26);
x_28 = lean_string_append(x_27, x_25);
lean_dec(x_25);
x_29 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_3);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at_____private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1625__spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonParseImportsResult____x40_Lean_Elab_ParseImportsFast___hyg_1467_(x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1625__spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_5);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1625_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; size_t x_7; lean_object* x_8; size_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("result", 6, 6);
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = l_Lean_Json_opt___at_____private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1625__spec__0(x_2, x_3);
x_5 = lean_mk_string_unchecked("errors", 6, 6);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_array_size(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_usize_of_nat(x_8);
x_10 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1625__spec__1(x_7, x_9, x_6);
x_11 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_4);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_mk_empty_array_with_capacity(x_8);
x_19 = l_List_flatMapTR_go___at_____private_Lean_Server_Rpc_Basic_0__Lean_Lsp_toJsonRpcRef____x40_Lean_Server_Rpc_Basic___hyg_173__spec__0(x_17, x_18);
x_20 = l_Lean_Json_mkObj(x_19);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1625__spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1625__spec__1(x_4, x_5, x_3);
return x_6;
}
}
static lean_object* _init_l_Lean_instToJsonPrintImportResult() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1625_), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportsResult____x40_Lean_Elab_ParseImportsFast___hyg_1680__spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_8 = l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1625_(x_5);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportsResult____x40_Lean_Elab_ParseImportsFast___hyg_1680_(lean_object* x_1) {
_start:
{
lean_object* x_2; size_t x_3; lean_object* x_4; size_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_2 = lean_mk_string_unchecked("imports", 7, 7);
x_3 = lean_array_size(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_usize_of_nat(x_4);
x_6 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportsResult____x40_Lean_Elab_ParseImportsFast___hyg_1680__spec__0(x_3, x_5, x_1);
x_7 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_mk_empty_array_with_capacity(x_4);
x_14 = l_List_flatMapTR_go___at_____private_Lean_Server_Rpc_Basic_0__Lean_Lsp_toJsonRpcRef____x40_Lean_Server_Rpc_Basic___hyg_173__spec__0(x_12, x_13);
x_15 = l_Lean_Json_mkObj(x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportsResult____x40_Lean_Elab_ParseImportsFast___hyg_1680__spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportsResult____x40_Lean_Elab_ParseImportsFast___hyg_1680__spec__0(x_4, x_5, x_3);
return x_6;
}
}
static lean_object* _init_l_Lean_instToJsonPrintImportsResult() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportsResult____x40_Lean_Elab_ParseImportsFast___hyg_1680_), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_printImportsJson_spec__0(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_2, x_1);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_17; lean_object* x_18; lean_object* x_26; lean_object* x_27; 
x_7 = lean_box(0);
lean_inc(x_3);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_26 = lean_array_uget(x_3, x_2);
lean_dec(x_3);
x_27 = l_IO_FS_readFile(x_26, x_4);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_parseImports_x27(x_28, x_26, x_29);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = lean_ctor_get(x_30, 1);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_32);
x_35 = lean_unsigned_to_nat(0u);
x_36 = lean_mk_empty_array_with_capacity(x_35);
lean_ctor_set(x_30, 1, x_36);
lean_ctor_set(x_30, 0, x_34);
x_9 = x_30;
x_10 = x_33;
goto block_16;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_37 = lean_ctor_get(x_30, 0);
x_38 = lean_ctor_get(x_30, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_30);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_37);
x_40 = lean_unsigned_to_nat(0u);
x_41 = lean_mk_empty_array_with_capacity(x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_41);
x_9 = x_42;
x_10 = x_38;
goto block_16;
}
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_30, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_30, 1);
lean_inc(x_44);
lean_dec(x_30);
x_17 = x_43;
x_18 = x_44;
goto block_25;
}
}
else
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_26);
x_45 = lean_ctor_get(x_27, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_27, 1);
lean_inc(x_46);
lean_dec(x_27);
x_17 = x_45;
x_18 = x_46;
goto block_25;
}
block_16:
{
lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_usize_of_nat(x_11);
x_13 = lean_usize_add(x_2, x_12);
x_14 = lean_array_uset(x_8, x_2, x_9);
x_2 = x_13;
x_3 = x_14;
x_4 = x_10;
goto _start;
}
block_25:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_box(0);
x_20 = lean_io_error_to_string(x_17);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_mk_empty_array_with_capacity(x_21);
x_23 = lean_array_push(x_22, x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_19);
lean_ctor_set(x_24, 1, x_23);
x_9 = x_24;
x_10 = x_18;
goto block_16;
}
}
}
}
LEAN_EXPORT lean_object* lean_print_imports_json(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; lean_object* x_4; size_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_3 = lean_array_size(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_usize_of_nat(x_4);
x_6 = l_Array_mapMUnsafe_map___at___Lean_printImportsJson_spec__0(x_3, x_5, x_1, x_2);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportsResult____x40_Lean_Elab_ParseImportsFast___hyg_1680_(x_7);
x_10 = l_Lean_Json_compress(x_9);
x_11 = l_IO_println___at___Lean_Environment_displayStats_spec__2(x_10, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_printImportsJson_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = l_Array_mapMUnsafe_map___at___Lean_printImportsJson_spec__0(x_5, x_6, x_3, x_4);
return x_7;
}
}
lean_object* initialize_Lean_Parser_Module(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_ParseImportsFast(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Parser_Module(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_ParseImports_instInhabitedState = _init_l_Lean_ParseImports_instInhabitedState();
lean_mark_persistent(l_Lean_ParseImports_instInhabitedState);
l_Lean_ParseImports_instInhabitedParser = _init_l_Lean_ParseImports_instInhabitedParser();
lean_mark_persistent(l_Lean_ParseImports_instInhabitedParser);
l_Lean_ParseImports_instAndThenParser = _init_l_Lean_ParseImports_instAndThenParser();
lean_mark_persistent(l_Lean_ParseImports_instAndThenParser);
l_Lean_instToJsonImport__1 = _init_l_Lean_instToJsonImport__1();
lean_mark_persistent(l_Lean_instToJsonImport__1);
l_Lean_instToJsonParseImportsResult = _init_l_Lean_instToJsonParseImportsResult();
lean_mark_persistent(l_Lean_instToJsonParseImportsResult);
l_Lean_instToJsonPrintImportResult = _init_l_Lean_instToJsonPrintImportResult();
lean_mark_persistent(l_Lean_instToJsonPrintImportResult);
l_Lean_instToJsonPrintImportsResult = _init_l_Lean_instToJsonPrintImportsResult();
lean_mark_persistent(l_Lean_instToJsonPrintImportsResult);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
