// Lean compiler output
// Module: Lean.Server.Completion.ImportCompletion
// Imports: Lean.Data.NameTrie Lean.Util.Paths Lean.Util.LakePath Lean.Server.Completion.CompletionItemData Lean.Parser.Module
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
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ImportCompletion_collectAvailableImports(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_forEachModuleInDir___at___ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__0_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_determineLakePath(lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Array_anyMUnsafe_any___at___ImportCompletion_isImportCmdCompletionRequest_spec__2_spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l___private_Lean_Server_Completion_CompletionItemData_0__Lean_Lsp_toJsonCompletionItemData____x40_Lean_Server_Completion_CompletionItemData___hyg_82_(lean_object*);
lean_object* l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___ImportCompletion_isImportCmdCompletionRequest_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_forEachModuleInDir___at___ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_forEachModuleInDir___at___ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ImportCompletion_isImportCmdCompletionRequest___boxed(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_ImportCompletion_addCompletionItemData(lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_System_FilePath_extension(lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___ImportCompletion_computePartialImportCompletions_spec__4(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
lean_object* l_Array_qsort_sort___at___Lean_mkTagDeclarationExtension_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ImportCompletion_computeCompletions___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___ImportCompletion_addCompletionItemData_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_withExtension(lean_object*, lean_object*);
lean_object* l_IO_FS_DirEntry_path(lean_object*);
LEAN_EXPORT lean_object* l_ImportCompletion_AvailableImports_toImportTrie(lean_object*);
lean_object* l_panic___at___Lean_Parser_ParserState_mkUnexpectedTokenErrors_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_ImportCompletion_collectAvailableImportsFromSrcSearchPath(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___ImportCompletion_computePartialImportCompletions_spec__5___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_NameTrie_matchingToArray(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___ImportCompletion_computePartialImportCompletions_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___ImportCompletion_find_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_process_child_wait(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___ImportCompletion_isImportCmdCompletionRequest_spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___at___ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___ImportCompletion_computePartialImportCompletions_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___ImportCompletion_computePartialImportCompletions_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FileMap_lspPosToUtf8Pos(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_foldlMUnsafe_fold___at___ImportCompletion_computePartialImportCompletions_spec__5___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___ImportCompletion_find_spec__2___lam__0___boxed(lean_object*);
lean_object* l_System_FilePath_isDir(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___ImportCompletion_isImportNameCompletionRequest_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t lean_uint32_of_nat(lean_object*);
LEAN_EXPORT uint8_t l_ImportCompletion_isImportNameCompletionRequest(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2_spec__2___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_ImportCompletion_isImportCompletionRequest(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___ImportCompletion_find_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___at___ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_forEachModuleInDir___at___ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_replacePrefix(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___ImportCompletion_computePartialImportCompletions_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_getSrcSearchPath(lean_object*);
LEAN_EXPORT lean_object* l_ImportCompletion_isImportCompletionRequest___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_process_spawn(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isMissing(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___ImportCompletion_AvailableImports_toImportTrie_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT uint8_t l_Array_mapMUnsafe_map___at___ImportCompletion_find_spec__2___lam__0(lean_object*);
LEAN_EXPORT uint8_t l_ImportCompletion_isImportCmdCompletionRequest(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Array_anyMUnsafe_any___at___ImportCompletion_isImportCmdCompletionRequest_spec__0_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Array_anyMUnsafe_any___at___ImportCompletion_isImportNameCompletionRequest_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___ImportCompletion_isImportCmdCompletionRequest_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_forEachModuleInDir___at___ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_NameTrie_empty(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___ImportCompletion_computePartialImportCompletions_spec__5(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Substring_nextn(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_____private_Lean_Data_Lsp_LanguageFeatures_0__Lean_Lsp_beqCompletionItem____x40_Lean_Data_Lsp_LanguageFeatures___hyg_2497__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ImportCompletion_computePartialImportCompletions(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___ImportCompletion_AvailableImports_toImportTrie_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonOpenNamespace____x40_Lean_Data_Lsp_Internal___hyg_2624__spec__0(size_t, size_t, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ImportCompletion_computeCompletions(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ImportCompletion_computePartialImportCompletions___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2_spec__2___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___ImportCompletion_isImportNameCompletionRequest_spec__0(lean_object*, lean_object*, size_t, size_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___ImportCompletion_find_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_ImportCompletion_isImportNameCompletionRequest___boxed(lean_object*, lean_object*);
lean_object* l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ImportCompletion_AvailableImports_toImportTrie___boxed(lean_object*);
lean_object* lean_io_read_dir(lean_object*, lean_object*);
lean_object* l_Lean_NameTrie_insert(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Array_anyMUnsafe_any___at___ImportCompletion_isImportNameCompletionRequest_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t);
uint8_t l_Substring_beq(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___ImportCompletion_isImportCmdCompletionRequest_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Array_anyMUnsafe_any___at___ImportCompletion_isImportCmdCompletionRequest_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_ImportCompletion_collectAvailableImportsFromLake(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_NameTrie_toArray___redArg(lean_object*);
lean_object* l_IO_FS_Handle_readToEnd(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___ImportCompletion_find_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ImportCompletion_find___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Char_utf8Size(uint32_t);
lean_object* l_Lean_Json_parse(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ImportCompletion_find(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_instDecidableEqPos(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Array_anyMUnsafe_any___at___ImportCompletion_isImportCmdCompletionRequest_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___ImportCompletion_find_spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint32_t l_Char_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___ImportCompletion_computePartialImportCompletions_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___ImportCompletion_addCompletionItemData_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___ImportCompletion_find_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___ImportCompletion_AvailableImports_toImportTrie_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_6 = lean_array_uget(x_1, x_3);
lean_inc(x_6);
x_7 = l_Lean_NameTrie_insert(lean_box(0), x_4, x_6, x_6);
lean_dec(x_6);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_usize_of_nat(x_8);
x_10 = lean_usize_add(x_3, x_9);
x_3 = x_10;
x_4 = x_7;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_ImportCompletion_AvailableImports_toImportTrie(lean_object* x_1) {
_start:
{
lean_object* x_2; size_t x_3; lean_object* x_4; size_t x_5; lean_object* x_6; 
x_2 = l_Lean_NameTrie_empty(lean_box(0));
x_3 = lean_array_size(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_usize_of_nat(x_4);
x_6 = l_Array_forIn_x27Unsafe_loop___at___ImportCompletion_AvailableImports_toImportTrie_spec__0(x_1, x_3, x_5, x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___ImportCompletion_AvailableImports_toImportTrie_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_forIn_x27Unsafe_loop___at___ImportCompletion_AvailableImports_toImportTrie_spec__0(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_ImportCompletion_AvailableImports_toImportTrie___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_ImportCompletion_AvailableImports_toImportTrie(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Array_anyMUnsafe_any___at___ImportCompletion_isImportNameCompletionRequest_spec__0_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_usize_dec_eq(x_3, x_4);
x_6 = lean_box(1);
if (x_5 == 0)
{
lean_object* x_7; uint8_t x_12; lean_object* x_15; lean_object* x_22; uint8_t x_23; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_7 = lean_unsigned_to_nat(1u);
x_33 = lean_unsigned_to_nat(2u);
x_34 = lean_array_uget(x_2, x_3);
x_35 = l_Lean_Syntax_getArg(x_34, x_7);
x_36 = l_Lean_Syntax_getArg(x_34, x_33);
x_37 = l_Lean_Syntax_getOptional_x3f(x_36);
lean_dec(x_36);
x_38 = lean_unsigned_to_nat(3u);
x_39 = l_Lean_Syntax_getArg(x_34, x_38);
lean_dec(x_34);
if (lean_obj_tag(x_37) == 0)
{
goto block_44;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_37, 0);
lean_inc(x_45);
lean_dec(x_37);
x_46 = l_Lean_Syntax_getTailPos_x3f(x_45, x_5);
lean_dec(x_45);
if (lean_obj_tag(x_46) == 0)
{
goto block_44;
}
else
{
lean_dec(x_35);
x_40 = x_46;
goto block_42;
}
}
block_11:
{
size_t x_8; size_t x_9; 
x_8 = lean_usize_of_nat(x_7);
x_9 = lean_usize_add(x_3, x_8);
x_3 = x_9;
goto _start;
}
block_14:
{
if (x_12 == 0)
{
goto block_11;
}
else
{
uint8_t x_13; 
x_13 = lean_unbox(x_6);
return x_13;
}
}
block_21:
{
lean_object* x_16; uint32_t x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_unsigned_to_nat(32u);
x_17 = l_Char_ofNat(x_16);
x_18 = l_Char_utf8Size(x_17);
x_19 = lean_nat_add(x_15, x_18);
lean_dec(x_18);
lean_dec(x_15);
x_20 = l_instDecidableEqPos(x_1, x_19);
lean_dec(x_19);
x_12 = x_20;
goto block_14;
}
block_32:
{
if (x_23 == 0)
{
lean_dec(x_22);
goto block_11;
}
else
{
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_24 = lean_mk_string_unchecked("Init.Data.Option.BasicAux", 25, 25);
x_25 = lean_mk_string_unchecked("Option.get!", 11, 11);
x_26 = lean_unsigned_to_nat(21u);
x_27 = lean_unsigned_to_nat(14u);
x_28 = lean_mk_string_unchecked("value is none", 13, 13);
x_29 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_24, x_25, x_26, x_27, x_28);
lean_dec(x_28);
lean_dec(x_25);
lean_dec(x_24);
x_30 = l_panic___at___Lean_Parser_ParserState_mkUnexpectedTokenErrors_spec__0(x_29);
x_15 = x_30;
goto block_21;
}
else
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_22, 0);
lean_inc(x_31);
lean_dec(x_22);
x_15 = x_31;
goto block_21;
}
}
}
block_42:
{
uint8_t x_41; 
x_41 = l_Lean_Syntax_isMissing(x_39);
lean_dec(x_39);
if (x_41 == 0)
{
x_22 = x_40;
x_23 = x_41;
goto block_32;
}
else
{
if (lean_obj_tag(x_40) == 0)
{
x_12 = x_5;
goto block_14;
}
else
{
x_22 = x_40;
x_23 = x_41;
goto block_32;
}
}
}
block_44:
{
lean_object* x_43; 
x_43 = l_Lean_Syntax_getTailPos_x3f(x_35, x_5);
lean_dec(x_35);
x_40 = x_43;
goto block_42;
}
}
else
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_box(0);
x_48 = lean_unbox(x_47);
return x_48;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___ImportCompletion_isImportNameCompletionRequest_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_usize_dec_eq(x_3, x_4);
x_6 = lean_box(1);
if (x_5 == 0)
{
lean_object* x_7; uint8_t x_12; lean_object* x_15; lean_object* x_22; uint8_t x_23; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_7 = lean_unsigned_to_nat(1u);
x_33 = lean_unsigned_to_nat(2u);
x_34 = lean_array_uget(x_2, x_3);
x_35 = l_Lean_Syntax_getArg(x_34, x_7);
x_36 = l_Lean_Syntax_getArg(x_34, x_33);
x_37 = l_Lean_Syntax_getOptional_x3f(x_36);
lean_dec(x_36);
x_38 = lean_unsigned_to_nat(3u);
x_39 = l_Lean_Syntax_getArg(x_34, x_38);
lean_dec(x_34);
if (lean_obj_tag(x_37) == 0)
{
goto block_44;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_37, 0);
lean_inc(x_45);
lean_dec(x_37);
x_46 = l_Lean_Syntax_getTailPos_x3f(x_45, x_5);
lean_dec(x_45);
if (lean_obj_tag(x_46) == 0)
{
goto block_44;
}
else
{
lean_dec(x_35);
x_40 = x_46;
goto block_42;
}
}
block_11:
{
size_t x_8; size_t x_9; uint8_t x_10; 
x_8 = lean_usize_of_nat(x_7);
x_9 = lean_usize_add(x_3, x_8);
x_10 = l_Array_anyMUnsafe_any___at___Array_anyMUnsafe_any___at___ImportCompletion_isImportNameCompletionRequest_spec__0_spec__0(x_1, x_2, x_9, x_4);
return x_10;
}
block_14:
{
if (x_12 == 0)
{
goto block_11;
}
else
{
uint8_t x_13; 
x_13 = lean_unbox(x_6);
return x_13;
}
}
block_21:
{
lean_object* x_16; uint32_t x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_unsigned_to_nat(32u);
x_17 = l_Char_ofNat(x_16);
x_18 = l_Char_utf8Size(x_17);
x_19 = lean_nat_add(x_15, x_18);
lean_dec(x_18);
lean_dec(x_15);
x_20 = l_instDecidableEqPos(x_1, x_19);
lean_dec(x_19);
x_12 = x_20;
goto block_14;
}
block_32:
{
if (x_23 == 0)
{
lean_dec(x_22);
goto block_11;
}
else
{
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_24 = lean_mk_string_unchecked("Init.Data.Option.BasicAux", 25, 25);
x_25 = lean_mk_string_unchecked("Option.get!", 11, 11);
x_26 = lean_unsigned_to_nat(21u);
x_27 = lean_unsigned_to_nat(14u);
x_28 = lean_mk_string_unchecked("value is none", 13, 13);
x_29 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_24, x_25, x_26, x_27, x_28);
lean_dec(x_28);
lean_dec(x_25);
lean_dec(x_24);
x_30 = l_panic___at___Lean_Parser_ParserState_mkUnexpectedTokenErrors_spec__0(x_29);
x_15 = x_30;
goto block_21;
}
else
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_22, 0);
lean_inc(x_31);
lean_dec(x_22);
x_15 = x_31;
goto block_21;
}
}
}
block_42:
{
uint8_t x_41; 
x_41 = l_Lean_Syntax_isMissing(x_39);
lean_dec(x_39);
if (x_41 == 0)
{
x_22 = x_40;
x_23 = x_41;
goto block_32;
}
else
{
if (lean_obj_tag(x_40) == 0)
{
x_12 = x_5;
goto block_14;
}
else
{
x_22 = x_40;
x_23 = x_41;
goto block_32;
}
}
}
block_44:
{
lean_object* x_43; 
x_43 = l_Lean_Syntax_getTailPos_x3f(x_35, x_5);
lean_dec(x_35);
x_40 = x_43;
goto block_42;
}
}
else
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_box(0);
x_48 = lean_unbox(x_47);
return x_48;
}
}
}
LEAN_EXPORT uint8_t l_ImportCompletion_isImportNameCompletionRequest(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Module", 6, 6);
x_6 = lean_mk_string_unchecked("header", 6, 6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
lean_inc(x_1);
x_8 = l_Lean_Syntax_isOfKind(x_1, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_28; uint8_t x_29; 
x_9 = lean_unsigned_to_nat(0u);
x_28 = l_Lean_Syntax_getArg(x_1, x_9);
x_29 = l_Lean_Syntax_isNone(x_28);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_unsigned_to_nat(1u);
lean_inc(x_28);
x_31 = l_Lean_Syntax_matchesNull(x_28, x_30);
if (x_31 == 0)
{
lean_dec(x_28);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_32 = l_Lean_Syntax_getArg(x_28, x_9);
lean_dec(x_28);
x_33 = lean_mk_string_unchecked("moduleTk", 8, 8);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_34 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_33);
x_35 = l_Lean_Syntax_isOfKind(x_32, x_34);
lean_dec(x_34);
if (x_35 == 0)
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_35;
}
else
{
goto block_27;
}
}
}
else
{
lean_dec(x_28);
goto block_27;
}
block_18:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_unsigned_to_nat(2u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
lean_dec(x_1);
x_12 = l_Lean_Syntax_getArgs(x_11);
lean_dec(x_11);
x_13 = lean_array_get_size(x_12);
x_14 = lean_nat_dec_lt(x_9, x_13);
if (x_14 == 0)
{
lean_dec(x_13);
lean_dec(x_12);
return x_14;
}
else
{
if (x_14 == 0)
{
lean_dec(x_13);
lean_dec(x_12);
return x_14;
}
else
{
size_t x_15; size_t x_16; uint8_t x_17; 
x_15 = lean_usize_of_nat(x_9);
x_16 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_17 = l_Array_anyMUnsafe_any___at___ImportCompletion_isImportNameCompletionRequest_spec__0(x_2, x_12, x_15, x_16);
lean_dec(x_12);
return x_17;
}
}
}
block_27:
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = l_Lean_Syntax_getArg(x_1, x_19);
x_21 = l_Lean_Syntax_isNone(x_20);
if (x_21 == 0)
{
uint8_t x_22; 
lean_inc(x_20);
x_22 = l_Lean_Syntax_matchesNull(x_20, x_19);
if (x_22 == 0)
{
lean_dec(x_20);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = l_Lean_Syntax_getArg(x_20, x_9);
lean_dec(x_20);
x_24 = lean_mk_string_unchecked("prelude", 7, 7);
x_25 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_24);
x_26 = l_Lean_Syntax_isOfKind(x_23, x_25);
lean_dec(x_25);
if (x_26 == 0)
{
lean_dec(x_1);
return x_26;
}
else
{
goto block_18;
}
}
}
else
{
lean_dec(x_20);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
goto block_18;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Array_anyMUnsafe_any___at___ImportCompletion_isImportNameCompletionRequest_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at___Array_anyMUnsafe_any___at___ImportCompletion_isImportNameCompletionRequest_spec__0_spec__0(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___ImportCompletion_isImportNameCompletionRequest_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at___ImportCompletion_isImportNameCompletionRequest_spec__0(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_ImportCompletion_isImportNameCompletionRequest___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_ImportCompletion_isImportNameCompletionRequest(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Array_anyMUnsafe_any___at___ImportCompletion_isImportCmdCompletionRequest_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("Parser", 6, 6);
x_8 = lean_mk_string_unchecked("Module", 6, 6);
x_9 = lean_mk_string_unchecked("header", 6, 6);
x_10 = lean_usize_dec_eq(x_4, x_5);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; lean_object* x_19; lean_object* x_22; lean_object* x_23; lean_object* x_35; 
x_11 = lean_box(1);
x_22 = lean_array_uget(x_3, x_4);
x_35 = l_Lean_Syntax_getPos_x3f(x_22, x_10);
if (lean_obj_tag(x_35) == 0)
{
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_12 = x_10;
goto block_18;
}
else
{
lean_object* x_36; uint8_t x_37; 
x_36 = l_Lean_Name_mkStr4(x_6, x_7, x_8, x_9);
lean_inc(x_2);
x_37 = l_Lean_Syntax_isOfKind(x_2, x_36);
lean_dec(x_36);
if (x_37 == 0)
{
lean_dec(x_35);
lean_dec(x_22);
x_12 = x_37;
goto block_18;
}
else
{
lean_object* x_38; 
x_38 = l_Lean_Syntax_getTailPos_x3f(x_22, x_10);
if (lean_obj_tag(x_38) == 0)
{
lean_dec(x_35);
lean_dec(x_22);
x_12 = x_10;
goto block_18;
}
else
{
lean_dec(x_38);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_39 = lean_mk_string_unchecked("Init.Data.Option.BasicAux", 25, 25);
x_40 = lean_mk_string_unchecked("Option.get!", 11, 11);
x_41 = lean_unsigned_to_nat(21u);
x_42 = lean_unsigned_to_nat(14u);
x_43 = lean_mk_string_unchecked("value is none", 13, 13);
x_44 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_39, x_40, x_41, x_42, x_43);
lean_dec(x_43);
lean_dec(x_40);
lean_dec(x_39);
x_45 = l_panic___at___Lean_Parser_ParserState_mkUnexpectedTokenErrors_spec__0(x_44);
x_23 = x_45;
goto block_34;
}
else
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_35, 0);
lean_inc(x_46);
lean_dec(x_35);
x_23 = x_46;
goto block_34;
}
}
}
}
block_18:
{
if (x_12 == 0)
{
lean_object* x_13; size_t x_14; size_t x_15; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_usize_of_nat(x_13);
x_15 = lean_usize_add(x_4, x_14);
x_4 = x_15;
goto _start;
}
else
{
uint8_t x_17; 
lean_dec(x_2);
x_17 = lean_unbox(x_11);
return x_17;
}
}
block_21:
{
uint8_t x_20; 
x_20 = lean_nat_dec_le(x_1, x_19);
lean_dec(x_19);
x_12 = x_20;
goto block_18;
}
block_34:
{
uint8_t x_24; 
x_24 = lean_nat_dec_le(x_23, x_1);
lean_dec(x_23);
if (x_24 == 0)
{
lean_dec(x_22);
x_12 = x_24;
goto block_18;
}
else
{
lean_object* x_25; 
x_25 = l_Lean_Syntax_getTailPos_x3f(x_22, x_10);
lean_dec(x_22);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_26 = lean_mk_string_unchecked("Init.Data.Option.BasicAux", 25, 25);
x_27 = lean_mk_string_unchecked("Option.get!", 11, 11);
x_28 = lean_unsigned_to_nat(21u);
x_29 = lean_unsigned_to_nat(14u);
x_30 = lean_mk_string_unchecked("value is none", 13, 13);
x_31 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_26, x_27, x_28, x_29, x_30);
lean_dec(x_30);
lean_dec(x_27);
lean_dec(x_26);
x_32 = l_panic___at___Lean_Parser_ParserState_mkUnexpectedTokenErrors_spec__0(x_31);
x_19 = x_32;
goto block_21;
}
else
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_25, 0);
lean_inc(x_33);
lean_dec(x_25);
x_19 = x_33;
goto block_21;
}
}
}
}
else
{
lean_object* x_47; uint8_t x_48; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_47 = lean_box(0);
x_48 = lean_unbox(x_47);
return x_48;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___ImportCompletion_isImportCmdCompletionRequest_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("Parser", 6, 6);
x_8 = lean_mk_string_unchecked("Module", 6, 6);
x_9 = lean_mk_string_unchecked("header", 6, 6);
x_10 = lean_usize_dec_eq(x_4, x_5);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; lean_object* x_19; lean_object* x_22; lean_object* x_23; lean_object* x_35; 
x_11 = lean_box(1);
x_22 = lean_array_uget(x_3, x_4);
x_35 = l_Lean_Syntax_getPos_x3f(x_22, x_10);
if (lean_obj_tag(x_35) == 0)
{
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_12 = x_10;
goto block_18;
}
else
{
lean_object* x_36; uint8_t x_37; 
x_36 = l_Lean_Name_mkStr4(x_6, x_7, x_8, x_9);
lean_inc(x_2);
x_37 = l_Lean_Syntax_isOfKind(x_2, x_36);
lean_dec(x_36);
if (x_37 == 0)
{
lean_dec(x_35);
lean_dec(x_22);
x_12 = x_37;
goto block_18;
}
else
{
lean_object* x_38; 
x_38 = l_Lean_Syntax_getTailPos_x3f(x_22, x_10);
if (lean_obj_tag(x_38) == 0)
{
lean_dec(x_35);
lean_dec(x_22);
x_12 = x_10;
goto block_18;
}
else
{
lean_dec(x_38);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_39 = lean_mk_string_unchecked("Init.Data.Option.BasicAux", 25, 25);
x_40 = lean_mk_string_unchecked("Option.get!", 11, 11);
x_41 = lean_unsigned_to_nat(21u);
x_42 = lean_unsigned_to_nat(14u);
x_43 = lean_mk_string_unchecked("value is none", 13, 13);
x_44 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_39, x_40, x_41, x_42, x_43);
lean_dec(x_43);
lean_dec(x_40);
lean_dec(x_39);
x_45 = l_panic___at___Lean_Parser_ParserState_mkUnexpectedTokenErrors_spec__0(x_44);
x_23 = x_45;
goto block_34;
}
else
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_35, 0);
lean_inc(x_46);
lean_dec(x_35);
x_23 = x_46;
goto block_34;
}
}
}
}
block_18:
{
if (x_12 == 0)
{
lean_object* x_13; size_t x_14; size_t x_15; uint8_t x_16; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_usize_of_nat(x_13);
x_15 = lean_usize_add(x_4, x_14);
x_16 = l_Array_anyMUnsafe_any___at___Array_anyMUnsafe_any___at___ImportCompletion_isImportCmdCompletionRequest_spec__0_spec__0(x_1, x_2, x_3, x_15, x_5);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_2);
x_17 = lean_unbox(x_11);
return x_17;
}
}
block_21:
{
uint8_t x_20; 
x_20 = lean_nat_dec_le(x_1, x_19);
lean_dec(x_19);
x_12 = x_20;
goto block_18;
}
block_34:
{
uint8_t x_24; 
x_24 = lean_nat_dec_le(x_23, x_1);
lean_dec(x_23);
if (x_24 == 0)
{
lean_dec(x_22);
x_12 = x_24;
goto block_18;
}
else
{
lean_object* x_25; 
x_25 = l_Lean_Syntax_getTailPos_x3f(x_22, x_10);
lean_dec(x_22);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_26 = lean_mk_string_unchecked("Init.Data.Option.BasicAux", 25, 25);
x_27 = lean_mk_string_unchecked("Option.get!", 11, 11);
x_28 = lean_unsigned_to_nat(21u);
x_29 = lean_unsigned_to_nat(14u);
x_30 = lean_mk_string_unchecked("value is none", 13, 13);
x_31 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_26, x_27, x_28, x_29, x_30);
lean_dec(x_30);
lean_dec(x_27);
lean_dec(x_26);
x_32 = l_panic___at___Lean_Parser_ParserState_mkUnexpectedTokenErrors_spec__0(x_31);
x_19 = x_32;
goto block_21;
}
else
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_25, 0);
lean_inc(x_33);
lean_dec(x_25);
x_19 = x_33;
goto block_21;
}
}
}
}
else
{
lean_object* x_47; uint8_t x_48; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_47 = lean_box(0);
x_48 = lean_unbox(x_47);
return x_48;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Array_anyMUnsafe_any___at___ImportCompletion_isImportCmdCompletionRequest_spec__2_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_7 = lean_box(1);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_uget(x_3, x_4);
x_17 = l_Lean_Syntax_getArgs(x_16);
lean_dec(x_16);
x_18 = lean_array_get_size(x_17);
x_19 = lean_nat_dec_lt(x_15, x_18);
if (x_19 == 0)
{
lean_dec(x_18);
lean_dec(x_17);
x_8 = x_6;
goto block_14;
}
else
{
if (x_19 == 0)
{
lean_dec(x_18);
lean_dec(x_17);
x_8 = x_6;
goto block_14;
}
else
{
size_t x_20; size_t x_21; uint8_t x_22; 
x_20 = lean_usize_of_nat(x_15);
x_21 = lean_usize_of_nat(x_18);
lean_dec(x_18);
lean_inc(x_2);
x_22 = l_Array_anyMUnsafe_any___at___ImportCompletion_isImportCmdCompletionRequest_spec__0(x_1, x_2, x_17, x_20, x_21);
lean_dec(x_17);
x_8 = x_22;
goto block_14;
}
}
block_14:
{
if (x_8 == 0)
{
lean_object* x_9; size_t x_10; size_t x_11; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_usize_of_nat(x_9);
x_11 = lean_usize_add(x_4, x_10);
x_4 = x_11;
goto _start;
}
else
{
uint8_t x_13; 
lean_dec(x_2);
x_13 = lean_unbox(x_7);
return x_13;
}
}
}
else
{
lean_object* x_23; uint8_t x_24; 
lean_dec(x_2);
x_23 = lean_box(0);
x_24 = lean_unbox(x_23);
return x_24;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___ImportCompletion_isImportCmdCompletionRequest_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_7 = lean_box(1);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_uget(x_3, x_4);
x_17 = l_Lean_Syntax_getArgs(x_16);
lean_dec(x_16);
x_18 = lean_array_get_size(x_17);
x_19 = lean_nat_dec_lt(x_15, x_18);
if (x_19 == 0)
{
lean_dec(x_18);
lean_dec(x_17);
x_8 = x_6;
goto block_14;
}
else
{
if (x_19 == 0)
{
lean_dec(x_18);
lean_dec(x_17);
x_8 = x_6;
goto block_14;
}
else
{
size_t x_20; size_t x_21; uint8_t x_22; 
x_20 = lean_usize_of_nat(x_15);
x_21 = lean_usize_of_nat(x_18);
lean_dec(x_18);
lean_inc(x_2);
x_22 = l_Array_anyMUnsafe_any___at___ImportCompletion_isImportCmdCompletionRequest_spec__0(x_1, x_2, x_17, x_20, x_21);
lean_dec(x_17);
x_8 = x_22;
goto block_14;
}
}
block_14:
{
if (x_8 == 0)
{
lean_object* x_9; size_t x_10; size_t x_11; uint8_t x_12; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_usize_of_nat(x_9);
x_11 = lean_usize_add(x_4, x_10);
x_12 = l_Array_anyMUnsafe_any___at___Array_anyMUnsafe_any___at___ImportCompletion_isImportCmdCompletionRequest_spec__2_spec__2(x_1, x_2, x_3, x_11, x_5);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_2);
x_13 = lean_unbox(x_7);
return x_13;
}
}
}
else
{
lean_object* x_23; uint8_t x_24; 
lean_dec(x_2);
x_23 = lean_box(0);
x_24 = lean_unbox(x_23);
return x_24;
}
}
}
LEAN_EXPORT uint8_t l_ImportCompletion_isImportCmdCompletionRequest(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Module", 6, 6);
x_6 = lean_mk_string_unchecked("header", 6, 6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
lean_inc(x_1);
x_8 = l_Lean_Syntax_isOfKind(x_1, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_30; uint8_t x_31; 
x_9 = lean_unsigned_to_nat(0u);
x_30 = l_Lean_Syntax_getArg(x_1, x_9);
x_31 = l_Lean_Syntax_isNone(x_30);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_unsigned_to_nat(1u);
lean_inc(x_30);
x_33 = l_Lean_Syntax_matchesNull(x_30, x_32);
if (x_33 == 0)
{
lean_dec(x_30);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_34 = l_Lean_Syntax_getArg(x_30, x_9);
lean_dec(x_30);
x_35 = lean_mk_string_unchecked("moduleTk", 8, 8);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_36 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_35);
x_37 = l_Lean_Syntax_isOfKind(x_34, x_36);
lean_dec(x_36);
if (x_37 == 0)
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_37;
}
else
{
goto block_29;
}
}
}
else
{
lean_dec(x_30);
goto block_29;
}
block_20:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_unsigned_to_nat(2u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
x_12 = l_Lean_Syntax_getArgs(x_11);
lean_dec(x_11);
x_13 = lean_array_get_size(x_12);
x_14 = lean_nat_dec_lt(x_9, x_13);
if (x_14 == 0)
{
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_1);
return x_8;
}
else
{
if (x_14 == 0)
{
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_1);
return x_8;
}
else
{
size_t x_15; size_t x_16; uint8_t x_17; 
x_15 = lean_usize_of_nat(x_9);
x_16 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_17 = l_Array_anyMUnsafe_any___at___ImportCompletion_isImportCmdCompletionRequest_spec__2(x_2, x_1, x_12, x_15, x_16);
lean_dec(x_12);
if (x_17 == 0)
{
return x_8;
}
else
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_box(0);
x_19 = lean_unbox(x_18);
return x_19;
}
}
}
}
block_29:
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_unsigned_to_nat(1u);
x_22 = l_Lean_Syntax_getArg(x_1, x_21);
x_23 = l_Lean_Syntax_isNone(x_22);
if (x_23 == 0)
{
uint8_t x_24; 
lean_inc(x_22);
x_24 = l_Lean_Syntax_matchesNull(x_22, x_21);
if (x_24 == 0)
{
lean_dec(x_22);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = l_Lean_Syntax_getArg(x_22, x_9);
lean_dec(x_22);
x_26 = lean_mk_string_unchecked("prelude", 7, 7);
x_27 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_26);
x_28 = l_Lean_Syntax_isOfKind(x_25, x_27);
lean_dec(x_27);
if (x_28 == 0)
{
lean_dec(x_1);
return x_28;
}
else
{
goto block_20;
}
}
}
else
{
lean_dec(x_22);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
goto block_20;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Array_anyMUnsafe_any___at___ImportCompletion_isImportCmdCompletionRequest_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l_Array_anyMUnsafe_any___at___Array_anyMUnsafe_any___at___ImportCompletion_isImportCmdCompletionRequest_spec__0_spec__0(x_1, x_2, x_3, x_6, x_7);
lean_dec(x_3);
lean_dec(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___ImportCompletion_isImportCmdCompletionRequest_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l_Array_anyMUnsafe_any___at___ImportCompletion_isImportCmdCompletionRequest_spec__0(x_1, x_2, x_3, x_6, x_7);
lean_dec(x_3);
lean_dec(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Array_anyMUnsafe_any___at___ImportCompletion_isImportCmdCompletionRequest_spec__2_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l_Array_anyMUnsafe_any___at___Array_anyMUnsafe_any___at___ImportCompletion_isImportCmdCompletionRequest_spec__2_spec__2(x_1, x_2, x_3, x_6, x_7);
lean_dec(x_3);
lean_dec(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___ImportCompletion_isImportCmdCompletionRequest_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l_Array_anyMUnsafe_any___at___ImportCompletion_isImportCmdCompletionRequest_spec__2(x_1, x_2, x_3, x_6, x_7);
lean_dec(x_3);
lean_dec(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_ImportCompletion_isImportCmdCompletionRequest___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_ImportCompletion_isImportCmdCompletionRequest(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___ImportCompletion_computePartialImportCompletions_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_mk_string_unchecked("Lean", 4, 4);
x_13 = lean_mk_string_unchecked("Parser", 6, 6);
x_14 = lean_mk_string_unchecked("Module", 6, 6);
x_15 = lean_mk_string_unchecked("header", 6, 6);
x_16 = lean_usize_dec_eq(x_3, x_4);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_array_uget(x_2, x_3);
x_18 = l_Lean_Name_isAnonymous(x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = l_Lean_Name_mkStr4(x_12, x_13, x_14, x_15);
lean_inc(x_1);
x_20 = l_Lean_Syntax_isOfKind(x_1, x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_dec(x_17);
x_6 = x_5;
goto block_11;
}
else
{
lean_object* x_21; 
x_21 = lean_array_push(x_5, x_17);
x_6 = x_21;
goto block_11;
}
}
else
{
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_6 = x_5;
goto block_11;
}
}
else
{
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_1);
return x_5;
}
block_11:
{
lean_object* x_7; size_t x_8; size_t x_9; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_usize_of_nat(x_7);
x_9 = lean_usize_add(x_3, x_8);
x_3 = x_9;
x_5 = x_6;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___ImportCompletion_computePartialImportCompletions_spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2_spec__2___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_65; uint8_t x_66; 
x_65 = l_Lean_Syntax_getArg(x_1, x_2);
x_66 = l_Lean_Syntax_isNone(x_65);
if (x_66 == 0)
{
uint8_t x_67; 
lean_inc(x_65);
x_67 = l_Lean_Syntax_matchesNull(x_65, x_5);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_65);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_68 = lean_mk_string_unchecked("Lean.Server.Completion.ImportCompletion", 39, 39);
x_69 = lean_mk_string_unchecked("ImportCompletion.computePartialImportCompletions", 48, 48);
x_70 = lean_unsigned_to_nat(56u);
x_71 = lean_unsigned_to_nat(10u);
x_72 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_73 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_68, x_69, x_70, x_71, x_72);
lean_dec(x_72);
lean_dec(x_69);
lean_dec(x_68);
x_74 = l_panic___at___ImportCompletion_computePartialImportCompletions_spec__1(x_73);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_75 = l_Lean_Syntax_getArg(x_65, x_3);
lean_dec(x_65);
x_76 = lean_mk_string_unchecked("all", 3, 3);
x_77 = l_Lean_Name_mkStr4(x_6, x_7, x_8, x_76);
x_78 = l_Lean_Syntax_isOfKind(x_75, x_77);
lean_dec(x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_79 = lean_mk_string_unchecked("Lean.Server.Completion.ImportCompletion", 39, 39);
x_80 = lean_mk_string_unchecked("ImportCompletion.computePartialImportCompletions", 48, 48);
x_81 = lean_unsigned_to_nat(56u);
x_82 = lean_unsigned_to_nat(10u);
x_83 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_84 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_79, x_80, x_81, x_82, x_83);
lean_dec(x_83);
lean_dec(x_80);
lean_dec(x_79);
x_85 = l_panic___at___ImportCompletion_computePartialImportCompletions_spec__1(x_84);
return x_85;
}
else
{
goto block_64;
}
}
}
else
{
lean_dec(x_65);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
goto block_64;
}
block_64:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_unsigned_to_nat(3u);
x_11 = lean_unsigned_to_nat(4u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = l_Lean_Syntax_isNone(x_12);
if (x_13 == 0)
{
uint8_t x_14; 
lean_inc(x_12);
x_14 = l_Lean_Syntax_matchesNull(x_12, x_2);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_12);
x_15 = lean_mk_string_unchecked("Lean.Server.Completion.ImportCompletion", 39, 39);
x_16 = lean_mk_string_unchecked("ImportCompletion.computePartialImportCompletions", 48, 48);
x_17 = lean_unsigned_to_nat(56u);
x_18 = lean_unsigned_to_nat(10u);
x_19 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_20 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_15, x_16, x_17, x_18, x_19);
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_15);
x_21 = l_panic___at___ImportCompletion_computePartialImportCompletions_spec__1(x_20);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = l_Lean_Syntax_getArg(x_12, x_3);
lean_dec(x_12);
x_23 = l_Lean_Syntax_getTailPos_x3f(x_22, x_13);
lean_dec(x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
x_24 = lean_box(0);
return x_24;
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_23);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_23, 0);
x_27 = l_instDecidableEqPos(x_26, x_4);
lean_dec(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
lean_free_object(x_23);
x_28 = lean_box(0);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = l_Lean_Syntax_getArg(x_1, x_10);
x_30 = l_Lean_Syntax_getId(x_29);
lean_dec(x_29);
x_31 = lean_mk_string_unchecked("", 0, 0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_23, 0, x_32);
return x_23;
}
}
else
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_23, 0);
lean_inc(x_33);
lean_dec(x_23);
x_34 = l_instDecidableEqPos(x_33, x_4);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_box(0);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_36 = l_Lean_Syntax_getArg(x_1, x_10);
x_37 = l_Lean_Syntax_getId(x_36);
lean_dec(x_36);
x_38 = lean_mk_string_unchecked("", 0, 0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
return x_40;
}
}
}
}
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; 
lean_dec(x_12);
x_41 = l_Lean_Syntax_getArg(x_1, x_10);
x_42 = lean_box(0);
x_43 = lean_unbox(x_42);
x_44 = l_Lean_Syntax_getTailPos_x3f(x_41, x_43);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; 
lean_dec(x_41);
x_45 = lean_box(0);
return x_45;
}
else
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_44);
if (x_46 == 0)
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_ctor_get(x_44, 0);
x_48 = l_instDecidableEqPos(x_47, x_4);
lean_dec(x_47);
if (x_48 == 0)
{
lean_object* x_49; 
lean_free_object(x_44);
lean_dec(x_41);
x_49 = lean_box(0);
return x_49;
}
else
{
lean_object* x_50; 
x_50 = l_Lean_Syntax_getId(x_41);
lean_dec(x_41);
if (lean_obj_tag(x_50) == 1)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
lean_ctor_set(x_44, 0, x_53);
return x_44;
}
else
{
lean_object* x_54; 
lean_dec(x_50);
lean_free_object(x_44);
x_54 = lean_box(0);
return x_54;
}
}
}
else
{
lean_object* x_55; uint8_t x_56; 
x_55 = lean_ctor_get(x_44, 0);
lean_inc(x_55);
lean_dec(x_44);
x_56 = l_instDecidableEqPos(x_55, x_4);
lean_dec(x_55);
if (x_56 == 0)
{
lean_object* x_57; 
lean_dec(x_41);
x_57 = lean_box(0);
return x_57;
}
else
{
lean_object* x_58; 
x_58 = l_Lean_Syntax_getId(x_41);
lean_dec(x_41);
if (lean_obj_tag(x_58) == 1)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_61);
return x_62;
}
else
{
lean_object* x_63; 
lean_dec(x_58);
x_63 = lean_box(0);
return x_63;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2_spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_box(0);
x_7 = lean_usize_dec_lt(x_4, x_3);
if (x_7 == 0)
{
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
lean_dec(x_5);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_mk_string_unchecked("import", 6, 6);
x_11 = lean_unsigned_to_nat(1u);
x_19 = lean_mk_string_unchecked("Lean", 4, 4);
x_20 = lean_mk_string_unchecked("Parser", 6, 6);
x_21 = lean_mk_string_unchecked("Module", 6, 6);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
x_22 = l_Lean_Name_mkStr4(x_19, x_20, x_21, x_10);
x_23 = lean_array_uget(x_2, x_4);
lean_inc(x_23);
x_24 = l_Lean_Syntax_isOfKind(x_23, x_22);
lean_dec(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
x_25 = lean_mk_string_unchecked("Lean.Server.Completion.ImportCompletion", 39, 39);
x_26 = lean_mk_string_unchecked("ImportCompletion.computePartialImportCompletions", 48, 48);
x_27 = lean_unsigned_to_nat(56u);
x_28 = lean_unsigned_to_nat(10u);
x_29 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_30 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_25, x_26, x_27, x_28, x_29);
lean_dec(x_29);
lean_dec(x_26);
lean_dec(x_25);
x_31 = l_panic___at___ImportCompletion_computePartialImportCompletions_spec__1(x_30);
x_12 = x_31;
goto block_18;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_32 = lean_unsigned_to_nat(2u);
x_33 = lean_unsigned_to_nat(0u);
x_34 = l_Lean_Syntax_getArg(x_23, x_33);
x_35 = l_Lean_Syntax_isNone(x_34);
if (x_35 == 0)
{
uint8_t x_36; 
lean_inc(x_34);
x_36 = l_Lean_Syntax_matchesNull(x_34, x_11);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_34);
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
x_37 = lean_mk_string_unchecked("Lean.Server.Completion.ImportCompletion", 39, 39);
x_38 = lean_mk_string_unchecked("ImportCompletion.computePartialImportCompletions", 48, 48);
x_39 = lean_unsigned_to_nat(56u);
x_40 = lean_unsigned_to_nat(10u);
x_41 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_42 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_37, x_38, x_39, x_40, x_41);
lean_dec(x_41);
lean_dec(x_38);
lean_dec(x_37);
x_43 = l_panic___at___ImportCompletion_computePartialImportCompletions_spec__1(x_42);
x_12 = x_43;
goto block_18;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_44 = l_Lean_Syntax_getArg(x_34, x_33);
lean_dec(x_34);
x_45 = lean_mk_string_unchecked("private", 7, 7);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
x_46 = l_Lean_Name_mkStr4(x_19, x_20, x_21, x_45);
x_47 = l_Lean_Syntax_isOfKind(x_44, x_46);
lean_dec(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
x_48 = lean_mk_string_unchecked("Lean.Server.Completion.ImportCompletion", 39, 39);
x_49 = lean_mk_string_unchecked("ImportCompletion.computePartialImportCompletions", 48, 48);
x_50 = lean_unsigned_to_nat(56u);
x_51 = lean_unsigned_to_nat(10u);
x_52 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_53 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_48, x_49, x_50, x_51, x_52);
lean_dec(x_52);
lean_dec(x_49);
lean_dec(x_48);
x_54 = l_panic___at___ImportCompletion_computePartialImportCompletions_spec__1(x_53);
x_12 = x_54;
goto block_18;
}
else
{
lean_object* x_55; 
x_55 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2_spec__2___lam__0(x_23, x_32, x_33, x_1, x_11, x_19, x_20, x_21, x_8);
lean_dec(x_23);
x_12 = x_55;
goto block_18;
}
}
}
else
{
lean_object* x_56; 
lean_dec(x_34);
x_56 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2_spec__2___lam__0(x_23, x_32, x_33, x_1, x_11, x_19, x_20, x_21, x_8);
lean_dec(x_23);
x_12 = x_56;
goto block_18;
}
}
block_18:
{
if (lean_obj_tag(x_12) == 0)
{
size_t x_13; size_t x_14; 
x_13 = lean_usize_of_nat(x_11);
x_14 = lean_usize_add(x_4, x_13);
x_4 = x_14;
x_5 = x_9;
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_9);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_12);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_8);
return x_17;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_box(0);
x_7 = lean_usize_dec_lt(x_4, x_3);
if (x_7 == 0)
{
lean_inc(x_5);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_mk_string_unchecked("import", 6, 6);
x_11 = lean_unsigned_to_nat(1u);
x_19 = lean_mk_string_unchecked("Lean", 4, 4);
x_20 = lean_mk_string_unchecked("Parser", 6, 6);
x_21 = lean_mk_string_unchecked("Module", 6, 6);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
x_22 = l_Lean_Name_mkStr4(x_19, x_20, x_21, x_10);
x_23 = lean_array_uget(x_2, x_4);
lean_inc(x_23);
x_24 = l_Lean_Syntax_isOfKind(x_23, x_22);
lean_dec(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
x_25 = lean_mk_string_unchecked("Lean.Server.Completion.ImportCompletion", 39, 39);
x_26 = lean_mk_string_unchecked("ImportCompletion.computePartialImportCompletions", 48, 48);
x_27 = lean_unsigned_to_nat(56u);
x_28 = lean_unsigned_to_nat(10u);
x_29 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_30 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_25, x_26, x_27, x_28, x_29);
lean_dec(x_29);
lean_dec(x_26);
lean_dec(x_25);
x_31 = l_panic___at___ImportCompletion_computePartialImportCompletions_spec__1(x_30);
x_12 = x_31;
goto block_18;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_32 = lean_unsigned_to_nat(2u);
x_33 = lean_unsigned_to_nat(0u);
x_34 = l_Lean_Syntax_getArg(x_23, x_33);
x_35 = l_Lean_Syntax_isNone(x_34);
if (x_35 == 0)
{
uint8_t x_36; 
lean_inc(x_34);
x_36 = l_Lean_Syntax_matchesNull(x_34, x_11);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_34);
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
x_37 = lean_mk_string_unchecked("Lean.Server.Completion.ImportCompletion", 39, 39);
x_38 = lean_mk_string_unchecked("ImportCompletion.computePartialImportCompletions", 48, 48);
x_39 = lean_unsigned_to_nat(56u);
x_40 = lean_unsigned_to_nat(10u);
x_41 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_42 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_37, x_38, x_39, x_40, x_41);
lean_dec(x_41);
lean_dec(x_38);
lean_dec(x_37);
x_43 = l_panic___at___ImportCompletion_computePartialImportCompletions_spec__1(x_42);
x_12 = x_43;
goto block_18;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_44 = l_Lean_Syntax_getArg(x_34, x_33);
lean_dec(x_34);
x_45 = lean_mk_string_unchecked("private", 7, 7);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
x_46 = l_Lean_Name_mkStr4(x_19, x_20, x_21, x_45);
x_47 = l_Lean_Syntax_isOfKind(x_44, x_46);
lean_dec(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
x_48 = lean_mk_string_unchecked("Lean.Server.Completion.ImportCompletion", 39, 39);
x_49 = lean_mk_string_unchecked("ImportCompletion.computePartialImportCompletions", 48, 48);
x_50 = lean_unsigned_to_nat(56u);
x_51 = lean_unsigned_to_nat(10u);
x_52 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_53 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_48, x_49, x_50, x_51, x_52);
lean_dec(x_52);
lean_dec(x_49);
lean_dec(x_48);
x_54 = l_panic___at___ImportCompletion_computePartialImportCompletions_spec__1(x_53);
x_12 = x_54;
goto block_18;
}
else
{
lean_object* x_55; 
x_55 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2_spec__2___lam__0(x_23, x_32, x_33, x_1, x_11, x_19, x_20, x_21, x_8);
lean_dec(x_23);
x_12 = x_55;
goto block_18;
}
}
}
else
{
lean_object* x_56; 
lean_dec(x_34);
x_56 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2_spec__2___lam__0(x_23, x_32, x_33, x_1, x_11, x_19, x_20, x_21, x_8);
lean_dec(x_23);
x_12 = x_56;
goto block_18;
}
}
block_18:
{
if (lean_obj_tag(x_12) == 0)
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_usize_of_nat(x_11);
x_14 = lean_usize_add(x_4, x_13);
x_15 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2_spec__2(x_1, x_2, x_3, x_14, x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_9);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_12);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_8);
return x_17;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___ImportCompletion_computePartialImportCompletions_spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_box(0);
x_8 = lean_array_uset(x_4, x_3, x_7);
x_9 = lean_box(0);
x_10 = l_Lean_Name_replacePrefix(x_6, x_1, x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_usize_of_nat(x_11);
x_13 = lean_usize_add(x_3, x_12);
x_14 = lean_array_uset(x_8, x_3, x_10);
x_3 = x_13;
x_4 = x_14;
goto _start;
}
}
}
LEAN_EXPORT uint8_t l_Array_foldlMUnsafe_fold___at___ImportCompletion_computePartialImportCompletions_spec__5___lam__0(uint8_t x_1, lean_object* x_2) {
_start:
{
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___ImportCompletion_computePartialImportCompletions_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_mk_string_unchecked("Lean", 4, 4);
x_14 = lean_mk_string_unchecked("Parser", 6, 6);
x_15 = lean_mk_string_unchecked("Module", 6, 6);
x_16 = lean_mk_string_unchecked("header", 6, 6);
x_17 = lean_usize_dec_eq(x_4, x_5);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_18 = l_Lean_Name_mkStr4(x_13, x_14, x_15, x_16);
x_19 = lean_box(x_17);
x_20 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at___ImportCompletion_computePartialImportCompletions_spec__5___lam__0___boxed), 2, 1);
lean_closure_set(x_20, 0, x_19);
lean_inc(x_1);
x_21 = l_Lean_Syntax_isOfKind(x_1, x_18);
lean_dec(x_18);
x_22 = lean_array_uget(x_3, x_4);
lean_inc(x_22);
x_23 = l_Lean_Name_toString(x_22, x_21, x_20);
x_24 = lean_unsigned_to_nat(0u);
x_25 = lean_string_utf8_byte_size(x_23);
lean_inc(x_23);
x_26 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_24);
lean_ctor_set(x_26, 2, x_25);
x_27 = lean_string_length(x_2);
x_28 = l_Substring_nextn(x_26, x_27, x_24);
lean_dec(x_26);
x_29 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_29, 1, x_24);
lean_ctor_set(x_29, 2, x_28);
x_30 = lean_string_utf8_byte_size(x_2);
lean_inc(x_2);
x_31 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_31, 0, x_2);
lean_ctor_set(x_31, 1, x_24);
lean_ctor_set(x_31, 2, x_30);
x_32 = l_Substring_beq(x_29, x_31);
if (x_32 == 0)
{
lean_dec(x_22);
x_7 = x_6;
goto block_12;
}
else
{
lean_object* x_33; 
x_33 = lean_array_push(x_6, x_22);
x_7 = x_33;
goto block_12;
}
}
else
{
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
block_12:
{
lean_object* x_8; size_t x_9; size_t x_10; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_usize_of_nat(x_8);
x_10 = lean_usize_add(x_4, x_9);
x_4 = x_10;
x_6 = x_7;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_ImportCompletion_computePartialImportCompletions(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
x_8 = lean_mk_string_unchecked("Parser", 6, 6);
x_9 = lean_mk_string_unchecked("Module", 6, 6);
x_10 = lean_mk_string_unchecked("header", 6, 6);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_11 = l_Lean_Name_mkStr4(x_7, x_8, x_9, x_10);
lean_inc(x_1);
x_12 = l_Lean_Syntax_isOfKind(x_1, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_mk_empty_array_with_capacity(x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_25; lean_object* x_26; lean_object* x_35; lean_object* x_71; uint8_t x_72; 
x_15 = lean_unsigned_to_nat(0u);
x_71 = l_Lean_Syntax_getArg(x_1, x_15);
x_72 = l_Lean_Syntax_isNone(x_71);
if (x_72 == 0)
{
lean_object* x_73; uint8_t x_74; 
x_73 = lean_unsigned_to_nat(1u);
lean_inc(x_71);
x_74 = l_Lean_Syntax_matchesNull(x_71, x_73);
if (x_74 == 0)
{
lean_object* x_75; 
lean_dec(x_71);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_75 = lean_mk_empty_array_with_capacity(x_15);
return x_75;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_76 = l_Lean_Syntax_getArg(x_71, x_15);
lean_dec(x_71);
x_77 = lean_mk_string_unchecked("moduleTk", 8, 8);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_78 = l_Lean_Name_mkStr4(x_7, x_8, x_9, x_77);
x_79 = l_Lean_Syntax_isOfKind(x_76, x_78);
lean_dec(x_78);
if (x_79 == 0)
{
lean_object* x_80; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_80 = lean_mk_empty_array_with_capacity(x_15);
return x_80;
}
else
{
goto block_70;
}
}
}
else
{
lean_dec(x_71);
goto block_70;
}
block_24:
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_array_get_size(x_17);
x_19 = lean_nat_dec_eq(x_18, x_15);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_nat_sub(x_18, x_16);
lean_dec(x_18);
x_21 = lean_nat_dec_le(x_15, x_20);
if (x_21 == 0)
{
lean_object* x_22; 
lean_inc(x_20);
x_22 = l_Array_qsort_sort___at___Lean_mkTagDeclarationExtension_spec__0___redArg(x_17, x_20, x_20);
lean_dec(x_20);
return x_22;
}
else
{
lean_object* x_23; 
x_23 = l_Array_qsort_sort___at___Lean_mkTagDeclarationExtension_spec__0___redArg(x_17, x_15, x_20);
lean_dec(x_20);
return x_23;
}
}
else
{
lean_dec(x_18);
return x_17;
}
}
block_34:
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_array_get_size(x_26);
x_28 = lean_mk_empty_array_with_capacity(x_15);
x_29 = lean_nat_dec_lt(x_15, x_27);
if (x_29 == 0)
{
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_1);
x_16 = x_25;
x_17 = x_28;
goto block_24;
}
else
{
uint8_t x_30; 
x_30 = lean_nat_dec_le(x_27, x_27);
if (x_30 == 0)
{
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_1);
x_16 = x_25;
x_17 = x_28;
goto block_24;
}
else
{
size_t x_31; size_t x_32; lean_object* x_33; 
x_31 = lean_usize_of_nat(x_15);
x_32 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_33 = l_Array_foldlMUnsafe_fold___at___ImportCompletion_computePartialImportCompletions_spec__0(x_1, x_26, x_31, x_32, x_28);
lean_dec(x_26);
x_16 = x_25;
x_17 = x_33;
goto block_24;
}
}
}
block_59:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; size_t x_42; size_t x_43; lean_object* x_44; lean_object* x_45; 
x_36 = lean_unsigned_to_nat(2u);
x_37 = l_Lean_Syntax_getArg(x_1, x_36);
x_38 = l_Lean_Syntax_getArgs(x_37);
lean_dec(x_37);
x_39 = lean_box(0);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_array_size(x_38);
x_43 = lean_usize_of_nat(x_15);
x_44 = l_Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2(x_2, x_38, x_42, x_43, x_41);
lean_dec(x_41);
lean_dec(x_38);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
lean_dec(x_44);
if (lean_obj_tag(x_45) == 0)
{
lean_dec(x_3);
lean_dec(x_1);
goto block_6;
}
else
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
lean_dec(x_45);
if (lean_obj_tag(x_46) == 0)
{
lean_dec(x_3);
lean_dec(x_1);
goto block_6;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; size_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
lean_dec(x_46);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = l_Lean_NameTrie_matchingToArray(lean_box(0), x_3, x_48);
x_51 = lean_array_size(x_50);
x_52 = l_Array_mapMUnsafe_map___at___ImportCompletion_computePartialImportCompletions_spec__4(x_48, x_51, x_43, x_50);
lean_dec(x_48);
x_53 = lean_array_get_size(x_52);
x_54 = lean_mk_empty_array_with_capacity(x_15);
x_55 = lean_nat_dec_lt(x_15, x_53);
if (x_55 == 0)
{
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_49);
x_25 = x_35;
x_26 = x_54;
goto block_34;
}
else
{
uint8_t x_56; 
x_56 = lean_nat_dec_le(x_53, x_53);
if (x_56 == 0)
{
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_49);
x_25 = x_35;
x_26 = x_54;
goto block_34;
}
else
{
size_t x_57; lean_object* x_58; 
x_57 = lean_usize_of_nat(x_53);
lean_dec(x_53);
lean_inc(x_1);
x_58 = l_Array_foldlMUnsafe_fold___at___ImportCompletion_computePartialImportCompletions_spec__5(x_1, x_49, x_52, x_43, x_57, x_54);
lean_dec(x_52);
x_25 = x_35;
x_26 = x_58;
goto block_34;
}
}
}
}
}
block_70:
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_60 = lean_unsigned_to_nat(1u);
x_61 = l_Lean_Syntax_getArg(x_1, x_60);
x_62 = l_Lean_Syntax_isNone(x_61);
if (x_62 == 0)
{
uint8_t x_63; 
lean_inc(x_61);
x_63 = l_Lean_Syntax_matchesNull(x_61, x_60);
if (x_63 == 0)
{
lean_object* x_64; 
lean_dec(x_61);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_64 = lean_mk_empty_array_with_capacity(x_15);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_65 = l_Lean_Syntax_getArg(x_61, x_15);
lean_dec(x_61);
x_66 = lean_mk_string_unchecked("prelude", 7, 7);
x_67 = l_Lean_Name_mkStr4(x_7, x_8, x_9, x_66);
x_68 = l_Lean_Syntax_isOfKind(x_65, x_67);
lean_dec(x_67);
if (x_68 == 0)
{
lean_object* x_69; 
lean_dec(x_3);
lean_dec(x_1);
x_69 = lean_mk_empty_array_with_capacity(x_15);
return x_69;
}
else
{
x_35 = x_60;
goto block_59;
}
}
}
else
{
lean_dec(x_61);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_35 = x_60;
goto block_59;
}
}
}
block_6:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_mk_empty_array_with_capacity(x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___ImportCompletion_computePartialImportCompletions_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at___ImportCompletion_computePartialImportCompletions_spec__0(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2_spec__2___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2_spec__2___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2_spec__2(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_forIn_x27Unsafe_loop___at___ImportCompletion_computePartialImportCompletions_spec__2(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___ImportCompletion_computePartialImportCompletions_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at___ImportCompletion_computePartialImportCompletions_spec__4(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___ImportCompletion_computePartialImportCompletions_spec__5___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Array_foldlMUnsafe_fold___at___ImportCompletion_computePartialImportCompletions_spec__5___lam__0(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___ImportCompletion_computePartialImportCompletions_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_foldlMUnsafe_fold___at___ImportCompletion_computePartialImportCompletions_spec__5(x_1, x_2, x_3, x_7, x_8, x_6);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_ImportCompletion_computePartialImportCompletions___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_ImportCompletion_computePartialImportCompletions(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_ImportCompletion_isImportCompletionRequest(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_14; lean_object* x_15; uint8_t x_20; lean_object* x_21; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l_Lean_FileMap_lspPosToUtf8Pos(x_1, x_4);
x_14 = lean_box(0);
x_20 = lean_unbox(x_14);
x_21 = l_Lean_Syntax_getPos_x3f(x_2, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_unsigned_to_nat(0u);
x_15 = x_22;
goto block_19;
}
else
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
lean_dec(x_21);
x_15 = x_23;
goto block_19;
}
block_13:
{
lean_object* x_7; uint32_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = lean_unsigned_to_nat(32u);
x_8 = l_Char_ofNat(x_7);
x_9 = l_Char_utf8Size(x_8);
x_10 = lean_nat_add(x_6, x_9);
lean_dec(x_6);
x_11 = lean_nat_add(x_10, x_9);
lean_dec(x_9);
lean_dec(x_10);
x_12 = lean_nat_dec_le(x_5, x_11);
lean_dec(x_11);
lean_dec(x_5);
return x_12;
}
block_19:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_14);
x_17 = l_Lean_Syntax_getTailPos_x3f(x_2, x_16);
if (lean_obj_tag(x_17) == 0)
{
x_6 = x_15;
goto block_13;
}
else
{
lean_object* x_18; 
lean_dec(x_15);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
x_6 = x_18;
goto block_13;
}
}
}
}
LEAN_EXPORT lean_object* l_ImportCompletion_isImportCompletionRequest___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_ImportCompletion_isImportCompletionRequest(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_ImportCompletion_collectAvailableImportsFromLake(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_determineLakePath(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_22; lean_object* x_23; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_box(2);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 0, 3);
x_8 = lean_unbox(x_5);
lean_ctor_set_uint8(x_7, 0, x_8);
x_9 = lean_unbox(x_6);
lean_ctor_set_uint8(x_7, 1, x_9);
x_10 = lean_unbox(x_6);
lean_ctor_set_uint8(x_7, 2, x_10);
x_11 = lean_mk_string_unchecked("available-imports", 17, 17);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_mk_empty_array_with_capacity(x_12);
x_14 = lean_array_push(x_13, x_11);
x_15 = lean_box(0);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_mk_empty_array_with_capacity(x_16);
x_18 = lean_box(1);
x_19 = lean_box(0);
lean_inc(x_7);
x_20 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_20, 0, x_7);
lean_ctor_set(x_20, 1, x_3);
lean_ctor_set(x_20, 2, x_14);
lean_ctor_set(x_20, 3, x_15);
lean_ctor_set(x_20, 4, x_17);
x_21 = lean_unbox(x_18);
lean_ctor_set_uint8(x_20, sizeof(void*)*5, x_21);
x_22 = lean_unbox(x_19);
lean_ctor_set_uint8(x_20, sizeof(void*)*5 + 1, x_22);
x_23 = lean_io_process_spawn(x_20, x_4);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
x_27 = l_IO_FS_Handle_readToEnd(x_26, x_25);
lean_dec(x_26);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_27, 1);
x_31 = lean_io_process_child_wait(x_7, x_24, x_30);
lean_dec(x_24);
lean_dec(x_7);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint32_t x_35; uint32_t x_36; uint8_t x_37; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_34 = x_31;
} else {
 lean_dec_ref(x_31);
 x_34 = lean_box(0);
}
x_35 = lean_uint32_of_nat(x_16);
x_36 = lean_unbox_uint32(x_32);
lean_dec(x_32);
x_37 = lean_uint32_dec_eq(x_36, x_35);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
lean_free_object(x_27);
lean_dec(x_29);
x_38 = lean_box(0);
if (lean_is_scalar(x_34)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_34;
}
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_33);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_49; 
x_40 = lean_string_utf8_byte_size(x_29);
x_41 = l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(x_29, x_40, x_16);
x_42 = l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(x_29, x_41, x_40);
x_43 = lean_string_utf8_extract(x_29, x_41, x_42);
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_29);
lean_inc(x_43);
x_49 = l_Lean_Json_parse(x_43);
if (lean_obj_tag(x_49) == 0)
{
lean_dec(x_49);
lean_free_object(x_27);
goto block_48;
}
else
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
lean_dec(x_49);
if (lean_obj_tag(x_50) == 4)
{
lean_object* x_51; size_t x_52; size_t x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
lean_dec(x_50);
x_52 = lean_array_size(x_51);
x_53 = lean_usize_of_nat(x_16);
x_54 = l_Array_mapMUnsafe_map___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonOpenNamespace____x40_Lean_Data_Lsp_Internal___hyg_2624__spec__0(x_52, x_53, x_51);
if (lean_obj_tag(x_54) == 0)
{
lean_dec(x_54);
lean_free_object(x_27);
goto block_48;
}
else
{
uint8_t x_55; 
lean_dec(x_43);
lean_dec(x_34);
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_ctor_set(x_27, 1, x_33);
lean_ctor_set(x_27, 0, x_54);
return x_27;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_54, 0);
lean_inc(x_56);
lean_dec(x_54);
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_27, 1, x_33);
lean_ctor_set(x_27, 0, x_57);
return x_27;
}
}
}
else
{
lean_dec(x_50);
lean_free_object(x_27);
goto block_48;
}
}
block_48:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_mk_string_unchecked("invalid output from `lake available-imports`:\n", 46, 46);
x_45 = lean_string_append(x_44, x_43);
lean_dec(x_43);
x_46 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_46, 0, x_45);
if (lean_is_scalar(x_34)) {
 x_47 = lean_alloc_ctor(1, 2, 0);
} else {
 x_47 = x_34;
 lean_ctor_set_tag(x_47, 1);
}
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_33);
return x_47;
}
}
}
else
{
uint8_t x_58; 
lean_free_object(x_27);
lean_dec(x_29);
x_58 = !lean_is_exclusive(x_31);
if (x_58 == 0)
{
return x_31;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_31, 0);
x_60 = lean_ctor_get(x_31, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_31);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_27, 0);
x_63 = lean_ctor_get(x_27, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_27);
x_64 = lean_io_process_child_wait(x_7, x_24, x_63);
lean_dec(x_24);
lean_dec(x_7);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; uint32_t x_68; uint32_t x_69; uint8_t x_70; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_67 = x_64;
} else {
 lean_dec_ref(x_64);
 x_67 = lean_box(0);
}
x_68 = lean_uint32_of_nat(x_16);
x_69 = lean_unbox_uint32(x_65);
lean_dec(x_65);
x_70 = lean_uint32_dec_eq(x_69, x_68);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; 
lean_dec(x_62);
x_71 = lean_box(0);
if (lean_is_scalar(x_67)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_67;
}
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_66);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_82; 
x_73 = lean_string_utf8_byte_size(x_62);
x_74 = l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(x_62, x_73, x_16);
x_75 = l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(x_62, x_74, x_73);
x_76 = lean_string_utf8_extract(x_62, x_74, x_75);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_62);
lean_inc(x_76);
x_82 = l_Lean_Json_parse(x_76);
if (lean_obj_tag(x_82) == 0)
{
lean_dec(x_82);
goto block_81;
}
else
{
lean_object* x_83; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
lean_dec(x_82);
if (lean_obj_tag(x_83) == 4)
{
lean_object* x_84; size_t x_85; size_t x_86; lean_object* x_87; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
lean_dec(x_83);
x_85 = lean_array_size(x_84);
x_86 = lean_usize_of_nat(x_16);
x_87 = l_Array_mapMUnsafe_map___at_____private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonOpenNamespace____x40_Lean_Data_Lsp_Internal___hyg_2624__spec__0(x_85, x_86, x_84);
if (lean_obj_tag(x_87) == 0)
{
lean_dec(x_87);
goto block_81;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_76);
lean_dec(x_67);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 x_89 = x_87;
} else {
 lean_dec_ref(x_87);
 x_89 = lean_box(0);
}
if (lean_is_scalar(x_89)) {
 x_90 = lean_alloc_ctor(1, 1, 0);
} else {
 x_90 = x_89;
}
lean_ctor_set(x_90, 0, x_88);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_66);
return x_91;
}
}
else
{
lean_dec(x_83);
goto block_81;
}
}
block_81:
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_77 = lean_mk_string_unchecked("invalid output from `lake available-imports`:\n", 46, 46);
x_78 = lean_string_append(x_77, x_76);
lean_dec(x_76);
x_79 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_79, 0, x_78);
if (lean_is_scalar(x_67)) {
 x_80 = lean_alloc_ctor(1, 2, 0);
} else {
 x_80 = x_67;
 lean_ctor_set_tag(x_80, 1);
}
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_66);
return x_80;
}
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_62);
x_92 = lean_ctor_get(x_64, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_64, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_94 = x_64;
} else {
 lean_dec_ref(x_64);
 x_94 = lean_box(0);
}
if (lean_is_scalar(x_94)) {
 x_95 = lean_alloc_ctor(1, 2, 0);
} else {
 x_95 = x_94;
}
lean_ctor_set(x_95, 0, x_92);
lean_ctor_set(x_95, 1, x_93);
return x_95;
}
}
}
else
{
uint8_t x_96; 
lean_dec(x_24);
lean_dec(x_7);
x_96 = !lean_is_exclusive(x_27);
if (x_96 == 0)
{
return x_27;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_27, 0);
x_98 = lean_ctor_get(x_27, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_27);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
else
{
uint8_t x_100; 
lean_dec(x_7);
x_100 = !lean_is_exclusive(x_23);
if (x_100 == 0)
{
return x_23;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_23, 0);
x_102 = lean_ctor_get(x_23, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_23);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
else
{
uint8_t x_104; 
x_104 = !lean_is_exclusive(x_2);
if (x_104 == 0)
{
return x_2;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_2, 0);
x_106 = lean_ctor_get(x_2, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_2);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_forEachModuleInDir___at___ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__0_spec__0___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_Name_append(x_1, x_3);
x_7 = lean_apply_3(x_2, x_6, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_forEachModuleInDir___at___ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_16; 
x_16 = lean_usize_dec_lt(x_4, x_3);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_5);
lean_ctor_set(x_17, 1, x_6);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_7);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
lean_dec(x_5);
x_19 = lean_array_uget(x_2, x_4);
lean_inc(x_19);
x_20 = l_IO_FS_DirEntry_path(x_19);
x_21 = l_System_FilePath_isDir(x_20, x_7);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_box(0);
x_25 = lean_unbox(x_22);
lean_dec(x_22);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = l_System_FilePath_extension(x_20);
x_27 = lean_mk_string_unchecked("lean", 4, 4);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_____private_Lean_Data_Lsp_LanguageFeatures_0__Lean_Lsp_beqCompletionItem____x40_Lean_Data_Lsp_LanguageFeatures___hyg_2497__spec__0(x_26, x_28);
lean_dec(x_28);
lean_dec(x_26);
if (x_29 == 0)
{
lean_dec(x_19);
x_8 = x_24;
x_9 = x_6;
x_10 = x_23;
goto block_15;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_30 = lean_ctor_get(x_19, 1);
lean_inc(x_30);
lean_dec(x_19);
x_31 = lean_mk_string_unchecked("", 0, 0);
x_32 = l_System_FilePath_withExtension(x_30, x_31);
lean_dec(x_31);
x_33 = lean_box(0);
x_34 = l_Lean_Name_str___override(x_33, x_32);
lean_inc(x_1);
x_35 = lean_apply_3(x_1, x_34, x_6, x_23);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_8 = x_24;
x_9 = x_38;
x_10 = x_37;
goto block_15;
}
else
{
lean_dec(x_1);
return x_35;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_19, 1);
lean_inc(x_39);
lean_dec(x_19);
x_40 = lean_box(0);
x_41 = l_Lean_Name_str___override(x_40, x_39);
lean_inc(x_1);
x_42 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_forEachModuleInDir___at___ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__0_spec__0___lam__0), 5, 2);
lean_closure_set(x_42, 0, x_41);
lean_closure_set(x_42, 1, x_1);
x_43 = l_Lean_forEachModuleInDir___at___ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0(x_20, x_42, x_6, x_23);
lean_dec(x_20);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_8 = x_24;
x_9 = x_46;
x_10 = x_45;
goto block_15;
}
else
{
lean_dec(x_1);
return x_43;
}
}
}
block_15:
{
lean_object* x_11; size_t x_12; size_t x_13; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_usize_of_nat(x_11);
x_13 = lean_usize_add(x_4, x_12);
x_4 = x_13;
x_5 = x_8;
x_6 = x_9;
x_7 = x_10;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_forEachModuleInDir___at___ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_16; 
x_16 = lean_usize_dec_lt(x_4, x_3);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_5);
lean_ctor_set(x_17, 1, x_6);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_7);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
lean_dec(x_5);
x_19 = lean_array_uget(x_2, x_4);
lean_inc(x_19);
x_20 = l_IO_FS_DirEntry_path(x_19);
x_21 = l_System_FilePath_isDir(x_20, x_7);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_box(0);
x_25 = lean_unbox(x_22);
lean_dec(x_22);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = l_System_FilePath_extension(x_20);
x_27 = lean_mk_string_unchecked("lean", 4, 4);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_____private_Lean_Data_Lsp_LanguageFeatures_0__Lean_Lsp_beqCompletionItem____x40_Lean_Data_Lsp_LanguageFeatures___hyg_2497__spec__0(x_26, x_28);
lean_dec(x_28);
lean_dec(x_26);
if (x_29 == 0)
{
lean_dec(x_19);
x_8 = x_24;
x_9 = x_6;
x_10 = x_23;
goto block_15;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_30 = lean_ctor_get(x_19, 1);
lean_inc(x_30);
lean_dec(x_19);
x_31 = lean_mk_string_unchecked("", 0, 0);
x_32 = l_System_FilePath_withExtension(x_30, x_31);
lean_dec(x_31);
x_33 = lean_box(0);
x_34 = l_Lean_Name_str___override(x_33, x_32);
lean_inc(x_1);
x_35 = lean_apply_3(x_1, x_34, x_6, x_23);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_8 = x_24;
x_9 = x_38;
x_10 = x_37;
goto block_15;
}
else
{
lean_dec(x_1);
return x_35;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_19, 1);
lean_inc(x_39);
lean_dec(x_19);
x_40 = lean_box(0);
x_41 = l_Lean_Name_str___override(x_40, x_39);
lean_inc(x_1);
x_42 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_forEachModuleInDir___at___ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__0_spec__0___lam__0), 5, 2);
lean_closure_set(x_42, 0, x_41);
lean_closure_set(x_42, 1, x_1);
x_43 = l_Lean_forEachModuleInDir___at___ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0(x_20, x_42, x_6, x_23);
lean_dec(x_20);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_8 = x_24;
x_9 = x_46;
x_10 = x_45;
goto block_15;
}
else
{
lean_dec(x_1);
return x_43;
}
}
}
block_15:
{
lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_usize_of_nat(x_11);
x_13 = lean_usize_add(x_4, x_12);
x_14 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_forEachModuleInDir___at___ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_13, x_8, x_9, x_10);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___at___ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_io_read_dir(x_1, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; lean_object* x_10; size_t x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_box(0);
x_9 = lean_array_size(x_6);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_usize_of_nat(x_10);
x_12 = l_Array_forIn_x27Unsafe_loop___at___Lean_forEachModuleInDir___at___ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__0(x_2, x_6, x_9, x_11, x_8, x_3, x_7);
lean_dec(x_6);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
lean_ctor_set(x_14, 0, x_8);
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_8);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set(x_12, 0, x_18);
return x_12;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_12, 0);
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_12);
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
if (lean_is_scalar(x_22)) {
 x_23 = lean_alloc_ctor(0, 2, 0);
} else {
 x_23 = x_22;
}
lean_ctor_set(x_23, 0, x_8);
lean_ctor_set(x_23, 1, x_21);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_20);
return x_24;
}
}
else
{
return x_12;
}
}
else
{
uint8_t x_25; 
lean_dec(x_3);
lean_dec(x_2);
x_25 = !lean_is_exclusive(x_5);
if (x_25 == 0)
{
return x_5;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_5, 0);
x_27 = lean_ctor_get(x_5, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_5);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__3___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_array_push(x_3, x_2);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
x_9 = l_System_FilePath_isDir(x_7, x_4);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_box(0);
x_13 = lean_unbox(x_10);
lean_dec(x_10);
if (x_13 == 0)
{
x_1 = x_8;
x_2 = x_12;
x_4 = x_11;
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__3___redArg___lam__0), 4, 1);
lean_closure_set(x_15, 0, x_12);
x_16 = l_Lean_forEachModuleInDir___at___ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0(x_7, x_15, x_3, x_11);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_1 = x_8;
x_2 = x_12;
x_3 = x_19;
x_4 = x_18;
goto _start;
}
else
{
return x_16;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_List_forIn_x27_loop___at___ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__3___redArg(x_2, x_3, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_ImportCompletion_collectAvailableImportsFromSrcSearchPath(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_7; 
x_7 = l_Lean_getSrcSearchPath(x_1);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_mk_empty_array_with_capacity(x_10);
x_12 = lean_box(0);
x_13 = l_List_forIn_x27_loop___at___ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__3___redArg(x_8, x_12, x_11, x_9);
lean_dec(x_8);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_14, 0);
lean_dec(x_17);
lean_ctor_set(x_14, 0, x_12);
x_2 = x_14;
x_3 = x_15;
goto block_6;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_18);
x_2 = x_19;
x_3 = x_15;
goto block_6;
}
}
else
{
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_13, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_dec(x_13);
x_2 = x_20;
x_3 = x_21;
goto block_6;
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_13);
if (x_22 == 0)
{
return x_13;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_13, 0);
x_24 = lean_ctor_get(x_13, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_13);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_7);
if (x_26 == 0)
{
return x_7;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_7, 0);
x_28 = lean_ctor_get(x_7, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_7);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
block_6:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_forEachModuleInDir___at___ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_forEachModuleInDir___at___ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__0_spec__0(x_1, x_2, x_8, x_9, x_5, x_6, x_7);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_forEachModuleInDir___at___ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l_Array_forIn_x27Unsafe_loop___at___Lean_forEachModuleInDir___at___ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__0(x_1, x_2, x_8, x_9, x_5, x_6, x_7);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___at___ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_forEachModuleInDir___at___ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_forIn_x27_loop___at___ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__3___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_List_forIn_x27_loop___at___ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_ImportCompletion_collectAvailableImports(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_ImportCompletion_collectAvailableImportsFromLake(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_ImportCompletion_collectAvailableImportsFromSrcSearchPath(x_4);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_2, 0);
lean_dec(x_7);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_dec(x_3);
lean_ctor_set(x_2, 0, x_8);
return x_2;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
lean_dec(x_3);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_2);
if (x_12 == 0)
{
return x_2;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_2);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___ImportCompletion_addCompletionItemData_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_box(0);
x_8 = lean_array_uset(x_4, x_3, x_7);
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_6, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_6, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_6, 3);
lean_inc(x_12);
x_13 = lean_ctor_get(x_6, 4);
lean_inc(x_13);
x_14 = lean_ctor_get(x_6, 5);
lean_inc(x_14);
lean_inc(x_1);
x_15 = l___private_Lean_Server_Completion_CompletionItemData_0__Lean_Lsp_toJsonCompletionItemData____x40_Lean_Server_Completion_CompletionItemData___hyg_82_(x_1);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_ctor_get(x_6, 7);
lean_inc(x_17);
lean_dec(x_6);
x_18 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_18, 0, x_9);
lean_ctor_set(x_18, 1, x_10);
lean_ctor_set(x_18, 2, x_11);
lean_ctor_set(x_18, 3, x_12);
lean_ctor_set(x_18, 4, x_13);
lean_ctor_set(x_18, 5, x_14);
lean_ctor_set(x_18, 6, x_16);
lean_ctor_set(x_18, 7, x_17);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_usize_of_nat(x_19);
x_21 = lean_usize_add(x_3, x_20);
x_22 = lean_array_uset(x_8, x_3, x_18);
x_3 = x_21;
x_4 = x_22;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_ImportCompletion_addCompletionItemData(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; size_t x_5; lean_object* x_6; size_t x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_array_size(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_usize_of_nat(x_6);
x_8 = l_Array_mapMUnsafe_map___at___ImportCompletion_addCompletionItemData_spec__0(x_2, x_5, x_7, x_4);
x_9 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___ImportCompletion_addCompletionItemData_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at___ImportCompletion_addCompletionItemData_spec__0(x_1, x_5, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___ImportCompletion_find_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
x_8 = l_Lean_FileMap_lspPosToUtf8Pos(x_2, x_7);
x_9 = lean_usize_dec_lt(x_5, x_4);
if (x_9 == 0)
{
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
else
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; 
lean_inc(x_1);
x_10 = l_ImportCompletion_isImportCmdCompletionRequest(x_1, x_8);
lean_dec(x_8);
x_11 = lean_box(x_10);
x_12 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at___ImportCompletion_computePartialImportCompletions_spec__5___lam__0___boxed), 2, 1);
lean_closure_set(x_12, 0, x_11);
x_13 = lean_array_uget(x_6, x_5);
x_14 = lean_box(0);
x_15 = lean_array_uset(x_6, x_5, x_14);
x_16 = l_Lean_Name_toString(x_13, x_9, x_12);
x_17 = lean_box(0);
x_18 = lean_box(0);
x_19 = lean_box(0);
x_20 = lean_box(0);
x_21 = lean_box(0);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_23, 0, x_16);
lean_ctor_set(x_23, 1, x_17);
lean_ctor_set(x_23, 2, x_18);
lean_ctor_set(x_23, 3, x_19);
lean_ctor_set(x_23, 4, x_20);
lean_ctor_set(x_23, 5, x_17);
lean_ctor_set(x_23, 6, x_21);
lean_ctor_set(x_23, 7, x_22);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_usize_of_nat(x_24);
x_26 = lean_usize_add(x_5, x_25);
x_27 = lean_array_uset(x_15, x_5, x_23);
x_5 = x_26;
x_6 = x_27;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___ImportCompletion_find_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
x_8 = lean_usize_dec_lt(x_5, x_4);
if (x_8 == 0)
{
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
else
{
lean_object* x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; size_t x_28; size_t x_29; lean_object* x_30; 
x_9 = l_Lean_FileMap_lspPosToUtf8Pos(x_2, x_7);
lean_inc(x_1);
x_10 = l_ImportCompletion_isImportNameCompletionRequest(x_1, x_9);
lean_inc(x_1);
x_11 = l_ImportCompletion_isImportCmdCompletionRequest(x_1, x_9);
lean_dec(x_9);
x_12 = lean_box(x_10);
x_13 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at___ImportCompletion_computePartialImportCompletions_spec__5___lam__0___boxed), 2, 1);
lean_closure_set(x_13, 0, x_12);
x_14 = lean_array_uget(x_6, x_5);
x_15 = lean_box(0);
x_16 = lean_array_uset(x_6, x_5, x_15);
x_17 = lean_mk_string_unchecked("import ", 7, 7);
x_18 = l_Lean_Name_toString(x_14, x_11, x_13);
x_19 = lean_string_append(x_17, x_18);
lean_dec(x_18);
x_20 = lean_box(0);
x_21 = lean_box(0);
x_22 = lean_box(0);
x_23 = lean_box(0);
x_24 = lean_box(0);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_26, 0, x_19);
lean_ctor_set(x_26, 1, x_20);
lean_ctor_set(x_26, 2, x_21);
lean_ctor_set(x_26, 3, x_22);
lean_ctor_set(x_26, 4, x_23);
lean_ctor_set(x_26, 5, x_20);
lean_ctor_set(x_26, 6, x_24);
lean_ctor_set(x_26, 7, x_25);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_usize_of_nat(x_27);
x_29 = lean_usize_add(x_5, x_28);
x_30 = lean_array_uset(x_16, x_5, x_26);
x_5 = x_29;
x_6 = x_30;
goto _start;
}
}
}
LEAN_EXPORT uint8_t l_Array_mapMUnsafe_map___at___ImportCompletion_find_spec__2___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___ImportCompletion_find_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
x_8 = lean_usize_dec_lt(x_5, x_4);
if (x_8 == 0)
{
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; lean_object* x_26; 
x_9 = l_Lean_FileMap_lspPosToUtf8Pos(x_2, x_7);
x_10 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at___ImportCompletion_find_spec__2___lam__0___boxed), 1, 0);
lean_inc(x_1);
x_11 = l_ImportCompletion_isImportNameCompletionRequest(x_1, x_9);
lean_dec(x_9);
x_12 = lean_array_uget(x_6, x_5);
x_13 = lean_box(0);
x_14 = lean_array_uset(x_6, x_5, x_13);
x_15 = l_Lean_Name_toString(x_12, x_11, x_10);
x_16 = lean_box(0);
x_17 = lean_box(0);
x_18 = lean_box(0);
x_19 = lean_box(0);
x_20 = lean_box(0);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_22, 0, x_15);
lean_ctor_set(x_22, 1, x_16);
lean_ctor_set(x_22, 2, x_17);
lean_ctor_set(x_22, 3, x_18);
lean_ctor_set(x_22, 4, x_19);
lean_ctor_set(x_22, 5, x_16);
lean_ctor_set(x_22, 6, x_20);
lean_ctor_set(x_22, 7, x_21);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_usize_of_nat(x_23);
x_25 = lean_usize_add(x_5, x_24);
x_26 = lean_array_uset(x_14, x_5, x_22);
x_5 = x_25;
x_6 = x_26;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_ImportCompletion_find(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = l_ImportCompletion_AvailableImports_toImportTrie(x_4);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
x_7 = l_Lean_FileMap_lspPosToUtf8Pos(x_1, x_6);
lean_inc(x_2);
x_8 = l_ImportCompletion_isImportNameCompletionRequest(x_2, x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_inc(x_2);
x_9 = l_ImportCompletion_isImportCmdCompletionRequest(x_2, x_7);
if (x_9 == 0)
{
lean_object* x_10; size_t x_11; lean_object* x_12; size_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_inc(x_2);
x_10 = l_ImportCompletion_computePartialImportCompletions(x_2, x_7, x_5);
lean_dec(x_7);
x_11 = lean_array_size(x_10);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_usize_of_nat(x_12);
lean_inc(x_3);
x_14 = l_Array_mapMUnsafe_map___at___ImportCompletion_find_spec__0(x_2, x_1, x_3, x_11, x_13, x_10);
x_15 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set_uint8(x_15, sizeof(void*)*1, x_9);
x_16 = l_ImportCompletion_addCompletionItemData(x_15, x_3);
return x_16;
}
else
{
lean_object* x_17; size_t x_18; lean_object* x_19; size_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_7);
x_17 = l_Lean_NameTrie_toArray___redArg(x_5);
x_18 = lean_array_size(x_17);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_usize_of_nat(x_19);
lean_inc(x_3);
x_21 = l_Array_mapMUnsafe_map___at___ImportCompletion_find_spec__1(x_2, x_1, x_3, x_18, x_20, x_17);
x_22 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set_uint8(x_22, sizeof(void*)*1, x_8);
x_23 = l_ImportCompletion_addCompletionItemData(x_22, x_3);
return x_23;
}
}
else
{
lean_object* x_24; size_t x_25; lean_object* x_26; size_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; 
lean_dec(x_7);
x_24 = l_Lean_NameTrie_toArray___redArg(x_5);
x_25 = lean_array_size(x_24);
x_26 = lean_unsigned_to_nat(0u);
x_27 = lean_usize_of_nat(x_26);
lean_inc(x_3);
x_28 = l_Array_mapMUnsafe_map___at___ImportCompletion_find_spec__2(x_2, x_1, x_3, x_25, x_27, x_24);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_30, 0, x_28);
x_31 = lean_unbox(x_29);
lean_ctor_set_uint8(x_30, sizeof(void*)*1, x_31);
x_32 = l_ImportCompletion_addCompletionItemData(x_30, x_3);
return x_32;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___ImportCompletion_find_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_mapMUnsafe_map___at___ImportCompletion_find_spec__0(x_1, x_2, x_3, x_7, x_8, x_6);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___ImportCompletion_find_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_mapMUnsafe_map___at___ImportCompletion_find_spec__1(x_1, x_2, x_3, x_7, x_8, x_6);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___ImportCompletion_find_spec__2___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Array_mapMUnsafe_map___at___ImportCompletion_find_spec__2___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___ImportCompletion_find_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_mapMUnsafe_map___at___ImportCompletion_find_spec__2(x_1, x_2, x_3, x_7, x_8, x_6);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_ImportCompletion_find___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_ImportCompletion_find(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_ImportCompletion_computeCompletions(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_ImportCompletion_collectAvailableImports(x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_3);
x_8 = l_ImportCompletion_find(x_1, x_2, x_3, x_7);
lean_dec(x_7);
x_9 = l_ImportCompletion_addCompletionItemData(x_8, x_3);
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
lean_inc(x_3);
x_12 = l_ImportCompletion_find(x_1, x_2, x_3, x_10);
lean_dec(x_10);
x_13 = l_ImportCompletion_addCompletionItemData(x_12, x_3);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
}
else
{
uint8_t x_15; 
lean_dec(x_3);
lean_dec(x_2);
x_15 = !lean_is_exclusive(x_5);
if (x_15 == 0)
{
return x_5;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_5, 0);
x_17 = lean_ctor_get(x_5, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_5);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_ImportCompletion_computeCompletions___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_ImportCompletion_computeCompletions(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* initialize_Lean_Data_NameTrie(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_Paths(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_LakePath(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Server_Completion_CompletionItemData(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Parser_Module(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Server_Completion_ImportCompletion(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_NameTrie(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_Paths(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_LakePath(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_Completion_CompletionItemData(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Module(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
