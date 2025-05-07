// Lean compiler output
// Module: Lean.Server.CodeActions.UnknownIdentifier
// Imports: Lean.Server.FileWorker.Utils Lean.Data.Lsp.Internal Lean.Server.Requests Lean.Server.Completion.CompletionInfoSelection Lean.Server.CodeActions.Basic Lean.Server.Completion.CompletionUtils
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
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__1_spec__1___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeIdQuery_x3f___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FileMap_utf8RangeToLspRange(lean_object*, lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__0_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_Lean_Language_SnapshotTree_collectMessagesInRange(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Server_FileWorker_computeDotQuery_x3f_spec__0(size_t, size_t, lean_object*);
lean_object* l___private_Lean_Language_Lean_Types_0__Lean_Language_Lean_pushOpt___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_Server_FileWorker_collectOpenNamespaces_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___lam__0(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_sendServerRequest___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_computeFallbackQuery_x3f___lam__1(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_importAllUnknownIdentifiersProvider;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_collectOpenNamespaces(lean_object*, lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_sendServerRequest___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeDotQuery_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_ServerTask_mapCheap___redArg(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Std_Data_DHashMap_Internal_RawLemmas_0__Std_DHashMap_Internal_Raw_u2080_modifyMap_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_waitUnknownIdentifierRanges(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanQueryModuleResponse____x40_Lean_Data_Lsp_Internal___hyg_3516_(lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lean_Server_RequestM_checkCancelled(lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_____private_Std_Data_DHashMap_Internal_RawLemmas_0__Std_DHashMap_Internal_Raw_u2080_modifyMap_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_Lean_Elab_InfoTree_smallestInfo_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__5_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeQuery_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__5(lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageLog_reportedPlusUnreported(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__3_spec__3___redArg(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_Lean_FileMap_ofPosition(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanQueryModuleParams____x40_Lean_Data_Lsp_Internal___hyg_3207_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeFallbackQuery_x3f___lam__1___boxed(lean_object*);
lean_object* l_Lean_Server_RequestCancellationToken_requestCancellationTask(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeIdQuery_x3f___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_toJsonCodeActionResolveData____x40_Lean_Server_CodeActions_Basic___hyg_59_(lean_object*);
uint8_t l_String_Range_overlaps(lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeDotIdQuery_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* l_Lean_Lsp_WorkspaceEdit_ofTextDocumentEdit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeFallbackQuery_x3f___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__3(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeFallbackQuery_x3f___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_getPrefix(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_RequestM_findCmdDataAtPos(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeQuery_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeQuery_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_sendServerRequest___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_FileMap_utf8PosToLspPos(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__3_spec__3___redArg___lam__0(uint8_t, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeFallbackQuery_x3f___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeDotIdQuery_x3f___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__3_spec__3(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__4(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* lean_task_get_own(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__4___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeFallbackQuery_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeDotQuery_x3f___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Server_FileWorker_computeDotQuery_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeIdQuery_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Environment_mainModule(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go(lean_object*);
lean_object* l_Lean_Server_ServerTask_waitAny___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_importAllUnknownIdentifiersCodeAction(lean_object*, lean_object*);
uint64_t l_Lean_Name_hash___override(lean_object*);
LEAN_EXPORT uint8_t l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__4___redArg___lam__0(uint8_t, lean_object*);
lean_object* l_Array_append(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Server_FileWorker_collectOpenNamespaces_spec__0(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Server_FileWorker_EditableDocument_versionedIdentifier(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_computeFallbackQuery_x3f___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__4(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Info_range_x3f(lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
lean_object* l_Lean_Name_getString_x21(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__5_spec__5(lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Lean_Server_Completion_findPrioritizedCompletionPartitionsAt(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_sendServerRequest___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__3___redArg___lam__0(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Server_Completion_getDotCompletionTypeNames(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Language_SnapshotTask_map___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeDotIdQuery_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__0_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__1_spec__1___lam__0(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeDotIdQuery_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Server_Completion_minimizeGlobalIdentifierInContext(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__1_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeDotQuery_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Server_RequestError_ofIoError(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__4_spec__4(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__3_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeIdQuery_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__4___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__3_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_6, x_5);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_array_uget(x_4, x_6);
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_dec(x_7);
lean_inc(x_12);
x_13 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0(x_1, x_2, x_3, x_11, x_12, x_8);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_13, 0);
lean_dec(x_16);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_14);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_12);
lean_ctor_set(x_13, 0, x_18);
return x_13;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_dec(x_13);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_14);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_12);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; size_t x_28; size_t x_29; 
lean_dec(x_12);
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_23);
lean_dec(x_13);
x_24 = lean_ctor_get(x_14, 0);
lean_inc(x_24);
lean_dec(x_14);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_usize_of_nat(x_27);
x_29 = lean_usize_add(x_6, x_28);
x_6 = x_29;
x_7 = x_26;
x_8 = x_23;
goto _start;
}
}
}
}
LEAN_EXPORT uint8_t l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__1_spec__1___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_unknownIdentifierMessageTag;
x_3 = lean_name_eq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_usize_dec_lt(x_5, x_4);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_11 = lean_box(0);
x_20 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__1_spec__1___lam__0___boxed), 1, 0);
x_21 = lean_array_uget(x_3, x_5);
x_22 = lean_ctor_get(x_6, 1);
lean_inc(x_22);
lean_dec(x_6);
x_23 = lean_ctor_get(x_21, 4);
lean_inc(x_23);
x_24 = l_Lean_MessageData_hasTag(x_20, x_23);
if (x_24 == 0)
{
lean_dec(x_21);
x_12 = x_22;
x_13 = x_7;
goto block_19;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_35; 
x_25 = lean_ctor_get(x_8, 0);
x_26 = lean_ctor_get(x_25, 3);
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
lean_inc(x_27);
x_28 = l_Lean_FileMap_ofPosition(x_26, x_27);
x_35 = lean_ctor_get(x_21, 2);
lean_inc(x_35);
lean_dec(x_21);
if (lean_obj_tag(x_35) == 0)
{
x_29 = x_27;
goto block_34;
}
else
{
lean_object* x_36; 
lean_dec(x_27);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec(x_35);
x_29 = x_36;
goto block_34;
}
block_34:
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = l_Lean_FileMap_ofPosition(x_26, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_String_Range_overlaps(x_31, x_2, x_24, x_24);
if (x_32 == 0)
{
lean_dec(x_31);
x_12 = x_22;
x_13 = x_7;
goto block_19;
}
else
{
lean_object* x_33; 
x_33 = lean_array_push(x_22, x_31);
x_12 = x_33;
x_13 = x_7;
goto block_19;
}
}
}
block_19:
{
lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; 
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_usize_of_nat(x_15);
x_17 = lean_usize_add(x_5, x_16);
x_5 = x_17;
x_6 = x_14;
x_7 = x_13;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_usize_dec_lt(x_5, x_4);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_11 = lean_box(0);
x_20 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__1_spec__1___lam__0___boxed), 1, 0);
x_21 = lean_array_uget(x_3, x_5);
x_22 = lean_ctor_get(x_6, 1);
lean_inc(x_22);
lean_dec(x_6);
x_23 = lean_ctor_get(x_21, 4);
lean_inc(x_23);
x_24 = l_Lean_MessageData_hasTag(x_20, x_23);
if (x_24 == 0)
{
lean_dec(x_21);
x_12 = x_22;
x_13 = x_7;
goto block_19;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_35; 
x_25 = lean_ctor_get(x_8, 0);
x_26 = lean_ctor_get(x_25, 3);
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
lean_inc(x_27);
x_28 = l_Lean_FileMap_ofPosition(x_26, x_27);
x_35 = lean_ctor_get(x_21, 2);
lean_inc(x_35);
lean_dec(x_21);
if (lean_obj_tag(x_35) == 0)
{
x_29 = x_27;
goto block_34;
}
else
{
lean_object* x_36; 
lean_dec(x_27);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec(x_35);
x_29 = x_36;
goto block_34;
}
block_34:
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = l_Lean_FileMap_ofPosition(x_26, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_String_Range_overlaps(x_31, x_2, x_24, x_24);
if (x_32 == 0)
{
lean_dec(x_31);
x_12 = x_22;
x_13 = x_7;
goto block_19;
}
else
{
lean_object* x_33; 
x_33 = lean_array_push(x_22, x_31);
x_12 = x_33;
x_13 = x_7;
goto block_19;
}
}
}
block_19:
{
lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_usize_of_nat(x_15);
x_17 = lean_usize_add(x_5, x_16);
x_18 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__1_spec__1(x_1, x_2, x_3, x_4, x_17, x_14, x_13);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; lean_object* x_12; size_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_5);
x_11 = lean_array_size(x_8);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_usize_of_nat(x_12);
x_14 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_8, x_11, x_13, x_10, x_6);
lean_dec(x_8);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_14, 0);
lean_dec(x_18);
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_dec(x_15);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_19);
lean_ctor_set(x_14, 0, x_4);
return x_14;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_dec(x_14);
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_dec(x_15);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_21);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_4);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_15);
lean_free_object(x_4);
x_23 = !lean_is_exclusive(x_14);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_14, 0);
lean_dec(x_24);
x_25 = lean_ctor_get(x_16, 0);
lean_inc(x_25);
lean_dec(x_16);
lean_ctor_set(x_14, 0, x_25);
return x_14;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_14, 1);
lean_inc(x_26);
lean_dec(x_14);
x_27 = lean_ctor_get(x_16, 0);
lean_inc(x_27);
lean_dec(x_16);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; size_t x_32; lean_object* x_33; size_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_29 = lean_ctor_get(x_4, 0);
lean_inc(x_29);
lean_dec(x_4);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_5);
x_32 = lean_array_size(x_29);
x_33 = lean_unsigned_to_nat(0u);
x_34 = lean_usize_of_nat(x_33);
x_35 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_29, x_32, x_34, x_31, x_6);
lean_dec(x_29);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_39 = x_35;
} else {
 lean_dec_ref(x_35);
 x_39 = lean_box(0);
}
x_40 = lean_ctor_get(x_36, 1);
lean_inc(x_40);
lean_dec(x_36);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
if (lean_is_scalar(x_39)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_39;
}
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_38);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_36);
x_43 = lean_ctor_get(x_35, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_44 = x_35;
} else {
 lean_dec_ref(x_35);
 x_44 = lean_box(0);
}
x_45 = lean_ctor_get(x_37, 0);
lean_inc(x_45);
lean_dec(x_37);
if (lean_is_scalar(x_44)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_44;
}
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_43);
return x_46;
}
}
}
else
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_4);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; size_t x_51; lean_object* x_52; size_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_48 = lean_ctor_get(x_4, 0);
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_5);
x_51 = lean_array_size(x_48);
x_52 = lean_unsigned_to_nat(0u);
x_53 = lean_usize_of_nat(x_52);
x_54 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__1(x_1, x_2, x_48, x_51, x_53, x_50, x_6);
lean_dec(x_48);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
if (lean_obj_tag(x_56) == 0)
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_54);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_54, 0);
lean_dec(x_58);
x_59 = lean_ctor_get(x_55, 1);
lean_inc(x_59);
lean_dec(x_55);
lean_ctor_set(x_4, 0, x_59);
lean_ctor_set(x_54, 0, x_4);
return x_54;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_54, 1);
lean_inc(x_60);
lean_dec(x_54);
x_61 = lean_ctor_get(x_55, 1);
lean_inc(x_61);
lean_dec(x_55);
lean_ctor_set(x_4, 0, x_61);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_4);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
}
else
{
uint8_t x_63; 
lean_dec(x_55);
lean_free_object(x_4);
x_63 = !lean_is_exclusive(x_54);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_54, 0);
lean_dec(x_64);
x_65 = lean_ctor_get(x_56, 0);
lean_inc(x_65);
lean_dec(x_56);
lean_ctor_set(x_54, 0, x_65);
return x_54;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_54, 1);
lean_inc(x_66);
lean_dec(x_54);
x_67 = lean_ctor_get(x_56, 0);
lean_inc(x_67);
lean_dec(x_56);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; size_t x_72; lean_object* x_73; size_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_69 = lean_ctor_get(x_4, 0);
lean_inc(x_69);
lean_dec(x_4);
x_70 = lean_box(0);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_5);
x_72 = lean_array_size(x_69);
x_73 = lean_unsigned_to_nat(0u);
x_74 = lean_usize_of_nat(x_73);
x_75 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__1(x_1, x_2, x_69, x_72, x_74, x_71, x_6);
lean_dec(x_69);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_78 = lean_ctor_get(x_75, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_79 = x_75;
} else {
 lean_dec_ref(x_75);
 x_79 = lean_box(0);
}
x_80 = lean_ctor_get(x_76, 1);
lean_inc(x_80);
lean_dec(x_76);
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_80);
if (lean_is_scalar(x_79)) {
 x_82 = lean_alloc_ctor(0, 2, 0);
} else {
 x_82 = x_79;
}
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_78);
return x_82;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_76);
x_83 = lean_ctor_get(x_75, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_84 = x_75;
} else {
 lean_dec_ref(x_75);
 x_84 = lean_box(0);
}
x_85 = lean_ctor_get(x_77, 0);
lean_inc(x_85);
lean_dec(x_77);
if (lean_is_scalar(x_84)) {
 x_86 = lean_alloc_ctor(0, 2, 0);
} else {
 x_86 = x_84;
}
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_83);
return x_86;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__4_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_usize_dec_lt(x_5, x_4);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_11 = lean_box(0);
x_20 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__1_spec__1___lam__0___boxed), 1, 0);
x_21 = lean_array_uget(x_3, x_5);
x_22 = lean_ctor_get(x_6, 1);
lean_inc(x_22);
lean_dec(x_6);
x_23 = lean_ctor_get(x_21, 4);
lean_inc(x_23);
x_24 = l_Lean_MessageData_hasTag(x_20, x_23);
if (x_24 == 0)
{
lean_dec(x_21);
x_12 = x_22;
x_13 = x_7;
goto block_19;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_35; 
x_25 = lean_ctor_get(x_8, 0);
x_26 = lean_ctor_get(x_25, 3);
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
lean_inc(x_27);
x_28 = l_Lean_FileMap_ofPosition(x_26, x_27);
x_35 = lean_ctor_get(x_21, 2);
lean_inc(x_35);
lean_dec(x_21);
if (lean_obj_tag(x_35) == 0)
{
x_29 = x_27;
goto block_34;
}
else
{
lean_object* x_36; 
lean_dec(x_27);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec(x_35);
x_29 = x_36;
goto block_34;
}
block_34:
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = l_Lean_FileMap_ofPosition(x_26, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_String_Range_overlaps(x_31, x_2, x_24, x_24);
if (x_32 == 0)
{
lean_dec(x_31);
x_12 = x_22;
x_13 = x_7;
goto block_19;
}
else
{
lean_object* x_33; 
x_33 = lean_array_push(x_22, x_31);
x_12 = x_33;
x_13 = x_7;
goto block_19;
}
}
}
block_19:
{
lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; 
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_usize_of_nat(x_15);
x_17 = lean_usize_add(x_5, x_16);
x_5 = x_17;
x_6 = x_14;
x_7 = x_13;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_usize_dec_lt(x_5, x_4);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_11 = lean_box(0);
x_20 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__1_spec__1___lam__0___boxed), 1, 0);
x_21 = lean_array_uget(x_3, x_5);
x_22 = lean_ctor_get(x_6, 1);
lean_inc(x_22);
lean_dec(x_6);
x_23 = lean_ctor_get(x_21, 4);
lean_inc(x_23);
x_24 = l_Lean_MessageData_hasTag(x_20, x_23);
if (x_24 == 0)
{
lean_dec(x_21);
x_12 = x_22;
x_13 = x_7;
goto block_19;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_35; 
x_25 = lean_ctor_get(x_8, 0);
x_26 = lean_ctor_get(x_25, 3);
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
lean_inc(x_27);
x_28 = l_Lean_FileMap_ofPosition(x_26, x_27);
x_35 = lean_ctor_get(x_21, 2);
lean_inc(x_35);
lean_dec(x_21);
if (lean_obj_tag(x_35) == 0)
{
x_29 = x_27;
goto block_34;
}
else
{
lean_object* x_36; 
lean_dec(x_27);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec(x_35);
x_29 = x_36;
goto block_34;
}
block_34:
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = l_Lean_FileMap_ofPosition(x_26, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_String_Range_overlaps(x_31, x_2, x_24, x_24);
if (x_32 == 0)
{
lean_dec(x_31);
x_12 = x_22;
x_13 = x_7;
goto block_19;
}
else
{
lean_object* x_33; 
x_33 = lean_array_push(x_22, x_31);
x_12 = x_33;
x_13 = x_7;
goto block_19;
}
}
}
block_19:
{
lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_usize_of_nat(x_15);
x_17 = lean_usize_add(x_5, x_16);
x_18 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__4_spec__4(x_1, x_2, x_3, x_4, x_17, x_14, x_13);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
lean_inc(x_4);
x_7 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0(x_1, x_2, x_4, x_6, x_4, x_5);
lean_dec(x_4);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
lean_dec(x_3);
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_7, 0);
lean_dec(x_10);
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
lean_dec(x_8);
lean_ctor_set(x_7, 0, x_11);
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_ctor_get(x_8, 0);
lean_inc(x_13);
lean_dec(x_8);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; lean_object* x_21; size_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_15 = lean_ctor_get(x_7, 1);
lean_inc(x_15);
lean_dec(x_7);
x_16 = lean_ctor_get(x_8, 0);
lean_inc(x_16);
lean_dec(x_8);
x_17 = lean_ctor_get(x_3, 1);
lean_inc(x_17);
lean_dec(x_3);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_16);
x_20 = lean_array_size(x_17);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_usize_of_nat(x_21);
x_23 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__4(x_1, x_2, x_17, x_20, x_22, x_19, x_15);
lean_dec(x_17);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_23);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_23, 0);
lean_dec(x_27);
x_28 = lean_ctor_get(x_24, 1);
lean_inc(x_28);
lean_dec(x_24);
lean_ctor_set(x_23, 0, x_28);
return x_23;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_23, 1);
lean_inc(x_29);
lean_dec(x_23);
x_30 = lean_ctor_get(x_24, 1);
lean_inc(x_30);
lean_dec(x_24);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
uint8_t x_32; 
lean_dec(x_24);
x_32 = !lean_is_exclusive(x_23);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_23, 0);
lean_dec(x_33);
x_34 = lean_ctor_get(x_25, 0);
lean_inc(x_34);
lean_dec(x_25);
lean_ctor_set(x_23, 0, x_34);
return x_23;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_23, 1);
lean_inc(x_35);
lean_dec(x_23);
x_36 = lean_ctor_get(x_25, 0);
lean_inc(x_36);
lean_dec(x_25);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_9; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec(x_1);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_box(0);
x_3 = x_10;
goto block_8;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_alloc_closure((void*)(l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go), 1, 0);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
x_17 = lean_box(1);
x_18 = lean_unbox(x_17);
x_19 = l_Lean_Language_SnapshotTask_map___redArg(x_13, x_14, x_15, x_16, x_18);
lean_ctor_set(x_9, 0, x_19);
x_3 = x_9;
goto block_8;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; 
x_20 = lean_ctor_get(x_9, 0);
lean_inc(x_20);
lean_dec(x_9);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go), 1, 0);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
x_25 = lean_box(1);
x_26 = lean_unbox(x_25);
x_27 = l_Lean_Language_SnapshotTask_map___redArg(x_21, x_22, x_23, x_24, x_26);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_3 = x_28;
goto block_8;
}
}
block_8:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_mk_empty_array_with_capacity(x_4);
x_6 = l___private_Lean_Language_Lean_Types_0__Lean_Language_Lean_pushOpt___redArg(x_3, x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_waitUnknownIdentifierRanges(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_17; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_17 = lean_ctor_get(x_5, 3);
lean_inc(x_17);
lean_dec(x_5);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_box(0);
x_7 = x_18;
goto block_16;
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_20 = lean_ctor_get(x_17, 0);
x_21 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___lam__0), 1, 0);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
x_25 = lean_box(1);
x_26 = lean_unbox(x_25);
x_27 = l_Lean_Language_SnapshotTask_map___redArg(x_22, x_21, x_23, x_24, x_26);
lean_ctor_set(x_17, 0, x_27);
x_7 = x_17;
goto block_16;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; 
x_28 = lean_ctor_get(x_17, 0);
lean_inc(x_28);
lean_dec(x_17);
x_29 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___lam__0), 1, 0);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
x_33 = lean_box(1);
x_34 = lean_unbox(x_33);
x_35 = l_Lean_Language_SnapshotTask_map___redArg(x_30, x_29, x_31, x_32, x_34);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_7 = x_36;
goto block_16;
}
}
block_16:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_mk_empty_array_with_capacity(x_8);
lean_inc(x_9);
x_10 = l___private_Lean_Language_Lean_Types_0__Lean_Language_Lean_pushOpt___redArg(x_7, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_10);
lean_inc(x_2);
x_12 = l_Lean_Language_SnapshotTree_collectMessagesInRange(x_11, x_2);
x_13 = lean_task_get_own(x_12);
x_14 = l_Lean_MessageLog_reportedPlusUnreported(x_13);
x_15 = l_Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0(x_1, x_2, x_14, x_9, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_10 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_11 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_4, x_9, x_10, x_7, x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__1_spec__1___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__1_spec__1___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_10 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__1_spec__1(x_1, x_2, x_3, x_8, x_9, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_10 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__1(x_1, x_2, x_3, x_8, x_9, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__4_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_10 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__4_spec__4(x_1, x_2, x_3, x_8, x_9, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_10 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__4(x_1, x_2, x_3, x_8, x_9, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentArray_forIn___at___Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Server_FileWorker_collectOpenNamespaces_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_Name_isAnonymous(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_mk_empty_array_with_capacity(x_5);
lean_inc(x_2);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_array_push(x_3, x_7);
x_9 = l_Lean_Name_getPrefix(x_2);
lean_dec(x_2);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_1 = x_10;
goto _start;
}
else
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_3);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_Server_FileWorker_collectOpenNamespaces_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_6 = x_1;
} else {
 lean_dec_ref(x_1);
 x_6 = lean_box(0);
}
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_4, 1);
x_13 = lean_array_mk(x_12);
lean_ctor_set(x_4, 1, x_13);
x_7 = x_4;
goto block_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_4, 0);
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_4);
x_16 = lean_array_mk(x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
x_7 = x_17;
goto block_10;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_4);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_4, 0);
x_20 = lean_ctor_get(x_4, 1);
lean_ctor_set(x_4, 1, x_19);
lean_ctor_set(x_4, 0, x_20);
x_7 = x_4;
goto block_10;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_4, 0);
x_22 = lean_ctor_get(x_4, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_4);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_7 = x_23;
goto block_10;
}
}
block_10:
{
lean_object* x_8; 
if (lean_is_scalar(x_6)) {
 x_8 = lean_alloc_ctor(1, 2, 0);
} else {
 x_8 = x_6;
}
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_2);
x_1 = x_5;
x_2 = x_8;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_collectOpenNamespaces(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_mk_empty_array_with_capacity(x_3);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
x_6 = l_Lean_Loop_forIn_loop___at___Lean_Server_FileWorker_collectOpenNamespaces_spec__0(x_5);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_box(0);
x_9 = l_List_mapTR_loop___at___Lean_Server_FileWorker_collectOpenNamespaces_spec__1(x_2, x_8);
x_10 = lean_array_mk(x_9);
x_11 = l_Array_append(lean_box(0), x_7, x_10);
lean_dec(x_10);
return x_11;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_computeFallbackQuery_x3f___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Info_range_x3f(x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_box(0);
x_5 = lean_unbox(x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_box(1);
x_8 = lean_unbox(x_7);
x_9 = lean_unbox(x_7);
x_10 = l_String_Range_overlaps(x_6, x_1, x_8, x_9);
lean_dec(x_6);
return x_10;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_computeFallbackQuery_x3f___lam__1(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeFallbackQuery_x3f___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = l_Lean_Server_Completion_minimizeGlobalIdentifierInContext(x_1, x_2, x_6);
x_8 = l_Lean_FileMap_utf8RangeToLspRange(x_3, x_4);
x_9 = lean_box(1);
x_10 = lean_unbox(x_9);
lean_inc(x_7);
x_11 = l_Lean_Name_toString(x_7, x_10, x_5);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_11);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeFallbackQuery_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_computeFallbackQuery_x3f___lam__0___boxed), 2, 1);
lean_closure_set(x_5, 0, x_2);
x_6 = l_Lean_Elab_InfoTree_smallestInfo_x3f(x_5, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_1);
x_7 = lean_box(0);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_6, 0);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
lean_dec(x_12);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_computeFallbackQuery_x3f___lam__1___boxed), 1, 0);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_15, 3);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_3, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_3, 1);
lean_inc(x_19);
x_20 = lean_string_utf8_extract(x_17, x_18, x_19);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
x_21 = lean_ctor_get(x_11, 0);
lean_inc(x_21);
lean_dec(x_11);
x_22 = lean_ctor_get(x_21, 4);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 5);
lean_inc(x_23);
lean_inc(x_23);
lean_inc(x_22);
x_24 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_computeFallbackQuery_x3f___lam__2___boxed), 6, 5);
lean_closure_set(x_24, 0, x_22);
lean_closure_set(x_24, 1, x_23);
lean_closure_set(x_24, 2, x_16);
lean_closure_set(x_24, 3, x_3);
lean_closure_set(x_24, 4, x_14);
x_25 = l_Lean_Server_FileWorker_collectOpenNamespaces(x_22, x_23);
lean_ctor_set(x_9, 1, x_25);
lean_ctor_set(x_9, 0, x_20);
x_26 = lean_ctor_get(x_21, 0);
lean_inc(x_26);
lean_dec(x_21);
x_27 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_27, 0, x_9);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set(x_27, 2, x_24);
lean_ctor_set(x_6, 0, x_27);
return x_6;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_28 = lean_ctor_get(x_9, 0);
lean_inc(x_28);
lean_dec(x_9);
x_29 = lean_ctor_get(x_1, 0);
lean_inc(x_29);
lean_dec(x_1);
x_30 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_computeFallbackQuery_x3f___lam__1___boxed), 1, 0);
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_ctor_get(x_31, 3);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_3, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_3, 1);
lean_inc(x_35);
x_36 = lean_string_utf8_extract(x_33, x_34, x_35);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
x_37 = lean_ctor_get(x_28, 0);
lean_inc(x_37);
lean_dec(x_28);
x_38 = lean_ctor_get(x_37, 4);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 5);
lean_inc(x_39);
lean_inc(x_39);
lean_inc(x_38);
x_40 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_computeFallbackQuery_x3f___lam__2___boxed), 6, 5);
lean_closure_set(x_40, 0, x_38);
lean_closure_set(x_40, 1, x_39);
lean_closure_set(x_40, 2, x_32);
lean_closure_set(x_40, 3, x_3);
lean_closure_set(x_40, 4, x_30);
x_41 = l_Lean_Server_FileWorker_collectOpenNamespaces(x_38, x_39);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_36);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_ctor_get(x_37, 0);
lean_inc(x_43);
lean_dec(x_37);
x_44 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
lean_ctor_set(x_44, 2, x_40);
lean_ctor_set(x_6, 0, x_44);
return x_6;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_45 = lean_ctor_get(x_6, 0);
lean_inc(x_45);
lean_dec(x_6);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_47 = x_45;
} else {
 lean_dec_ref(x_45);
 x_47 = lean_box(0);
}
x_48 = lean_ctor_get(x_1, 0);
lean_inc(x_48);
lean_dec(x_1);
x_49 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_computeFallbackQuery_x3f___lam__1___boxed), 1, 0);
x_50 = lean_ctor_get(x_48, 0);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_ctor_get(x_50, 3);
lean_inc(x_51);
lean_dec(x_50);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_3, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_3, 1);
lean_inc(x_54);
x_55 = lean_string_utf8_extract(x_52, x_53, x_54);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
x_56 = lean_ctor_get(x_46, 0);
lean_inc(x_56);
lean_dec(x_46);
x_57 = lean_ctor_get(x_56, 4);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 5);
lean_inc(x_58);
lean_inc(x_58);
lean_inc(x_57);
x_59 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_computeFallbackQuery_x3f___lam__2___boxed), 6, 5);
lean_closure_set(x_59, 0, x_57);
lean_closure_set(x_59, 1, x_58);
lean_closure_set(x_59, 2, x_51);
lean_closure_set(x_59, 3, x_3);
lean_closure_set(x_59, 4, x_49);
x_60 = l_Lean_Server_FileWorker_collectOpenNamespaces(x_57, x_58);
if (lean_is_scalar(x_47)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_47;
}
lean_ctor_set(x_61, 0, x_55);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_ctor_get(x_56, 0);
lean_inc(x_62);
lean_dec(x_56);
x_63 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
lean_ctor_set(x_63, 2, x_59);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
return x_64;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeFallbackQuery_x3f___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Server_FileWorker_computeFallbackQuery_x3f___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeFallbackQuery_x3f___lam__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Server_FileWorker_computeFallbackQuery_x3f___lam__1(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeFallbackQuery_x3f___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Server_FileWorker_computeFallbackQuery_x3f___lam__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeIdQuery_x3f___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_9 = l_Lean_Server_Completion_minimizeGlobalIdentifierInContext(x_1, x_2, x_8);
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
lean_dec(x_3);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_ctor_get(x_11, 3);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_5);
x_14 = l_Lean_FileMap_utf8RangeToLspRange(x_12, x_13);
lean_dec(x_13);
lean_inc(x_9);
x_15 = l_Lean_Name_toString(x_9, x_6, x_7);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_15);
lean_ctor_set(x_17, 2, x_16);
lean_ctor_set(x_17, 3, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_9);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeIdQuery_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_box(1);
x_6 = lean_unbox(x_5);
x_7 = l_Lean_Syntax_getPos_x3f(x_3, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_unbox(x_5);
x_11 = l_Lean_Syntax_getTailPos_x3f(x_3, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_box(0);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_14 = lean_ctor_get(x_11, 0);
x_15 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_computeFallbackQuery_x3f___lam__1___boxed), 1, 0);
x_16 = lean_unbox(x_5);
lean_inc(x_15);
x_17 = l_Lean_Name_toString(x_4, x_16, x_15);
x_18 = lean_ctor_get(x_2, 0);
lean_inc(x_18);
lean_dec(x_2);
x_19 = lean_ctor_get(x_18, 4);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 5);
lean_inc(x_20);
lean_inc(x_20);
lean_inc(x_19);
x_21 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_computeIdQuery_x3f___lam__1___boxed), 8, 7);
lean_closure_set(x_21, 0, x_19);
lean_closure_set(x_21, 1, x_20);
lean_closure_set(x_21, 2, x_1);
lean_closure_set(x_21, 3, x_9);
lean_closure_set(x_21, 4, x_14);
lean_closure_set(x_21, 5, x_5);
lean_closure_set(x_21, 6, x_15);
x_22 = l_Lean_Server_FileWorker_collectOpenNamespaces(x_19, x_20);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_17);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_ctor_get(x_18, 0);
lean_inc(x_24);
lean_dec(x_18);
x_25 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_25, 2, x_21);
lean_ctor_set(x_11, 0, x_25);
return x_11;
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_26 = lean_ctor_get(x_11, 0);
lean_inc(x_26);
lean_dec(x_11);
x_27 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_computeFallbackQuery_x3f___lam__1___boxed), 1, 0);
x_28 = lean_unbox(x_5);
lean_inc(x_27);
x_29 = l_Lean_Name_toString(x_4, x_28, x_27);
x_30 = lean_ctor_get(x_2, 0);
lean_inc(x_30);
lean_dec(x_2);
x_31 = lean_ctor_get(x_30, 4);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 5);
lean_inc(x_32);
lean_inc(x_32);
lean_inc(x_31);
x_33 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_computeIdQuery_x3f___lam__1___boxed), 8, 7);
lean_closure_set(x_33, 0, x_31);
lean_closure_set(x_33, 1, x_32);
lean_closure_set(x_33, 2, x_1);
lean_closure_set(x_33, 3, x_9);
lean_closure_set(x_33, 4, x_26);
lean_closure_set(x_33, 5, x_5);
lean_closure_set(x_33, 6, x_27);
x_34 = l_Lean_Server_FileWorker_collectOpenNamespaces(x_31, x_32);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_29);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_ctor_get(x_30, 0);
lean_inc(x_36);
lean_dec(x_30);
x_37 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
lean_ctor_set(x_37, 2, x_33);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
return x_38;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeIdQuery_x3f___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_6);
lean_dec(x_6);
x_10 = l_Lean_Server_FileWorker_computeIdQuery_x3f___lam__1(x_1, x_2, x_3, x_4, x_5, x_9, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeIdQuery_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_FileWorker_computeIdQuery_x3f(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Server_FileWorker_computeDotQuery_x3f_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_box(0);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_mk_empty_array_with_capacity(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_usize_of_nat(x_11);
x_13 = lean_usize_add(x_2, x_12);
x_14 = lean_array_uset(x_7, x_2, x_10);
x_2 = x_13;
x_3 = x_14;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeDotQuery_x3f___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_14; lean_object* x_15; lean_object* x_19; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_19 = lean_infer_type(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_20, x_3, x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_Server_Completion_getDotCompletionTypeNames(x_23, x_2, x_3, x_4, x_5, x_24);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_25, 0, x_28);
return x_25;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_25, 0);
x_30 = lean_ctor_get(x_25, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_25);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_29);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_25, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_25, 1);
lean_inc(x_34);
lean_dec(x_25);
x_14 = x_33;
x_15 = x_34;
goto block_18;
}
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_35 = lean_ctor_get(x_19, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_19, 1);
lean_inc(x_36);
lean_dec(x_19);
x_14 = x_35;
x_15 = x_36;
goto block_18;
}
block_13:
{
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
return x_11;
}
else
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_7);
return x_12;
}
}
block_18:
{
uint8_t x_16; 
x_16 = l_Lean_Exception_isInterrupt(x_14);
if (x_16 == 0)
{
uint8_t x_17; 
x_17 = l_Lean_Exception_isRuntime(x_14);
x_7 = x_15;
x_8 = x_14;
x_9 = x_17;
goto block_13;
}
else
{
x_7 = x_15;
x_8 = x_14;
x_9 = x_16;
goto block_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeDotQuery_x3f___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
x_6 = l_Lean_FileMap_utf8RangeToLspRange(x_3, x_5);
lean_dec(x_5);
x_7 = l_Lean_Name_getString_x21(x_4);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_7);
lean_ctor_set(x_9, 2, x_8);
lean_ctor_set(x_9, 3, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeDotQuery_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_box(1);
x_8 = lean_unbox(x_7);
x_9 = l_Lean_Syntax_getPos_x3f(x_6, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_4);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_unbox(x_7);
x_14 = l_Lean_Syntax_getTailPos_x3f(x_6, x_13);
lean_dec(x_6);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_4);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_ctor_get(x_3, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_3, 3);
lean_inc(x_19);
lean_dec(x_3);
x_20 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_computeDotQuery_x3f___lam__0), 6, 1);
lean_closure_set(x_20, 0, x_19);
lean_inc(x_2);
x_21 = l_Lean_Elab_ContextInfo_runMetaM___redArg(x_2, x_18, x_20, x_4);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_2);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 0);
lean_dec(x_24);
x_25 = lean_box(0);
lean_ctor_set(x_21, 0, x_25);
return x_21;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_dec(x_21);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_21);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_21, 0);
lean_dec(x_30);
x_31 = !lean_is_exclusive(x_22);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; size_t x_39; lean_object* x_40; size_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_32 = lean_ctor_get(x_22, 0);
x_33 = lean_ctor_get(x_1, 0);
lean_inc(x_33);
lean_dec(x_1);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_ctor_get(x_34, 3);
lean_inc(x_35);
lean_dec(x_34);
lean_inc(x_35);
lean_inc(x_17);
lean_inc(x_12);
x_36 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_computeDotQuery_x3f___lam__1), 4, 3);
lean_closure_set(x_36, 0, x_12);
lean_closure_set(x_36, 1, x_17);
lean_closure_set(x_36, 2, x_35);
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_string_utf8_extract(x_37, x_12, x_17);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_37);
x_39 = lean_array_size(x_32);
x_40 = lean_unsigned_to_nat(0u);
x_41 = lean_usize_of_nat(x_40);
x_42 = l_Array_mapMUnsafe_map___at___Lean_Server_FileWorker_computeDotQuery_x3f_spec__0(x_39, x_41, x_32);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_38);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_ctor_get(x_2, 0);
lean_inc(x_44);
lean_dec(x_2);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_45);
lean_ctor_set(x_46, 2, x_36);
lean_ctor_set(x_22, 0, x_46);
return x_21;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; size_t x_54; lean_object* x_55; size_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_47 = lean_ctor_get(x_22, 0);
lean_inc(x_47);
lean_dec(x_22);
x_48 = lean_ctor_get(x_1, 0);
lean_inc(x_48);
lean_dec(x_1);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
lean_dec(x_48);
x_50 = lean_ctor_get(x_49, 3);
lean_inc(x_50);
lean_dec(x_49);
lean_inc(x_50);
lean_inc(x_17);
lean_inc(x_12);
x_51 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_computeDotQuery_x3f___lam__1), 4, 3);
lean_closure_set(x_51, 0, x_12);
lean_closure_set(x_51, 1, x_17);
lean_closure_set(x_51, 2, x_50);
x_52 = lean_ctor_get(x_50, 0);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_string_utf8_extract(x_52, x_12, x_17);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_52);
x_54 = lean_array_size(x_47);
x_55 = lean_unsigned_to_nat(0u);
x_56 = lean_usize_of_nat(x_55);
x_57 = l_Array_mapMUnsafe_map___at___Lean_Server_FileWorker_computeDotQuery_x3f_spec__0(x_54, x_56, x_47);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_53);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_ctor_get(x_2, 0);
lean_inc(x_59);
lean_dec(x_2);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
lean_dec(x_59);
x_61 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_60);
lean_ctor_set(x_61, 2, x_51);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_21, 0, x_62);
return x_21;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; size_t x_72; lean_object* x_73; size_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_63 = lean_ctor_get(x_21, 1);
lean_inc(x_63);
lean_dec(x_21);
x_64 = lean_ctor_get(x_22, 0);
lean_inc(x_64);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 x_65 = x_22;
} else {
 lean_dec_ref(x_22);
 x_65 = lean_box(0);
}
x_66 = lean_ctor_get(x_1, 0);
lean_inc(x_66);
lean_dec(x_1);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
lean_dec(x_66);
x_68 = lean_ctor_get(x_67, 3);
lean_inc(x_68);
lean_dec(x_67);
lean_inc(x_68);
lean_inc(x_17);
lean_inc(x_12);
x_69 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_computeDotQuery_x3f___lam__1), 4, 3);
lean_closure_set(x_69, 0, x_12);
lean_closure_set(x_69, 1, x_17);
lean_closure_set(x_69, 2, x_68);
x_70 = lean_ctor_get(x_68, 0);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_string_utf8_extract(x_70, x_12, x_17);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_70);
x_72 = lean_array_size(x_64);
x_73 = lean_unsigned_to_nat(0u);
x_74 = lean_usize_of_nat(x_73);
x_75 = l_Array_mapMUnsafe_map___at___Lean_Server_FileWorker_computeDotQuery_x3f_spec__0(x_72, x_74, x_64);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_71);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_ctor_get(x_2, 0);
lean_inc(x_77);
lean_dec(x_2);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
lean_dec(x_77);
x_79 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_79, 0, x_76);
lean_ctor_set(x_79, 1, x_78);
lean_ctor_set(x_79, 2, x_69);
if (lean_is_scalar(x_65)) {
 x_80 = lean_alloc_ctor(1, 1, 0);
} else {
 x_80 = x_65;
}
lean_ctor_set(x_80, 0, x_79);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_63);
return x_81;
}
}
}
else
{
uint8_t x_82; 
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_2);
lean_dec(x_1);
x_82 = !lean_is_exclusive(x_21);
if (x_82 == 0)
{
return x_21;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_21, 0);
x_84 = lean_ctor_get(x_21, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_21);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Server_FileWorker_computeDotQuery_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lean_Server_FileWorker_computeDotQuery_x3f_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeDotIdQuery_x3f___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_1, x_3, x_6);
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
x_11 = l_Lean_Expr_cleanupAnnotations(x_8);
x_12 = l_Lean_Expr_getAppFn(x_11);
lean_dec(x_11);
x_13 = l_Lean_Expr_cleanupAnnotations(x_12);
if (lean_obj_tag(x_13) == 4)
{
lean_object* x_14; 
x_14 = l_Lean_Server_Completion_getDotCompletionTypeNames(x_13, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
lean_dec(x_10);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_14, 0, x_17);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_14, 0);
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_14);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_18);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_14);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_29; 
x_23 = lean_ctor_get(x_14, 0);
x_24 = lean_ctor_get(x_14, 1);
lean_inc(x_24);
lean_inc(x_23);
x_29 = l_Lean_Exception_isInterrupt(x_23);
if (x_29 == 0)
{
uint8_t x_30; 
x_30 = l_Lean_Exception_isRuntime(x_23);
lean_dec(x_23);
x_25 = x_30;
goto block_28;
}
else
{
lean_dec(x_23);
x_25 = x_29;
goto block_28;
}
block_28:
{
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_14);
x_26 = lean_box(0);
if (lean_is_scalar(x_10)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_10;
}
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_24);
return x_27;
}
else
{
lean_dec(x_24);
lean_dec(x_10);
return x_14;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_38; 
x_31 = lean_ctor_get(x_14, 0);
x_32 = lean_ctor_get(x_14, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_14);
lean_inc(x_32);
lean_inc(x_31);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_38 = l_Lean_Exception_isInterrupt(x_31);
if (x_38 == 0)
{
uint8_t x_39; 
x_39 = l_Lean_Exception_isRuntime(x_31);
lean_dec(x_31);
x_34 = x_39;
goto block_37;
}
else
{
lean_dec(x_31);
x_34 = x_38;
goto block_37;
}
block_37:
{
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_33);
x_35 = lean_box(0);
if (lean_is_scalar(x_10)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_10;
}
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_32);
return x_36;
}
else
{
lean_dec(x_32);
lean_dec(x_10);
return x_33;
}
}
}
}
}
else
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_40 = lean_box(0);
if (lean_is_scalar(x_10)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_10;
}
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_9);
return x_41;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeDotIdQuery_x3f___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_6, 3);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_3);
x_9 = l_Lean_FileMap_utf8RangeToLspRange(x_7, x_8);
lean_dec(x_8);
x_10 = l_Lean_Name_getString_x21(x_4);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_10);
lean_ctor_set(x_12, 2, x_11);
lean_ctor_set(x_12, 3, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeDotIdQuery_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_box(1);
x_9 = lean_unbox(x_8);
x_10 = l_Lean_Syntax_getPos_x3f(x_3, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_7);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_unbox(x_8);
x_15 = l_Lean_Syntax_getTailPos_x3f(x_3, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_7);
return x_17;
}
else
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_7);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_15, 0);
lean_inc(x_20);
lean_dec(x_15);
x_21 = lean_ctor_get(x_6, 0);
lean_inc(x_21);
lean_dec(x_6);
x_22 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_computeDotIdQuery_x3f___lam__0), 6, 1);
lean_closure_set(x_22, 0, x_21);
lean_inc(x_2);
x_23 = l_Lean_Elab_ContextInfo_runMetaM___redArg(x_2, x_5, x_22, x_7);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
lean_dec(x_20);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_23, 0);
lean_dec(x_26);
x_27 = lean_box(0);
lean_ctor_set(x_23, 0, x_27);
return x_23;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_23, 1);
lean_inc(x_28);
lean_dec(x_23);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_23);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_23, 0);
lean_dec(x_32);
x_33 = !lean_is_exclusive(x_24);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; size_t x_39; lean_object* x_40; size_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_34 = lean_ctor_get(x_24, 0);
x_35 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_computeFallbackQuery_x3f___lam__1___boxed), 1, 0);
x_36 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_computeDotIdQuery_x3f___lam__2), 4, 3);
lean_closure_set(x_36, 0, x_1);
lean_closure_set(x_36, 1, x_13);
lean_closure_set(x_36, 2, x_20);
x_37 = lean_unbox(x_8);
x_38 = l_Lean_Name_toString(x_4, x_37, x_35);
x_39 = lean_array_size(x_34);
x_40 = lean_unsigned_to_nat(0u);
x_41 = lean_usize_of_nat(x_40);
x_42 = l_Array_mapMUnsafe_map___at___Lean_Server_FileWorker_computeDotQuery_x3f_spec__0(x_39, x_41, x_34);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_38);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_ctor_get(x_2, 0);
lean_inc(x_44);
lean_dec(x_2);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_45);
lean_ctor_set(x_46, 2, x_36);
lean_ctor_set(x_24, 0, x_46);
return x_23;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; size_t x_52; lean_object* x_53; size_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_47 = lean_ctor_get(x_24, 0);
lean_inc(x_47);
lean_dec(x_24);
x_48 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_computeFallbackQuery_x3f___lam__1___boxed), 1, 0);
x_49 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_computeDotIdQuery_x3f___lam__2), 4, 3);
lean_closure_set(x_49, 0, x_1);
lean_closure_set(x_49, 1, x_13);
lean_closure_set(x_49, 2, x_20);
x_50 = lean_unbox(x_8);
x_51 = l_Lean_Name_toString(x_4, x_50, x_48);
x_52 = lean_array_size(x_47);
x_53 = lean_unsigned_to_nat(0u);
x_54 = lean_usize_of_nat(x_53);
x_55 = l_Array_mapMUnsafe_map___at___Lean_Server_FileWorker_computeDotQuery_x3f_spec__0(x_52, x_54, x_47);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_51);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_ctor_get(x_2, 0);
lean_inc(x_57);
lean_dec(x_2);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
lean_dec(x_57);
x_59 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_59, 0, x_56);
lean_ctor_set(x_59, 1, x_58);
lean_ctor_set(x_59, 2, x_49);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_23, 0, x_60);
return x_23;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; size_t x_68; lean_object* x_69; size_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_61 = lean_ctor_get(x_23, 1);
lean_inc(x_61);
lean_dec(x_23);
x_62 = lean_ctor_get(x_24, 0);
lean_inc(x_62);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 x_63 = x_24;
} else {
 lean_dec_ref(x_24);
 x_63 = lean_box(0);
}
x_64 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_computeFallbackQuery_x3f___lam__1___boxed), 1, 0);
x_65 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_computeDotIdQuery_x3f___lam__2), 4, 3);
lean_closure_set(x_65, 0, x_1);
lean_closure_set(x_65, 1, x_13);
lean_closure_set(x_65, 2, x_20);
x_66 = lean_unbox(x_8);
x_67 = l_Lean_Name_toString(x_4, x_66, x_64);
x_68 = lean_array_size(x_62);
x_69 = lean_unsigned_to_nat(0u);
x_70 = lean_usize_of_nat(x_69);
x_71 = l_Array_mapMUnsafe_map___at___Lean_Server_FileWorker_computeDotQuery_x3f_spec__0(x_68, x_70, x_62);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_67);
lean_ctor_set(x_72, 1, x_71);
x_73 = lean_ctor_get(x_2, 0);
lean_inc(x_73);
lean_dec(x_2);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
lean_dec(x_73);
x_75 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_75, 0, x_72);
lean_ctor_set(x_75, 1, x_74);
lean_ctor_set(x_75, 2, x_65);
if (lean_is_scalar(x_63)) {
 x_76 = lean_alloc_ctor(1, 1, 0);
} else {
 x_76 = x_63;
}
lean_ctor_set(x_76, 0, x_75);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_61);
return x_77;
}
}
}
else
{
uint8_t x_78; 
lean_dec(x_20);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_78 = !lean_is_exclusive(x_23);
if (x_78 == 0)
{
return x_23;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_23, 0);
x_80 = lean_ctor_get(x_23, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_23);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeDotIdQuery_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Server_FileWorker_computeDotIdQuery_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeQuery_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_box(1);
x_7 = lean_unbox(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_8 = l_Lean_Server_RequestM_findCmdDataAtPos(x_1, x_5, x_7);
x_9 = lean_task_get_own(x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_4);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_15 = x_12;
} else {
 lean_dec_ref(x_12);
 x_15 = lean_box(0);
}
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_ctor_get(x_20, 3);
lean_inc(x_21);
lean_dec(x_20);
lean_inc(x_14);
x_22 = l_Lean_Server_Completion_findPrioritizedCompletionPartitionsAt(x_21, x_5, x_13, x_14);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_unsigned_to_nat(0u);
x_25 = lean_array_get_size(x_23);
x_26 = lean_nat_dec_lt(x_24, x_25);
lean_dec(x_25);
if (x_26 == 0)
{
lean_dec(x_23);
goto block_18;
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_array_fget(x_23, x_24);
lean_dec(x_23);
x_28 = lean_array_get_size(x_27);
x_29 = lean_nat_dec_lt(x_24, x_28);
lean_dec(x_28);
if (x_29 == 0)
{
lean_dec(x_27);
goto block_18;
}
else
{
lean_object* x_30; uint8_t x_31; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_3);
lean_dec(x_2);
x_30 = lean_array_fget(x_27, x_24);
lean_dec(x_27);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = lean_ctor_get(x_30, 1);
lean_dec(x_33);
x_34 = lean_ctor_get(x_32, 2);
lean_inc(x_34);
switch (lean_obj_tag(x_34)) {
case 0:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_free_object(x_30);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_36 = lean_ctor_get(x_34, 0);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_Lean_Server_FileWorker_computeDotQuery_x3f(x_1, x_35, x_36, x_4);
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
return x_37;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_37, 0);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_37);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_37);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_37, 0);
x_44 = l_Lean_Server_RequestError_ofIoError(x_43);
lean_ctor_set(x_37, 0, x_44);
return x_37;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_37, 0);
x_46 = lean_ctor_get(x_37, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_37);
x_47 = l_Lean_Server_RequestError_ofIoError(x_45);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
}
case 1:
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_ctor_get(x_32, 1);
lean_inc(x_49);
lean_dec(x_32);
x_50 = lean_ctor_get(x_34, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_34, 1);
lean_inc(x_51);
lean_dec(x_34);
x_52 = l_Lean_Server_FileWorker_computeIdQuery_x3f(x_1, x_49, x_50, x_51);
lean_dec(x_50);
lean_ctor_set(x_30, 1, x_4);
lean_ctor_set(x_30, 0, x_52);
return x_30;
}
case 2:
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_free_object(x_30);
x_53 = lean_ctor_get(x_32, 1);
lean_inc(x_53);
lean_dec(x_32);
x_54 = lean_ctor_get(x_34, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_34, 1);
lean_inc(x_55);
x_56 = lean_ctor_get(x_34, 2);
lean_inc(x_56);
x_57 = lean_ctor_get(x_34, 3);
lean_inc(x_57);
lean_dec(x_34);
x_58 = l_Lean_Server_FileWorker_computeDotIdQuery_x3f(x_1, x_53, x_54, x_55, x_56, x_57, x_4);
lean_dec(x_54);
if (lean_obj_tag(x_58) == 0)
{
uint8_t x_59; 
x_59 = !lean_is_exclusive(x_58);
if (x_59 == 0)
{
return x_58;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_58, 0);
x_61 = lean_ctor_get(x_58, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_58);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
else
{
uint8_t x_63; 
x_63 = !lean_is_exclusive(x_58);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_58, 0);
x_65 = l_Lean_Server_RequestError_ofIoError(x_64);
lean_ctor_set(x_58, 0, x_65);
return x_58;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_58, 0);
x_67 = lean_ctor_get(x_58, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_58);
x_68 = l_Lean_Server_RequestError_ofIoError(x_66);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_67);
return x_69;
}
}
}
default: 
{
lean_object* x_70; 
lean_dec(x_34);
lean_dec(x_32);
lean_dec(x_1);
x_70 = lean_box(0);
lean_ctor_set(x_30, 1, x_4);
lean_ctor_set(x_30, 0, x_70);
return x_30;
}
}
}
else
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_30, 0);
lean_inc(x_71);
lean_dec(x_30);
x_72 = lean_ctor_get(x_71, 2);
lean_inc(x_72);
switch (lean_obj_tag(x_72)) {
case 0:
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = lean_ctor_get(x_72, 0);
lean_inc(x_74);
lean_dec(x_72);
x_75 = l_Lean_Server_FileWorker_computeDotQuery_x3f(x_1, x_73, x_74, x_4);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_78 = x_75;
} else {
 lean_dec_ref(x_75);
 x_78 = lean_box(0);
}
if (lean_is_scalar(x_78)) {
 x_79 = lean_alloc_ctor(0, 2, 0);
} else {
 x_79 = x_78;
}
lean_ctor_set(x_79, 0, x_76);
lean_ctor_set(x_79, 1, x_77);
return x_79;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_80 = lean_ctor_get(x_75, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_75, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_82 = x_75;
} else {
 lean_dec_ref(x_75);
 x_82 = lean_box(0);
}
x_83 = l_Lean_Server_RequestError_ofIoError(x_80);
if (lean_is_scalar(x_82)) {
 x_84 = lean_alloc_ctor(1, 2, 0);
} else {
 x_84 = x_82;
}
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_81);
return x_84;
}
}
case 1:
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_85 = lean_ctor_get(x_71, 1);
lean_inc(x_85);
lean_dec(x_71);
x_86 = lean_ctor_get(x_72, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_72, 1);
lean_inc(x_87);
lean_dec(x_72);
x_88 = l_Lean_Server_FileWorker_computeIdQuery_x3f(x_1, x_85, x_86, x_87);
lean_dec(x_86);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_4);
return x_89;
}
case 2:
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_90 = lean_ctor_get(x_71, 1);
lean_inc(x_90);
lean_dec(x_71);
x_91 = lean_ctor_get(x_72, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_72, 1);
lean_inc(x_92);
x_93 = lean_ctor_get(x_72, 2);
lean_inc(x_93);
x_94 = lean_ctor_get(x_72, 3);
lean_inc(x_94);
lean_dec(x_72);
x_95 = l_Lean_Server_FileWorker_computeDotIdQuery_x3f(x_1, x_90, x_91, x_92, x_93, x_94, x_4);
lean_dec(x_91);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_98 = x_95;
} else {
 lean_dec_ref(x_95);
 x_98 = lean_box(0);
}
if (lean_is_scalar(x_98)) {
 x_99 = lean_alloc_ctor(0, 2, 0);
} else {
 x_99 = x_98;
}
lean_ctor_set(x_99, 0, x_96);
lean_ctor_set(x_99, 1, x_97);
return x_99;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_100 = lean_ctor_get(x_95, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_95, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_102 = x_95;
} else {
 lean_dec_ref(x_95);
 x_102 = lean_box(0);
}
x_103 = l_Lean_Server_RequestError_ofIoError(x_100);
if (lean_is_scalar(x_102)) {
 x_104 = lean_alloc_ctor(1, 2, 0);
} else {
 x_104 = x_102;
}
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_101);
return x_104;
}
}
default: 
{
lean_object* x_105; lean_object* x_106; 
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_1);
x_105 = lean_box(0);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_4);
return x_106;
}
}
}
}
}
block_18:
{
lean_object* x_16; lean_object* x_17; 
x_16 = l_Lean_Server_FileWorker_computeFallbackQuery_x3f(x_1, x_2, x_3, x_14);
if (lean_is_scalar(x_15)) {
 x_17 = lean_alloc_ctor(0, 2, 0);
} else {
 x_17 = x_15;
}
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_4);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeQuery_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Server_FileWorker_computeQuery_x3f___redArg(x_1, x_2, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeQuery_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Server_FileWorker_computeQuery_x3f(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_importAllUnknownIdentifiersProvider() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_mk_string_unchecked("unknownIdentifiers", 18, 18);
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_importAllUnknownIdentifiersCodeAction(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_3 = lean_box(0);
x_4 = lean_mk_string_unchecked("Import all unambiguous unknown identifiers", 42, 42);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_2);
x_6 = lean_box(0);
x_7 = lean_box(0);
x_8 = lean_box(0);
x_9 = lean_box(0);
x_10 = l_Lean_Server_FileWorker_importAllUnknownIdentifiersProvider;
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_10);
lean_ctor_set(x_12, 2, x_11);
x_13 = l___private_Lean_Server_CodeActions_Basic_0__Lean_Server_toJsonCodeActionResolveData____x40_Lean_Server_CodeActions_Basic___hyg_59_(x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_15, 0, x_3);
lean_ctor_set(x_15, 1, x_3);
lean_ctor_set(x_15, 2, x_4);
lean_ctor_set(x_15, 3, x_5);
lean_ctor_set(x_15, 4, x_6);
lean_ctor_set(x_15, 5, x_7);
lean_ctor_set(x_15, 6, x_3);
lean_ctor_set(x_15, 7, x_8);
lean_ctor_set(x_15, 8, x_9);
lean_ctor_set(x_15, 9, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_eq(x_4, x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = lean_array_uget(x_3, x_4);
lean_inc(x_2);
x_11 = l_Lean_Server_FileWorker_computeQuery_x3f___redArg(x_9, x_2, x_10, x_7);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
if (lean_obj_tag(x_12) == 0)
{
x_14 = x_6;
goto block_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_12, 0);
lean_inc(x_20);
lean_dec(x_12);
x_21 = lean_array_push(x_6, x_20);
x_14 = x_21;
goto block_19;
}
block_19:
{
lean_object* x_15; size_t x_16; size_t x_17; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_usize_of_nat(x_15);
x_17 = lean_usize_add(x_4, x_16);
x_4 = x_17;
x_6 = x_14;
x_7 = x_13;
goto _start;
}
}
else
{
uint8_t x_22; 
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_11);
if (x_22 == 0)
{
return x_11;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_11, 0);
x_24 = lean_ctor_get(x_11, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_11);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
else
{
lean_object* x_26; 
lean_dec(x_2);
lean_dec(x_1);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_6);
lean_ctor_set(x_26, 1, x_7);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_mk_empty_array_with_capacity(x_8);
x_10 = lean_nat_dec_lt(x_4, x_5);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_7);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_3);
x_13 = lean_nat_dec_le(x_5, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_9);
lean_ctor_set(x_14, 1, x_7);
return x_14;
}
else
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_usize_of_nat(x_4);
x_16 = lean_usize_of_nat(x_5);
x_17 = l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__0_spec__0___redArg(x_1, x_2, x_3, x_15, x_16, x_9, x_7);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec(x_5);
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
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_sendServerRequest___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__3___redArg___lam__0(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanQueryModuleResponse____x40_Lean_Data_Lsp_Internal___hyg_3516_(x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
lean_free_object(x_1);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_box(0);
x_7 = lean_mk_string_unchecked("Cannot parse server request response: ", 38, 38);
x_8 = l_Lean_Json_compress(x_3);
x_9 = lean_string_append(x_7, x_8);
lean_dec(x_8);
x_10 = lean_mk_string_unchecked("\n", 1, 1);
x_11 = lean_string_append(x_9, x_10);
lean_dec(x_10);
x_12 = lean_string_append(x_11, x_5);
lean_dec(x_5);
x_13 = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_unbox(x_6);
lean_ctor_set_uint8(x_13, sizeof(void*)*1, x_14);
return x_13;
}
else
{
lean_object* x_15; 
lean_dec(x_3);
x_15 = lean_ctor_get(x_4, 0);
lean_inc(x_15);
lean_dec(x_4);
lean_ctor_set(x_1, 0, x_15);
return x_1;
}
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
lean_dec(x_1);
lean_inc(x_16);
x_17 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanQueryModuleResponse____x40_Lean_Data_Lsp_Internal___hyg_3516_(x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_box(0);
x_20 = lean_mk_string_unchecked("Cannot parse server request response: ", 38, 38);
x_21 = l_Lean_Json_compress(x_16);
x_22 = lean_string_append(x_20, x_21);
lean_dec(x_21);
x_23 = lean_mk_string_unchecked("\n", 1, 1);
x_24 = lean_string_append(x_22, x_23);
lean_dec(x_23);
x_25 = lean_string_append(x_24, x_18);
lean_dec(x_18);
x_26 = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_unbox(x_19);
lean_ctor_set_uint8(x_26, sizeof(void*)*1, x_27);
return x_26;
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_16);
x_28 = lean_ctor_get(x_17, 0);
lean_inc(x_28);
lean_dec(x_17);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_1);
if (x_30 == 0)
{
return x_1;
}
else
{
uint8_t x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_32 = lean_ctor_get(x_1, 0);
lean_inc(x_32);
lean_dec(x_1);
x_33 = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set_uint8(x_33, sizeof(void*)*1, x_31);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_sendServerRequest___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 5);
lean_inc(x_5);
lean_dec(x_3);
x_6 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanQueryModuleParams____x40_Lean_Data_Lsp_Internal___hyg_3207_(x_2);
x_7 = lean_apply_3(x_5, x_1, x_6, x_4);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_alloc_closure((void*)(l_Lean_Server_RequestM_sendServerRequest___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__3___redArg___lam__0), 1, 0);
x_11 = l_Lean_Server_ServerTask_mapCheap___redArg(x_10, x_9);
lean_ctor_set(x_7, 0, x_11);
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_7, 0);
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_7);
x_14 = lean_alloc_closure((void*)(l_Lean_Server_RequestM_sendServerRequest___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__3___redArg___lam__0), 1, 0);
x_15 = l_Lean_Server_ServerTask_mapCheap___redArg(x_14, x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_sendServerRequest___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Server_RequestM_sendServerRequest___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__3___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__4___redArg___lam__0(uint8_t x_1, lean_object* x_2) {
_start:
{
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_17; 
x_17 = lean_usize_dec_lt(x_7, x_6);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_3);
lean_dec(x_1);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_8);
lean_ctor_set(x_18, 1, x_9);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_28; 
x_19 = lean_array_uget(x_5, x_7);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
x_22 = lean_ctor_get_uint8(x_19, sizeof(void*)*2);
lean_dec(x_19);
x_23 = lean_ctor_get(x_2, 1);
x_24 = lean_ctor_get(x_8, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_8, 1);
lean_inc(x_25);
lean_dec(x_8);
x_26 = lean_ctor_get(x_1, 1);
lean_inc(x_26);
lean_inc(x_21);
lean_inc(x_26);
x_27 = l_Lean_Environment_contains(x_26, x_21, x_17);
if (x_27 == 0)
{
goto block_95;
}
else
{
if (x_4 == 0)
{
lean_dec(x_26);
x_28 = x_4;
goto block_91;
}
else
{
goto block_95;
}
}
block_91:
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_1, 2);
lean_inc(x_29);
x_30 = lean_apply_1(x_29, x_21);
if (x_27 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_31 = lean_box(x_28);
x_32 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__4___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_32, 0, x_31);
x_33 = lean_box(0);
x_34 = lean_mk_string_unchecked("Import ", 7, 7);
x_35 = lean_ctor_get(x_30, 0);
lean_inc(x_35);
lean_inc(x_32);
x_36 = l_Lean_Name_toString(x_35, x_17, x_32);
x_37 = lean_string_append(x_34, x_36);
lean_dec(x_36);
x_38 = lean_mk_string_unchecked(" from ", 6, 6);
x_39 = lean_string_append(x_37, x_38);
lean_dec(x_38);
x_40 = l_Lean_Name_toString(x_20, x_17, x_32);
x_41 = lean_string_append(x_39, x_40);
x_42 = lean_mk_string_unchecked("quickfix", 8, 8);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_44 = lean_box(0);
x_45 = lean_box(0);
x_46 = l_Lean_Server_FileWorker_EditableDocument_versionedIdentifier(x_23);
x_47 = lean_mk_string_unchecked("import ", 7, 7);
x_48 = lean_string_append(x_47, x_40);
lean_dec(x_40);
x_49 = lean_mk_string_unchecked("\n", 1, 1);
x_50 = lean_string_append(x_48, x_49);
lean_dec(x_49);
lean_inc(x_3);
x_51 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_51, 0, x_3);
lean_ctor_set(x_51, 1, x_50);
lean_ctor_set(x_51, 2, x_33);
lean_ctor_set(x_51, 3, x_33);
x_52 = lean_ctor_get(x_30, 1);
lean_inc(x_52);
lean_dec(x_30);
x_53 = lean_unsigned_to_nat(2u);
x_54 = lean_mk_empty_array_with_capacity(x_53);
x_55 = lean_array_push(x_54, x_51);
x_56 = lean_array_push(x_55, x_52);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_46);
lean_ctor_set(x_57, 1, x_56);
x_58 = l_Lean_Lsp_WorkspaceEdit_ofTextDocumentEdit(x_57);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_58);
x_60 = lean_box(0);
x_61 = lean_box(0);
x_62 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_62, 0, x_33);
lean_ctor_set(x_62, 1, x_33);
lean_ctor_set(x_62, 2, x_41);
lean_ctor_set(x_62, 3, x_43);
lean_ctor_set(x_62, 4, x_44);
lean_ctor_set(x_62, 5, x_45);
lean_ctor_set(x_62, 6, x_33);
lean_ctor_set(x_62, 7, x_59);
lean_ctor_set(x_62, 8, x_60);
lean_ctor_set(x_62, 9, x_61);
x_63 = lean_array_push(x_25, x_62);
if (x_22 == 0)
{
lean_object* x_64; 
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_24);
lean_ctor_set(x_64, 1, x_63);
x_10 = x_64;
x_11 = x_9;
goto block_16;
}
else
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_24);
x_65 = lean_box(x_22);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_63);
x_10 = x_66;
x_11 = x_9;
goto block_16;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_20);
x_67 = lean_box(x_28);
x_68 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__4___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_68, 0, x_67);
x_69 = lean_box(0);
x_70 = lean_mk_string_unchecked("Change to ", 10, 10);
x_71 = lean_ctor_get(x_30, 0);
lean_inc(x_71);
x_72 = l_Lean_Name_toString(x_71, x_27, x_68);
x_73 = lean_string_append(x_70, x_72);
lean_dec(x_72);
x_74 = lean_mk_string_unchecked("quickfix", 8, 8);
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_74);
x_76 = lean_box(0);
x_77 = lean_box(0);
x_78 = l_Lean_Server_FileWorker_EditableDocument_versionedIdentifier(x_23);
x_79 = lean_ctor_get(x_30, 1);
lean_inc(x_79);
lean_dec(x_30);
x_80 = lean_unsigned_to_nat(1u);
x_81 = lean_mk_empty_array_with_capacity(x_80);
x_82 = lean_array_push(x_81, x_79);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_78);
lean_ctor_set(x_83, 1, x_82);
x_84 = l_Lean_Lsp_WorkspaceEdit_ofTextDocumentEdit(x_83);
x_85 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_85, 0, x_84);
x_86 = lean_box(0);
x_87 = lean_box(0);
x_88 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_88, 0, x_69);
lean_ctor_set(x_88, 1, x_69);
lean_ctor_set(x_88, 2, x_73);
lean_ctor_set(x_88, 3, x_75);
lean_ctor_set(x_88, 4, x_76);
lean_ctor_set(x_88, 5, x_77);
lean_ctor_set(x_88, 6, x_69);
lean_ctor_set(x_88, 7, x_85);
lean_ctor_set(x_88, 8, x_86);
lean_ctor_set(x_88, 9, x_87);
x_89 = lean_array_push(x_25, x_88);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_24);
lean_ctor_set(x_90, 1, x_89);
x_10 = x_90;
x_11 = x_9;
goto block_16;
}
}
block_95:
{
lean_object* x_92; uint8_t x_93; 
x_92 = l_Lean_Environment_mainModule(x_26);
lean_dec(x_26);
x_93 = lean_name_eq(x_20, x_92);
lean_dec(x_92);
if (x_93 == 0)
{
x_28 = x_93;
goto block_91;
}
else
{
lean_object* x_94; 
lean_dec(x_21);
lean_dec(x_20);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_24);
lean_ctor_set(x_94, 1, x_25);
x_10 = x_94;
x_11 = x_9;
goto block_16;
}
}
}
block_16:
{
lean_object* x_12; size_t x_13; size_t x_14; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_usize_of_nat(x_12);
x_14 = lean_usize_add(x_7, x_13);
x_7 = x_14;
x_8 = x_10;
x_9 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__4___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__5_spec__5(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_6, x_5);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_2);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_12 = lean_ctor_get(x_7, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
lean_dec(x_7);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_12, 2);
lean_inc(x_17);
x_18 = lean_nat_dec_lt(x_16, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_2);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_14);
lean_ctor_set(x_19, 1, x_15);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_12);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_9);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; size_t x_26; lean_object* x_27; size_t x_28; lean_object* x_29; uint8_t x_30; 
x_22 = lean_array_uget(x_4, x_6);
x_23 = lean_ctor_get(x_12, 0);
lean_inc(x_23);
lean_dec(x_12);
x_24 = lean_array_fget(x_23, x_16);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_14);
lean_ctor_set(x_25, 1, x_15);
x_26 = lean_array_size(x_24);
x_27 = lean_unsigned_to_nat(0u);
x_28 = lean_usize_of_nat(x_27);
lean_inc(x_2);
x_29 = l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__4___redArg(x_22, x_1, x_2, x_3, x_24, x_26, x_28, x_25, x_9);
lean_dec(x_24);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; size_t x_36; size_t x_37; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_ctor_get(x_29, 1);
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_nat_add(x_16, x_33);
lean_dec(x_16);
x_35 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_35, 0, x_23);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set(x_35, 2, x_17);
lean_ctor_set(x_29, 1, x_31);
lean_ctor_set(x_29, 0, x_35);
x_36 = lean_usize_of_nat(x_33);
x_37 = lean_usize_add(x_6, x_36);
x_6 = x_37;
x_7 = x_29;
x_9 = x_32;
goto _start;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; size_t x_45; size_t x_46; 
x_39 = lean_ctor_get(x_29, 0);
x_40 = lean_ctor_get(x_29, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_29);
x_41 = lean_unsigned_to_nat(1u);
x_42 = lean_nat_add(x_16, x_41);
lean_dec(x_16);
x_43 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_43, 0, x_23);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set(x_43, 2, x_17);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_39);
x_45 = lean_usize_of_nat(x_41);
x_46 = lean_usize_add(x_6, x_45);
x_6 = x_46;
x_7 = x_44;
x_9 = x_40;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__5(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_6, x_5);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_2);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_12 = lean_ctor_get(x_7, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
lean_dec(x_7);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_12, 2);
lean_inc(x_17);
x_18 = lean_nat_dec_lt(x_16, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_2);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_14);
lean_ctor_set(x_19, 1, x_15);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_12);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_9);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; size_t x_26; lean_object* x_27; size_t x_28; lean_object* x_29; uint8_t x_30; 
x_22 = lean_array_uget(x_4, x_6);
x_23 = lean_ctor_get(x_12, 0);
lean_inc(x_23);
lean_dec(x_12);
x_24 = lean_array_fget(x_23, x_16);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_14);
lean_ctor_set(x_25, 1, x_15);
x_26 = lean_array_size(x_24);
x_27 = lean_unsigned_to_nat(0u);
x_28 = lean_usize_of_nat(x_27);
lean_inc(x_2);
x_29 = l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__4___redArg(x_22, x_1, x_2, x_3, x_24, x_26, x_28, x_25, x_9);
lean_dec(x_24);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; size_t x_36; size_t x_37; lean_object* x_38; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_ctor_get(x_29, 1);
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_nat_add(x_16, x_33);
lean_dec(x_16);
x_35 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_35, 0, x_23);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set(x_35, 2, x_17);
lean_ctor_set(x_29, 1, x_31);
lean_ctor_set(x_29, 0, x_35);
x_36 = lean_usize_of_nat(x_33);
x_37 = lean_usize_add(x_6, x_36);
x_38 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__5_spec__5(x_1, x_2, x_3, x_4, x_5, x_37, x_29, x_8, x_32);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; size_t x_45; size_t x_46; lean_object* x_47; 
x_39 = lean_ctor_get(x_29, 0);
x_40 = lean_ctor_get(x_29, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_29);
x_41 = lean_unsigned_to_nat(1u);
x_42 = lean_nat_add(x_16, x_41);
lean_dec(x_16);
x_43 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_43, 0, x_23);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set(x_43, 2, x_17);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_39);
x_45 = lean_usize_of_nat(x_41);
x_46 = lean_usize_add(x_6, x_45);
x_47 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__5_spec__5(x_1, x_2, x_3, x_4, x_5, x_46, x_44, x_8, x_40);
return x_47;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lam__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_get_size(x_4);
lean_inc(x_5);
x_9 = l_Array_filterMapM___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__0(x_5, x_3, x_4, x_7, x_8, x_5, x_6);
lean_dec(x_8);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = l_Array_isEmpty___redArg(x_11);
if (x_13 == 0)
{
lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
lean_free_object(x_9);
x_14 = lean_mk_string_unchecked("$/lean/queryModule", 18, 18);
x_15 = lean_array_size(x_11);
x_16 = lean_usize_of_nat(x_7);
lean_inc(x_11);
x_17 = l_Array_mapMUnsafe_map___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2(x_15, x_16, x_11);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_17);
lean_inc(x_5);
x_19 = l_Lean_Server_RequestM_sendServerRequest___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__3___redArg(x_14, x_18, x_5, x_12);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 1);
x_23 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lam__0), 1, 0);
x_24 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lam__1), 1, 0);
x_25 = l_Lean_Server_ServerTask_mapCheap___redArg(x_24, x_21);
x_26 = lean_ctor_get(x_5, 4);
lean_inc(x_26);
x_27 = l_Lean_Server_RequestCancellationToken_requestCancellationTask(x_26);
lean_dec(x_26);
x_28 = l_Lean_Server_ServerTask_mapCheap___redArg(x_23, x_27);
x_29 = lean_box(0);
lean_ctor_set_tag(x_19, 1);
lean_ctor_set(x_19, 1, x_29);
lean_ctor_set(x_19, 0, x_28);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_25);
lean_ctor_set(x_30, 1, x_19);
x_31 = l_Lean_Server_ServerTask_waitAny___redArg(x_30, x_22);
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
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_32, 0);
lean_inc(x_48);
lean_dec(x_32);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
lean_dec(x_48);
x_82 = lean_ctor_get(x_5, 1);
lean_inc(x_82);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
lean_dec(x_82);
x_84 = lean_ctor_get(x_83, 1);
lean_inc(x_84);
x_85 = lean_ctor_get(x_84, 2);
lean_inc(x_85);
lean_dec(x_84);
x_86 = l_Lean_Syntax_getTailPos_x3f(x_85, x_13);
lean_dec(x_85);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; 
lean_dec(x_83);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_7);
lean_ctor_set(x_87, 1, x_7);
x_50 = x_87;
goto block_81;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_88 = lean_ctor_get(x_86, 0);
lean_inc(x_88);
lean_dec(x_86);
x_89 = lean_ctor_get(x_83, 0);
lean_inc(x_89);
lean_dec(x_83);
x_90 = lean_ctor_get(x_89, 3);
lean_inc(x_90);
lean_dec(x_89);
x_91 = l_Lean_FileMap_utf8PosToLspPos(x_90, x_88);
lean_dec(x_88);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
lean_dec(x_91);
x_93 = lean_unsigned_to_nat(1u);
x_94 = lean_nat_add(x_92, x_93);
lean_dec(x_92);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_7);
x_50 = x_95;
goto block_81;
}
block_81:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
lean_inc(x_50);
if (lean_is_scalar(x_34)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_34;
}
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_mk_empty_array_with_capacity(x_7);
x_53 = lean_array_get_size(x_49);
x_54 = l_Array_toSubarray___redArg(x_49, x_7, x_53);
x_55 = lean_box(x_13);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_52);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_56);
x_58 = l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__5(x_5, x_51, x_13, x_11, x_15, x_16, x_57, x_5, x_33);
lean_dec(x_11);
lean_dec(x_5);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
lean_dec(x_59);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_unbox(x_61);
lean_dec(x_61);
if (x_62 == 0)
{
uint8_t x_63; 
lean_dec(x_2);
x_63 = !lean_is_exclusive(x_58);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_58, 0);
lean_dec(x_64);
x_65 = lean_ctor_get(x_60, 1);
lean_inc(x_65);
lean_dec(x_60);
lean_ctor_set(x_58, 0, x_65);
return x_58;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_58, 1);
lean_inc(x_66);
lean_dec(x_58);
x_67 = lean_ctor_get(x_60, 1);
lean_inc(x_67);
lean_dec(x_60);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
}
else
{
uint8_t x_69; 
x_69 = !lean_is_exclusive(x_58);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_70 = lean_ctor_get(x_58, 0);
lean_dec(x_70);
x_71 = lean_ctor_get(x_60, 1);
lean_inc(x_71);
lean_dec(x_60);
x_72 = lean_mk_string_unchecked("quickfix", 8, 8);
x_73 = l_Lean_Server_FileWorker_importAllUnknownIdentifiersCodeAction(x_2, x_72);
x_74 = lean_array_push(x_71, x_73);
lean_ctor_set(x_58, 0, x_74);
return x_58;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_75 = lean_ctor_get(x_58, 1);
lean_inc(x_75);
lean_dec(x_58);
x_76 = lean_ctor_get(x_60, 1);
lean_inc(x_76);
lean_dec(x_60);
x_77 = lean_mk_string_unchecked("quickfix", 8, 8);
x_78 = l_Lean_Server_FileWorker_importAllUnknownIdentifiersCodeAction(x_2, x_77);
x_79 = lean_array_push(x_76, x_78);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_75);
return x_80;
}
}
}
}
else
{
lean_dec(x_48);
lean_dec(x_34);
lean_dec(x_11);
lean_dec(x_2);
x_35 = x_5;
goto block_47;
}
}
else
{
lean_dec(x_34);
lean_dec(x_32);
lean_dec(x_11);
lean_dec(x_2);
x_35 = x_5;
goto block_47;
}
block_47:
{
lean_object* x_36; 
x_36 = l_Lean_Server_RequestM_checkCancelled(x_35, x_33);
lean_dec(x_35);
if (lean_obj_tag(x_36) == 0)
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_36, 0);
lean_dec(x_38);
x_39 = lean_mk_empty_array_with_capacity(x_7);
lean_ctor_set(x_36, 0, x_39);
return x_36;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_36, 1);
lean_inc(x_40);
lean_dec(x_36);
x_41 = lean_mk_empty_array_with_capacity(x_7);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
}
else
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_36);
if (x_43 == 0)
{
return x_36;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_36, 0);
x_45 = lean_ctor_get(x_36, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_36);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_96 = lean_ctor_get(x_19, 0);
x_97 = lean_ctor_get(x_19, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_19);
x_98 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lam__0), 1, 0);
x_99 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lam__1), 1, 0);
x_100 = l_Lean_Server_ServerTask_mapCheap___redArg(x_99, x_96);
x_101 = lean_ctor_get(x_5, 4);
lean_inc(x_101);
x_102 = l_Lean_Server_RequestCancellationToken_requestCancellationTask(x_101);
lean_dec(x_101);
x_103 = l_Lean_Server_ServerTask_mapCheap___redArg(x_98, x_102);
x_104 = lean_box(0);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_100);
lean_ctor_set(x_106, 1, x_105);
x_107 = l_Lean_Server_ServerTask_waitAny___redArg(x_106, x_97);
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_110 = x_107;
} else {
 lean_dec_ref(x_107);
 x_110 = lean_box(0);
}
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_122; 
x_122 = lean_ctor_get(x_108, 0);
lean_inc(x_122);
lean_dec(x_108);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
lean_dec(x_122);
x_149 = lean_ctor_get(x_5, 1);
lean_inc(x_149);
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
lean_dec(x_149);
x_151 = lean_ctor_get(x_150, 1);
lean_inc(x_151);
x_152 = lean_ctor_get(x_151, 2);
lean_inc(x_152);
lean_dec(x_151);
x_153 = l_Lean_Syntax_getTailPos_x3f(x_152, x_13);
lean_dec(x_152);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; 
lean_dec(x_150);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_7);
lean_ctor_set(x_154, 1, x_7);
x_124 = x_154;
goto block_148;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_155 = lean_ctor_get(x_153, 0);
lean_inc(x_155);
lean_dec(x_153);
x_156 = lean_ctor_get(x_150, 0);
lean_inc(x_156);
lean_dec(x_150);
x_157 = lean_ctor_get(x_156, 3);
lean_inc(x_157);
lean_dec(x_156);
x_158 = l_Lean_FileMap_utf8PosToLspPos(x_157, x_155);
lean_dec(x_155);
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
lean_dec(x_158);
x_160 = lean_unsigned_to_nat(1u);
x_161 = lean_nat_add(x_159, x_160);
lean_dec(x_159);
x_162 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_7);
x_124 = x_162;
goto block_148;
}
block_148:
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; 
lean_inc(x_124);
if (lean_is_scalar(x_110)) {
 x_125 = lean_alloc_ctor(0, 2, 0);
} else {
 x_125 = x_110;
}
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_124);
x_126 = lean_mk_empty_array_with_capacity(x_7);
x_127 = lean_array_get_size(x_123);
x_128 = l_Array_toSubarray___redArg(x_123, x_7, x_127);
x_129 = lean_box(x_13);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_126);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_128);
lean_ctor_set(x_131, 1, x_130);
x_132 = l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__5(x_5, x_125, x_13, x_11, x_15, x_16, x_131, x_5, x_109);
lean_dec(x_11);
lean_dec(x_5);
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_133, 1);
lean_inc(x_134);
lean_dec(x_133);
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_unbox(x_135);
lean_dec(x_135);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_dec(x_2);
x_137 = lean_ctor_get(x_132, 1);
lean_inc(x_137);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_138 = x_132;
} else {
 lean_dec_ref(x_132);
 x_138 = lean_box(0);
}
x_139 = lean_ctor_get(x_134, 1);
lean_inc(x_139);
lean_dec(x_134);
if (lean_is_scalar(x_138)) {
 x_140 = lean_alloc_ctor(0, 2, 0);
} else {
 x_140 = x_138;
}
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_137);
return x_140;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_141 = lean_ctor_get(x_132, 1);
lean_inc(x_141);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_142 = x_132;
} else {
 lean_dec_ref(x_132);
 x_142 = lean_box(0);
}
x_143 = lean_ctor_get(x_134, 1);
lean_inc(x_143);
lean_dec(x_134);
x_144 = lean_mk_string_unchecked("quickfix", 8, 8);
x_145 = l_Lean_Server_FileWorker_importAllUnknownIdentifiersCodeAction(x_2, x_144);
x_146 = lean_array_push(x_143, x_145);
if (lean_is_scalar(x_142)) {
 x_147 = lean_alloc_ctor(0, 2, 0);
} else {
 x_147 = x_142;
}
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_141);
return x_147;
}
}
}
else
{
lean_dec(x_122);
lean_dec(x_110);
lean_dec(x_11);
lean_dec(x_2);
x_111 = x_5;
goto block_121;
}
}
else
{
lean_dec(x_110);
lean_dec(x_108);
lean_dec(x_11);
lean_dec(x_2);
x_111 = x_5;
goto block_121;
}
block_121:
{
lean_object* x_112; 
x_112 = l_Lean_Server_RequestM_checkCancelled(x_111, x_109);
lean_dec(x_111);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_113 = lean_ctor_get(x_112, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 x_114 = x_112;
} else {
 lean_dec_ref(x_112);
 x_114 = lean_box(0);
}
x_115 = lean_mk_empty_array_with_capacity(x_7);
if (lean_is_scalar(x_114)) {
 x_116 = lean_alloc_ctor(0, 2, 0);
} else {
 x_116 = x_114;
}
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_113);
return x_116;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_117 = lean_ctor_get(x_112, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_112, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 x_119 = x_112;
} else {
 lean_dec_ref(x_112);
 x_119 = lean_box(0);
}
if (lean_is_scalar(x_119)) {
 x_120 = lean_alloc_ctor(1, 2, 0);
} else {
 x_120 = x_119;
}
lean_ctor_set(x_120, 0, x_117);
lean_ctor_set(x_120, 1, x_118);
return x_120;
}
}
}
}
else
{
lean_object* x_163; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_163 = lean_mk_empty_array_with_capacity(x_7);
lean_ctor_set(x_9, 0, x_163);
return x_9;
}
}
else
{
lean_object* x_164; lean_object* x_165; uint8_t x_166; 
x_164 = lean_ctor_get(x_9, 0);
x_165 = lean_ctor_get(x_9, 1);
lean_inc(x_165);
lean_inc(x_164);
lean_dec(x_9);
x_166 = l_Array_isEmpty___redArg(x_164);
if (x_166 == 0)
{
lean_object* x_167; size_t x_168; size_t x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_167 = lean_mk_string_unchecked("$/lean/queryModule", 18, 18);
x_168 = lean_array_size(x_164);
x_169 = lean_usize_of_nat(x_7);
lean_inc(x_164);
x_170 = l_Array_mapMUnsafe_map___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2(x_168, x_169, x_164);
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_1);
lean_ctor_set(x_171, 1, x_170);
lean_inc(x_5);
x_172 = l_Lean_Server_RequestM_sendServerRequest___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__3___redArg(x_167, x_171, x_5, x_165);
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
x_176 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lam__0), 1, 0);
x_177 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lam__1), 1, 0);
x_178 = l_Lean_Server_ServerTask_mapCheap___redArg(x_177, x_173);
x_179 = lean_ctor_get(x_5, 4);
lean_inc(x_179);
x_180 = l_Lean_Server_RequestCancellationToken_requestCancellationTask(x_179);
lean_dec(x_179);
x_181 = l_Lean_Server_ServerTask_mapCheap___redArg(x_176, x_180);
x_182 = lean_box(0);
if (lean_is_scalar(x_175)) {
 x_183 = lean_alloc_ctor(1, 2, 0);
} else {
 x_183 = x_175;
 lean_ctor_set_tag(x_183, 1);
}
lean_ctor_set(x_183, 0, x_181);
lean_ctor_set(x_183, 1, x_182);
x_184 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_184, 0, x_178);
lean_ctor_set(x_184, 1, x_183);
x_185 = l_Lean_Server_ServerTask_waitAny___redArg(x_184, x_174);
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_185, 1);
lean_inc(x_187);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 lean_ctor_release(x_185, 1);
 x_188 = x_185;
} else {
 lean_dec_ref(x_185);
 x_188 = lean_box(0);
}
if (lean_obj_tag(x_186) == 0)
{
lean_object* x_200; 
x_200 = lean_ctor_get(x_186, 0);
lean_inc(x_200);
lean_dec(x_186);
if (lean_obj_tag(x_200) == 0)
{
lean_object* x_201; lean_object* x_202; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_201 = lean_ctor_get(x_200, 0);
lean_inc(x_201);
lean_dec(x_200);
x_227 = lean_ctor_get(x_5, 1);
lean_inc(x_227);
x_228 = lean_ctor_get(x_227, 0);
lean_inc(x_228);
lean_dec(x_227);
x_229 = lean_ctor_get(x_228, 1);
lean_inc(x_229);
x_230 = lean_ctor_get(x_229, 2);
lean_inc(x_230);
lean_dec(x_229);
x_231 = l_Lean_Syntax_getTailPos_x3f(x_230, x_166);
lean_dec(x_230);
if (lean_obj_tag(x_231) == 0)
{
lean_object* x_232; 
lean_dec(x_228);
x_232 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_232, 0, x_7);
lean_ctor_set(x_232, 1, x_7);
x_202 = x_232;
goto block_226;
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_233 = lean_ctor_get(x_231, 0);
lean_inc(x_233);
lean_dec(x_231);
x_234 = lean_ctor_get(x_228, 0);
lean_inc(x_234);
lean_dec(x_228);
x_235 = lean_ctor_get(x_234, 3);
lean_inc(x_235);
lean_dec(x_234);
x_236 = l_Lean_FileMap_utf8PosToLspPos(x_235, x_233);
lean_dec(x_233);
x_237 = lean_ctor_get(x_236, 0);
lean_inc(x_237);
lean_dec(x_236);
x_238 = lean_unsigned_to_nat(1u);
x_239 = lean_nat_add(x_237, x_238);
lean_dec(x_237);
x_240 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_240, 0, x_239);
lean_ctor_set(x_240, 1, x_7);
x_202 = x_240;
goto block_226;
}
block_226:
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; uint8_t x_214; 
lean_inc(x_202);
if (lean_is_scalar(x_188)) {
 x_203 = lean_alloc_ctor(0, 2, 0);
} else {
 x_203 = x_188;
}
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set(x_203, 1, x_202);
x_204 = lean_mk_empty_array_with_capacity(x_7);
x_205 = lean_array_get_size(x_201);
x_206 = l_Array_toSubarray___redArg(x_201, x_7, x_205);
x_207 = lean_box(x_166);
x_208 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_204);
x_209 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_209, 0, x_206);
lean_ctor_set(x_209, 1, x_208);
x_210 = l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__5(x_5, x_203, x_166, x_164, x_168, x_169, x_209, x_5, x_187);
lean_dec(x_164);
lean_dec(x_5);
x_211 = lean_ctor_get(x_210, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_211, 1);
lean_inc(x_212);
lean_dec(x_211);
x_213 = lean_ctor_get(x_212, 0);
lean_inc(x_213);
x_214 = lean_unbox(x_213);
lean_dec(x_213);
if (x_214 == 0)
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
lean_dec(x_2);
x_215 = lean_ctor_get(x_210, 1);
lean_inc(x_215);
if (lean_is_exclusive(x_210)) {
 lean_ctor_release(x_210, 0);
 lean_ctor_release(x_210, 1);
 x_216 = x_210;
} else {
 lean_dec_ref(x_210);
 x_216 = lean_box(0);
}
x_217 = lean_ctor_get(x_212, 1);
lean_inc(x_217);
lean_dec(x_212);
if (lean_is_scalar(x_216)) {
 x_218 = lean_alloc_ctor(0, 2, 0);
} else {
 x_218 = x_216;
}
lean_ctor_set(x_218, 0, x_217);
lean_ctor_set(x_218, 1, x_215);
return x_218;
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_219 = lean_ctor_get(x_210, 1);
lean_inc(x_219);
if (lean_is_exclusive(x_210)) {
 lean_ctor_release(x_210, 0);
 lean_ctor_release(x_210, 1);
 x_220 = x_210;
} else {
 lean_dec_ref(x_210);
 x_220 = lean_box(0);
}
x_221 = lean_ctor_get(x_212, 1);
lean_inc(x_221);
lean_dec(x_212);
x_222 = lean_mk_string_unchecked("quickfix", 8, 8);
x_223 = l_Lean_Server_FileWorker_importAllUnknownIdentifiersCodeAction(x_2, x_222);
x_224 = lean_array_push(x_221, x_223);
if (lean_is_scalar(x_220)) {
 x_225 = lean_alloc_ctor(0, 2, 0);
} else {
 x_225 = x_220;
}
lean_ctor_set(x_225, 0, x_224);
lean_ctor_set(x_225, 1, x_219);
return x_225;
}
}
}
else
{
lean_dec(x_200);
lean_dec(x_188);
lean_dec(x_164);
lean_dec(x_2);
x_189 = x_5;
goto block_199;
}
}
else
{
lean_dec(x_188);
lean_dec(x_186);
lean_dec(x_164);
lean_dec(x_2);
x_189 = x_5;
goto block_199;
}
block_199:
{
lean_object* x_190; 
x_190 = l_Lean_Server_RequestM_checkCancelled(x_189, x_187);
lean_dec(x_189);
if (lean_obj_tag(x_190) == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_191 = lean_ctor_get(x_190, 1);
lean_inc(x_191);
if (lean_is_exclusive(x_190)) {
 lean_ctor_release(x_190, 0);
 lean_ctor_release(x_190, 1);
 x_192 = x_190;
} else {
 lean_dec_ref(x_190);
 x_192 = lean_box(0);
}
x_193 = lean_mk_empty_array_with_capacity(x_7);
if (lean_is_scalar(x_192)) {
 x_194 = lean_alloc_ctor(0, 2, 0);
} else {
 x_194 = x_192;
}
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_194, 1, x_191);
return x_194;
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_195 = lean_ctor_get(x_190, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_190, 1);
lean_inc(x_196);
if (lean_is_exclusive(x_190)) {
 lean_ctor_release(x_190, 0);
 lean_ctor_release(x_190, 1);
 x_197 = x_190;
} else {
 lean_dec_ref(x_190);
 x_197 = lean_box(0);
}
if (lean_is_scalar(x_197)) {
 x_198 = lean_alloc_ctor(1, 2, 0);
} else {
 x_198 = x_197;
}
lean_ctor_set(x_198, 0, x_195);
lean_ctor_set(x_198, 1, x_196);
return x_198;
}
}
}
else
{
lean_object* x_241; lean_object* x_242; 
lean_dec(x_164);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_241 = lean_mk_empty_array_with_capacity(x_7);
x_242 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_242, 0, x_241);
lean_ctor_set(x_242, 1, x_165);
return x_242;
}
}
}
else
{
uint8_t x_243; 
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_243 = !lean_is_exclusive(x_9);
if (x_243 == 0)
{
return x_9;
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; 
x_244 = lean_ctor_get(x_9, 0);
x_245 = lean_ctor_get(x_9, 1);
lean_inc(x_245);
lean_inc(x_244);
lean_dec(x_9);
x_246 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_246, 0, x_244);
lean_ctor_set(x_246, 1, x_245);
return x_246;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_10 = l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__0_spec__0___redArg(x_1, x_2, x_3, x_8, x_9, x_6, x_7);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_11 = l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__0_spec__0(x_1, x_2, x_3, x_9, x_10, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_filterMapM___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_sendServerRequest___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Server_RequestM_sendServerRequest___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__4___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__4___redArg___lam__0(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_12 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_13 = l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__4___redArg(x_1, x_2, x_3, x_10, x_5, x_11, x_12, x_8, x_9);
lean_dec(x_5);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_13 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_14 = l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__4(x_1, x_2, x_3, x_11, x_5, x_12, x_13, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__5_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_12 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_13 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__5_spec__5(x_1, x_2, x_10, x_4, x_11, x_12, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_12 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_13 = l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__5(x_1, x_2, x_10, x_4, x_11, x_12, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_usize_dec_eq(x_3, x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_10, 3);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_array_uget(x_2, x_3);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_string_utf8_byte_size(x_14);
lean_dec(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_Server_FileWorker_computeQuery_x3f___redArg(x_7, x_16, x_12, x_6);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
if (lean_obj_tag(x_18) == 0)
{
x_20 = x_5;
goto block_25;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_18, 0);
lean_inc(x_26);
lean_dec(x_18);
x_27 = lean_array_push(x_5, x_26);
x_20 = x_27;
goto block_25;
}
block_25:
{
lean_object* x_21; size_t x_22; size_t x_23; 
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_usize_of_nat(x_21);
x_23 = lean_usize_add(x_3, x_22);
x_3 = x_23;
x_5 = x_20;
x_6 = x_19;
goto _start;
}
}
else
{
uint8_t x_28; 
lean_dec(x_5);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_17);
if (x_28 == 0)
{
return x_17;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_17, 0);
x_30 = lean_ctor_get(x_17, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_17);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
lean_object* x_32; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_5);
lean_ctor_set(x_32, 1, x_6);
return x_32;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__0_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_mk_empty_array_with_capacity(x_7);
x_9 = lean_nat_dec_lt(x_3, x_4);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_6);
return x_10;
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_get_size(x_2);
x_12 = lean_nat_dec_le(x_4, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_6);
return x_13;
}
else
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_usize_of_nat(x_3);
x_15 = lean_usize_of_nat(x_4);
x_16 = l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__0_spec__0___redArg(x_1, x_2, x_14, x_15, x_8, x_6);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_5, x_4);
if (x_7 == 0)
{
lean_dec(x_2);
return x_6;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_21; 
lean_dec(x_6);
x_8 = lean_box(0);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_array_uget(x_3, x_5);
x_21 = lean_ctor_get_uint8(x_11, sizeof(void*)*2);
if (x_21 == 0)
{
x_12 = x_1;
goto block_20;
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_2, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_11, 1);
lean_inc(x_23);
x_24 = l_Lean_Environment_contains(x_22, x_23, x_21);
if (x_24 == 0)
{
x_12 = x_21;
goto block_20;
}
else
{
x_12 = x_1;
goto block_20;
}
}
block_20:
{
if (x_12 == 0)
{
lean_object* x_13; size_t x_14; size_t x_15; 
lean_dec(x_11);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_usize_of_nat(x_13);
x_15 = lean_usize_add(x_5, x_14);
x_5 = x_15;
x_6 = x_10;
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_10);
lean_dec(x_2);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_11);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_9);
return x_19;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__3_spec__3___redArg___lam__0(uint8_t x_1, lean_object* x_2) {
_start:
{
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__3_spec__3___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_15; 
x_15 = lean_usize_dec_lt(x_5, x_4);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_2);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_6);
lean_ctor_set(x_16, 1, x_7);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_17 = lean_ctor_get(x_6, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_6, 1);
lean_inc(x_18);
lean_dec(x_6);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_17, 2);
lean_inc(x_22);
x_23 = lean_nat_dec_lt(x_21, x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_2);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_19);
lean_ctor_set(x_24, 1, x_20);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_17);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_7);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_42; lean_object* x_43; lean_object* x_44; size_t x_45; lean_object* x_46; size_t x_47; lean_object* x_48; lean_object* x_49; 
x_27 = lean_array_uget(x_3, x_5);
x_28 = lean_ctor_get(x_17, 0);
lean_inc(x_28);
lean_dec(x_17);
x_29 = lean_array_fget(x_28, x_21);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_21, x_30);
lean_dec(x_21);
x_32 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_32, 0, x_28);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_32, 2, x_22);
x_42 = lean_box(0);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_array_size(x_29);
x_46 = lean_unsigned_to_nat(0u);
x_47 = lean_usize_of_nat(x_46);
lean_inc(x_27);
x_48 = l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2(x_1, x_27, x_29, x_45, x_47, x_44);
lean_dec(x_29);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
lean_dec(x_48);
if (lean_obj_tag(x_49) == 0)
{
lean_dec(x_27);
goto block_41;
}
else
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
lean_dec(x_49);
if (lean_obj_tag(x_50) == 0)
{
lean_dec(x_27);
goto block_41;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
lean_dec(x_50);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = lean_ctor_get(x_27, 1);
lean_inc(x_54);
x_55 = l_Lean_Environment_mainModule(x_54);
lean_dec(x_54);
x_56 = lean_name_eq(x_52, x_55);
lean_dec(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_112; lean_object* x_122; uint64_t x_123; lean_object* x_124; uint64_t x_125; uint64_t x_126; uint64_t x_127; lean_object* x_128; uint64_t x_129; uint64_t x_130; uint64_t x_131; size_t x_132; size_t x_133; size_t x_134; size_t x_135; size_t x_136; lean_object* x_137; uint8_t x_138; 
x_57 = lean_ctor_get(x_27, 2);
lean_inc(x_57);
lean_dec(x_27);
x_58 = lean_ctor_get(x_20, 1);
lean_inc(x_58);
x_59 = lean_box(x_56);
x_60 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__3_spec__3___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_60, 0, x_59);
x_61 = lean_apply_1(x_57, x_53);
x_122 = lean_array_get_size(x_58);
x_123 = l_Lean_Name_hash___override(x_52);
x_124 = lean_unsigned_to_nat(32u);
x_125 = lean_uint64_of_nat(x_124);
x_126 = lean_uint64_shift_right(x_123, x_125);
x_127 = lean_uint64_xor(x_123, x_126);
x_128 = lean_unsigned_to_nat(16u);
x_129 = lean_uint64_of_nat(x_128);
x_130 = lean_uint64_shift_right(x_127, x_129);
x_131 = lean_uint64_xor(x_127, x_130);
x_132 = lean_uint64_to_usize(x_131);
x_133 = lean_usize_of_nat(x_122);
lean_dec(x_122);
x_134 = lean_usize_of_nat(x_30);
x_135 = lean_usize_sub(x_133, x_134);
x_136 = lean_usize_land(x_132, x_135);
x_137 = lean_array_uget(x_58, x_136);
lean_dec(x_58);
x_138 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Std_Data_DHashMap_Internal_RawLemmas_0__Std_DHashMap_Internal_Raw_u2080_modifyMap_spec__0___redArg(x_52, x_137);
lean_dec(x_137);
if (x_138 == 0)
{
x_112 = x_23;
goto block_121;
}
else
{
if (x_56 == 0)
{
lean_dec(x_60);
x_62 = x_19;
x_63 = x_20;
x_64 = x_7;
goto block_111;
}
else
{
x_112 = x_56;
goto block_121;
}
}
block_111:
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint64_t x_70; lean_object* x_71; uint64_t x_72; uint64_t x_73; uint64_t x_74; lean_object* x_75; uint64_t x_76; uint64_t x_77; uint64_t x_78; size_t x_79; size_t x_80; size_t x_81; size_t x_82; size_t x_83; lean_object* x_84; uint8_t x_85; 
x_65 = lean_ctor_get(x_63, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_63, 1);
lean_inc(x_66);
x_67 = lean_ctor_get(x_61, 1);
lean_inc(x_67);
lean_dec(x_61);
x_68 = lean_array_push(x_62, x_67);
x_69 = lean_array_get_size(x_66);
x_70 = l_Lean_Name_hash___override(x_52);
x_71 = lean_unsigned_to_nat(32u);
x_72 = lean_uint64_of_nat(x_71);
x_73 = lean_uint64_shift_right(x_70, x_72);
x_74 = lean_uint64_xor(x_70, x_73);
x_75 = lean_unsigned_to_nat(16u);
x_76 = lean_uint64_of_nat(x_75);
x_77 = lean_uint64_shift_right(x_74, x_76);
x_78 = lean_uint64_xor(x_74, x_77);
x_79 = lean_uint64_to_usize(x_78);
x_80 = lean_usize_of_nat(x_69);
lean_dec(x_69);
x_81 = lean_usize_of_nat(x_30);
x_82 = lean_usize_sub(x_80, x_81);
x_83 = lean_usize_land(x_79, x_82);
x_84 = lean_array_uget(x_66, x_83);
x_85 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Std_Data_DHashMap_Internal_RawLemmas_0__Std_DHashMap_Internal_Raw_u2080_modifyMap_spec__0___redArg(x_52, x_84);
if (x_85 == 0)
{
uint8_t x_86; 
x_86 = !lean_is_exclusive(x_63);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_87 = lean_ctor_get(x_63, 1);
lean_dec(x_87);
x_88 = lean_ctor_get(x_63, 0);
lean_dec(x_88);
x_89 = lean_nat_add(x_65, x_30);
lean_dec(x_65);
x_90 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_90, 0, x_52);
lean_ctor_set(x_90, 1, x_43);
lean_ctor_set(x_90, 2, x_84);
x_91 = lean_array_uset(x_66, x_83, x_90);
x_92 = lean_unsigned_to_nat(2u);
x_93 = lean_nat_shiftl(x_89, x_92);
x_94 = lean_unsigned_to_nat(3u);
x_95 = lean_nat_div(x_93, x_94);
lean_dec(x_93);
x_96 = lean_array_get_size(x_91);
x_97 = lean_nat_dec_le(x_95, x_96);
lean_dec(x_96);
lean_dec(x_95);
if (x_97 == 0)
{
lean_object* x_98; 
x_98 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Std_Data_DHashMap_Internal_RawLemmas_0__Std_DHashMap_Internal_Raw_u2080_modifyMap_spec__1___redArg(x_91);
lean_ctor_set(x_63, 1, x_98);
lean_ctor_set(x_63, 0, x_89);
x_33 = x_64;
x_34 = x_68;
x_35 = x_63;
goto block_38;
}
else
{
lean_ctor_set(x_63, 1, x_91);
lean_ctor_set(x_63, 0, x_89);
x_33 = x_64;
x_34 = x_68;
x_35 = x_63;
goto block_38;
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; 
lean_dec(x_63);
x_99 = lean_nat_add(x_65, x_30);
lean_dec(x_65);
x_100 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_100, 0, x_52);
lean_ctor_set(x_100, 1, x_43);
lean_ctor_set(x_100, 2, x_84);
x_101 = lean_array_uset(x_66, x_83, x_100);
x_102 = lean_unsigned_to_nat(2u);
x_103 = lean_nat_shiftl(x_99, x_102);
x_104 = lean_unsigned_to_nat(3u);
x_105 = lean_nat_div(x_103, x_104);
lean_dec(x_103);
x_106 = lean_array_get_size(x_101);
x_107 = lean_nat_dec_le(x_105, x_106);
lean_dec(x_106);
lean_dec(x_105);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; 
x_108 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Std_Data_DHashMap_Internal_RawLemmas_0__Std_DHashMap_Internal_Raw_u2080_modifyMap_spec__1___redArg(x_101);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_99);
lean_ctor_set(x_109, 1, x_108);
x_33 = x_64;
x_34 = x_68;
x_35 = x_109;
goto block_38;
}
else
{
lean_object* x_110; 
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_99);
lean_ctor_set(x_110, 1, x_101);
x_33 = x_64;
x_34 = x_68;
x_35 = x_110;
goto block_38;
}
}
}
else
{
lean_dec(x_84);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_52);
x_33 = x_64;
x_34 = x_68;
x_35 = x_63;
goto block_38;
}
}
block_121:
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_113 = lean_mk_string_unchecked("import ", 7, 7);
lean_inc(x_52);
x_114 = l_Lean_Name_toString(x_52, x_112, x_60);
x_115 = lean_string_append(x_113, x_114);
lean_dec(x_114);
x_116 = lean_mk_string_unchecked("\n", 1, 1);
x_117 = lean_string_append(x_115, x_116);
lean_dec(x_116);
x_118 = lean_box(0);
lean_inc(x_2);
x_119 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_119, 0, x_2);
lean_ctor_set(x_119, 1, x_117);
lean_ctor_set(x_119, 2, x_118);
lean_ctor_set(x_119, 3, x_118);
x_120 = lean_array_push(x_19, x_119);
x_62 = x_120;
x_63 = x_20;
x_64 = x_7;
goto block_111;
}
}
else
{
lean_object* x_139; lean_object* x_140; 
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_27);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_19);
lean_ctor_set(x_139, 1, x_20);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_32);
lean_ctor_set(x_140, 1, x_139);
x_8 = x_140;
x_9 = x_7;
goto block_14;
}
}
}
block_38:
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_32);
lean_ctor_set(x_37, 1, x_36);
x_8 = x_37;
x_9 = x_33;
goto block_14;
}
block_41:
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_19);
lean_ctor_set(x_39, 1, x_20);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_32);
lean_ctor_set(x_40, 1, x_39);
x_8 = x_40;
x_9 = x_7;
goto block_14;
}
}
}
block_14:
{
lean_object* x_10; size_t x_11; size_t x_12; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_usize_of_nat(x_10);
x_12 = lean_usize_add(x_5, x_11);
x_5 = x_12;
x_6 = x_8;
x_7 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__3_spec__3(uint8_t x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__3_spec__3___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__3(uint8_t x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_16; 
x_16 = lean_usize_dec_lt(x_5, x_4);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_2);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_6);
lean_ctor_set(x_17, 1, x_8);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_18 = lean_ctor_get(x_6, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_6, 1);
lean_inc(x_19);
lean_dec(x_6);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_18, 2);
lean_inc(x_23);
x_24 = lean_nat_dec_lt(x_22, x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_2);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_25, 1, x_21);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_18);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_8);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_43; lean_object* x_44; lean_object* x_45; size_t x_46; lean_object* x_47; size_t x_48; lean_object* x_49; lean_object* x_50; 
x_28 = lean_array_uget(x_3, x_5);
x_29 = lean_ctor_get(x_18, 0);
lean_inc(x_29);
lean_dec(x_18);
x_30 = lean_array_fget(x_29, x_22);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_add(x_22, x_31);
lean_dec(x_22);
x_33 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_33, 0, x_29);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_33, 2, x_23);
x_43 = lean_box(0);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_array_size(x_30);
x_47 = lean_unsigned_to_nat(0u);
x_48 = lean_usize_of_nat(x_47);
lean_inc(x_28);
x_49 = l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2(x_1, x_28, x_30, x_46, x_48, x_45);
lean_dec(x_30);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
lean_dec(x_49);
if (lean_obj_tag(x_50) == 0)
{
lean_dec(x_28);
goto block_42;
}
else
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
lean_dec(x_50);
if (lean_obj_tag(x_51) == 0)
{
lean_dec(x_28);
goto block_42;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
lean_dec(x_51);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_ctor_get(x_28, 1);
lean_inc(x_55);
x_56 = l_Lean_Environment_mainModule(x_55);
lean_dec(x_55);
x_57 = lean_name_eq(x_53, x_56);
lean_dec(x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_113; lean_object* x_123; uint64_t x_124; lean_object* x_125; uint64_t x_126; uint64_t x_127; uint64_t x_128; lean_object* x_129; uint64_t x_130; uint64_t x_131; uint64_t x_132; size_t x_133; size_t x_134; size_t x_135; size_t x_136; size_t x_137; lean_object* x_138; uint8_t x_139; 
x_58 = lean_ctor_get(x_28, 2);
lean_inc(x_58);
lean_dec(x_28);
x_59 = lean_ctor_get(x_21, 1);
lean_inc(x_59);
x_60 = lean_box(x_57);
x_61 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__3_spec__3___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_61, 0, x_60);
x_62 = lean_apply_1(x_58, x_54);
x_123 = lean_array_get_size(x_59);
x_124 = l_Lean_Name_hash___override(x_53);
x_125 = lean_unsigned_to_nat(32u);
x_126 = lean_uint64_of_nat(x_125);
x_127 = lean_uint64_shift_right(x_124, x_126);
x_128 = lean_uint64_xor(x_124, x_127);
x_129 = lean_unsigned_to_nat(16u);
x_130 = lean_uint64_of_nat(x_129);
x_131 = lean_uint64_shift_right(x_128, x_130);
x_132 = lean_uint64_xor(x_128, x_131);
x_133 = lean_uint64_to_usize(x_132);
x_134 = lean_usize_of_nat(x_123);
lean_dec(x_123);
x_135 = lean_usize_of_nat(x_31);
x_136 = lean_usize_sub(x_134, x_135);
x_137 = lean_usize_land(x_133, x_136);
x_138 = lean_array_uget(x_59, x_137);
lean_dec(x_59);
x_139 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Std_Data_DHashMap_Internal_RawLemmas_0__Std_DHashMap_Internal_Raw_u2080_modifyMap_spec__0___redArg(x_53, x_138);
lean_dec(x_138);
if (x_139 == 0)
{
x_113 = x_24;
goto block_122;
}
else
{
if (x_57 == 0)
{
lean_dec(x_61);
x_63 = x_20;
x_64 = x_21;
x_65 = x_8;
goto block_112;
}
else
{
x_113 = x_57;
goto block_122;
}
}
block_112:
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint64_t x_71; lean_object* x_72; uint64_t x_73; uint64_t x_74; uint64_t x_75; lean_object* x_76; uint64_t x_77; uint64_t x_78; uint64_t x_79; size_t x_80; size_t x_81; size_t x_82; size_t x_83; size_t x_84; lean_object* x_85; uint8_t x_86; 
x_66 = lean_ctor_get(x_64, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_64, 1);
lean_inc(x_67);
x_68 = lean_ctor_get(x_62, 1);
lean_inc(x_68);
lean_dec(x_62);
x_69 = lean_array_push(x_63, x_68);
x_70 = lean_array_get_size(x_67);
x_71 = l_Lean_Name_hash___override(x_53);
x_72 = lean_unsigned_to_nat(32u);
x_73 = lean_uint64_of_nat(x_72);
x_74 = lean_uint64_shift_right(x_71, x_73);
x_75 = lean_uint64_xor(x_71, x_74);
x_76 = lean_unsigned_to_nat(16u);
x_77 = lean_uint64_of_nat(x_76);
x_78 = lean_uint64_shift_right(x_75, x_77);
x_79 = lean_uint64_xor(x_75, x_78);
x_80 = lean_uint64_to_usize(x_79);
x_81 = lean_usize_of_nat(x_70);
lean_dec(x_70);
x_82 = lean_usize_of_nat(x_31);
x_83 = lean_usize_sub(x_81, x_82);
x_84 = lean_usize_land(x_80, x_83);
x_85 = lean_array_uget(x_67, x_84);
x_86 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Std_Data_DHashMap_Internal_RawLemmas_0__Std_DHashMap_Internal_Raw_u2080_modifyMap_spec__0___redArg(x_53, x_85);
if (x_86 == 0)
{
uint8_t x_87; 
x_87 = !lean_is_exclusive(x_64);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_88 = lean_ctor_get(x_64, 1);
lean_dec(x_88);
x_89 = lean_ctor_get(x_64, 0);
lean_dec(x_89);
x_90 = lean_nat_add(x_66, x_31);
lean_dec(x_66);
x_91 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_91, 0, x_53);
lean_ctor_set(x_91, 1, x_44);
lean_ctor_set(x_91, 2, x_85);
x_92 = lean_array_uset(x_67, x_84, x_91);
x_93 = lean_unsigned_to_nat(2u);
x_94 = lean_nat_shiftl(x_90, x_93);
x_95 = lean_unsigned_to_nat(3u);
x_96 = lean_nat_div(x_94, x_95);
lean_dec(x_94);
x_97 = lean_array_get_size(x_92);
x_98 = lean_nat_dec_le(x_96, x_97);
lean_dec(x_97);
lean_dec(x_96);
if (x_98 == 0)
{
lean_object* x_99; 
x_99 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Std_Data_DHashMap_Internal_RawLemmas_0__Std_DHashMap_Internal_Raw_u2080_modifyMap_spec__1___redArg(x_92);
lean_ctor_set(x_64, 1, x_99);
lean_ctor_set(x_64, 0, x_90);
x_34 = x_69;
x_35 = x_65;
x_36 = x_64;
goto block_39;
}
else
{
lean_ctor_set(x_64, 1, x_92);
lean_ctor_set(x_64, 0, x_90);
x_34 = x_69;
x_35 = x_65;
x_36 = x_64;
goto block_39;
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; 
lean_dec(x_64);
x_100 = lean_nat_add(x_66, x_31);
lean_dec(x_66);
x_101 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_101, 0, x_53);
lean_ctor_set(x_101, 1, x_44);
lean_ctor_set(x_101, 2, x_85);
x_102 = lean_array_uset(x_67, x_84, x_101);
x_103 = lean_unsigned_to_nat(2u);
x_104 = lean_nat_shiftl(x_100, x_103);
x_105 = lean_unsigned_to_nat(3u);
x_106 = lean_nat_div(x_104, x_105);
lean_dec(x_104);
x_107 = lean_array_get_size(x_102);
x_108 = lean_nat_dec_le(x_106, x_107);
lean_dec(x_107);
lean_dec(x_106);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; 
x_109 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Std_Data_DHashMap_Internal_RawLemmas_0__Std_DHashMap_Internal_Raw_u2080_modifyMap_spec__1___redArg(x_102);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_100);
lean_ctor_set(x_110, 1, x_109);
x_34 = x_69;
x_35 = x_65;
x_36 = x_110;
goto block_39;
}
else
{
lean_object* x_111; 
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_100);
lean_ctor_set(x_111, 1, x_102);
x_34 = x_69;
x_35 = x_65;
x_36 = x_111;
goto block_39;
}
}
}
else
{
lean_dec(x_85);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_53);
x_34 = x_69;
x_35 = x_65;
x_36 = x_64;
goto block_39;
}
}
block_122:
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_114 = lean_mk_string_unchecked("import ", 7, 7);
lean_inc(x_53);
x_115 = l_Lean_Name_toString(x_53, x_113, x_61);
x_116 = lean_string_append(x_114, x_115);
lean_dec(x_115);
x_117 = lean_mk_string_unchecked("\n", 1, 1);
x_118 = lean_string_append(x_116, x_117);
lean_dec(x_117);
x_119 = lean_box(0);
lean_inc(x_2);
x_120 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_120, 0, x_2);
lean_ctor_set(x_120, 1, x_118);
lean_ctor_set(x_120, 2, x_119);
lean_ctor_set(x_120, 3, x_119);
x_121 = lean_array_push(x_20, x_120);
x_63 = x_121;
x_64 = x_21;
x_65 = x_8;
goto block_112;
}
}
else
{
lean_object* x_140; lean_object* x_141; 
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_28);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_20);
lean_ctor_set(x_140, 1, x_21);
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_33);
lean_ctor_set(x_141, 1, x_140);
x_9 = x_141;
x_10 = x_8;
goto block_15;
}
}
}
block_39:
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_33);
lean_ctor_set(x_38, 1, x_37);
x_9 = x_38;
x_10 = x_35;
goto block_15;
}
block_42:
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_20);
lean_ctor_set(x_40, 1, x_21);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_33);
lean_ctor_set(x_41, 1, x_40);
x_9 = x_41;
x_10 = x_8;
goto block_15;
}
}
}
block_15:
{
lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_usize_of_nat(x_11);
x_13 = lean_usize_add(x_5, x_12);
x_14 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__3_spec__3___redArg(x_1, x_2, x_3, x_4, x_13, x_9, x_10);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_get_size(x_3);
lean_inc(x_4);
x_8 = l_Array_filterMapM___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__0(x_4, x_3, x_6, x_7, x_4, x_5);
lean_dec(x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = l_Array_isEmpty___redArg(x_10);
if (x_12 == 0)
{
lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
lean_free_object(x_8);
x_13 = lean_mk_string_unchecked("$/lean/queryModule", 18, 18);
x_14 = lean_array_size(x_10);
x_15 = lean_usize_of_nat(x_6);
lean_inc(x_10);
x_16 = l_Array_mapMUnsafe_map___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2(x_14, x_15, x_10);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_16);
lean_inc(x_4);
x_18 = l_Lean_Server_RequestM_sendServerRequest___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__3___redArg(x_13, x_17, x_4, x_11);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
x_22 = lean_task_get_own(x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_free_object(x_18);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 x_24 = x_22;
} else {
 lean_dec_ref(x_22);
 x_24 = lean_box(0);
}
x_25 = lean_ctor_get(x_4, 1);
lean_inc(x_25);
x_100 = lean_ctor_get(x_25, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_100, 1);
lean_inc(x_101);
x_102 = lean_ctor_get(x_101, 2);
lean_inc(x_102);
lean_dec(x_101);
x_103 = l_Lean_Syntax_getTailPos_x3f(x_102, x_12);
lean_dec(x_102);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; 
lean_dec(x_100);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_6);
lean_ctor_set(x_104, 1, x_6);
x_26 = x_104;
goto block_99;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_105 = lean_ctor_get(x_103, 0);
lean_inc(x_105);
lean_dec(x_103);
x_106 = lean_ctor_get(x_100, 0);
lean_inc(x_106);
lean_dec(x_100);
x_107 = lean_ctor_get(x_106, 3);
lean_inc(x_107);
lean_dec(x_106);
x_108 = l_Lean_FileMap_utf8PosToLspPos(x_107, x_105);
lean_dec(x_105);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
lean_dec(x_108);
x_110 = lean_unsigned_to_nat(1u);
x_111 = lean_nat_add(x_109, x_110);
lean_dec(x_109);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_6);
x_26 = x_112;
goto block_99;
}
block_99:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
lean_inc(x_26);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_mk_empty_array_with_capacity(x_6);
x_29 = lean_unsigned_to_nat(8u);
x_30 = lean_unsigned_to_nat(2u);
x_31 = lean_nat_shiftl(x_29, x_30);
x_32 = lean_unsigned_to_nat(3u);
x_33 = lean_nat_div(x_31, x_32);
lean_dec(x_31);
x_34 = l_Nat_nextPowerOfTwo(x_33);
lean_dec(x_33);
x_35 = lean_box(0);
x_36 = lean_mk_array(x_34, x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_6);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_array_get_size(x_23);
x_39 = l_Array_toSubarray___redArg(x_23, x_6, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_28);
lean_ctor_set(x_40, 1, x_37);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__3(x_12, x_27, x_10, x_14, x_15, x_41, x_4, x_21);
lean_dec(x_4);
lean_dec(x_10);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
x_45 = !lean_is_exclusive(x_42);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_ctor_get(x_42, 0);
lean_dec(x_46);
x_47 = !lean_is_exclusive(x_44);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_48 = lean_ctor_get(x_44, 0);
x_49 = lean_ctor_get(x_44, 1);
lean_dec(x_49);
x_50 = lean_ctor_get(x_2, 0);
x_51 = lean_ctor_get(x_2, 1);
x_52 = lean_ctor_get(x_2, 2);
x_53 = lean_ctor_get(x_2, 3);
x_54 = lean_ctor_get(x_2, 4);
x_55 = lean_ctor_get(x_2, 5);
x_56 = lean_ctor_get(x_2, 6);
x_57 = l_Lean_Server_FileWorker_EditableDocument_versionedIdentifier(x_25);
lean_dec(x_25);
lean_ctor_set(x_44, 1, x_48);
lean_ctor_set(x_44, 0, x_57);
x_58 = l_Lean_Lsp_WorkspaceEdit_ofTextDocumentEdit(x_44);
if (lean_is_scalar(x_24)) {
 x_59 = lean_alloc_ctor(1, 1, 0);
} else {
 x_59 = x_24;
 lean_ctor_set_tag(x_59, 1);
}
lean_ctor_set(x_59, 0, x_58);
x_60 = lean_ctor_get(x_2, 8);
x_61 = lean_ctor_get(x_2, 9);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
x_62 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_62, 0, x_50);
lean_ctor_set(x_62, 1, x_51);
lean_ctor_set(x_62, 2, x_52);
lean_ctor_set(x_62, 3, x_53);
lean_ctor_set(x_62, 4, x_54);
lean_ctor_set(x_62, 5, x_55);
lean_ctor_set(x_62, 6, x_56);
lean_ctor_set(x_62, 7, x_59);
lean_ctor_set(x_62, 8, x_60);
lean_ctor_set(x_62, 9, x_61);
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_42, 0, x_63);
return x_42;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_64 = lean_ctor_get(x_44, 0);
lean_inc(x_64);
lean_dec(x_44);
x_65 = lean_ctor_get(x_2, 0);
x_66 = lean_ctor_get(x_2, 1);
x_67 = lean_ctor_get(x_2, 2);
x_68 = lean_ctor_get(x_2, 3);
x_69 = lean_ctor_get(x_2, 4);
x_70 = lean_ctor_get(x_2, 5);
x_71 = lean_ctor_get(x_2, 6);
x_72 = l_Lean_Server_FileWorker_EditableDocument_versionedIdentifier(x_25);
lean_dec(x_25);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_64);
x_74 = l_Lean_Lsp_WorkspaceEdit_ofTextDocumentEdit(x_73);
if (lean_is_scalar(x_24)) {
 x_75 = lean_alloc_ctor(1, 1, 0);
} else {
 x_75 = x_24;
 lean_ctor_set_tag(x_75, 1);
}
lean_ctor_set(x_75, 0, x_74);
x_76 = lean_ctor_get(x_2, 8);
x_77 = lean_ctor_get(x_2, 9);
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
x_78 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_78, 0, x_65);
lean_ctor_set(x_78, 1, x_66);
lean_ctor_set(x_78, 2, x_67);
lean_ctor_set(x_78, 3, x_68);
lean_ctor_set(x_78, 4, x_69);
lean_ctor_set(x_78, 5, x_70);
lean_ctor_set(x_78, 6, x_71);
lean_ctor_set(x_78, 7, x_75);
lean_ctor_set(x_78, 8, x_76);
lean_ctor_set(x_78, 9, x_77);
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_42, 0, x_79);
return x_42;
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_80 = lean_ctor_get(x_42, 1);
lean_inc(x_80);
lean_dec(x_42);
x_81 = lean_ctor_get(x_44, 0);
lean_inc(x_81);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_82 = x_44;
} else {
 lean_dec_ref(x_44);
 x_82 = lean_box(0);
}
x_83 = lean_ctor_get(x_2, 0);
x_84 = lean_ctor_get(x_2, 1);
x_85 = lean_ctor_get(x_2, 2);
x_86 = lean_ctor_get(x_2, 3);
x_87 = lean_ctor_get(x_2, 4);
x_88 = lean_ctor_get(x_2, 5);
x_89 = lean_ctor_get(x_2, 6);
x_90 = l_Lean_Server_FileWorker_EditableDocument_versionedIdentifier(x_25);
lean_dec(x_25);
if (lean_is_scalar(x_82)) {
 x_91 = lean_alloc_ctor(0, 2, 0);
} else {
 x_91 = x_82;
}
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_81);
x_92 = l_Lean_Lsp_WorkspaceEdit_ofTextDocumentEdit(x_91);
if (lean_is_scalar(x_24)) {
 x_93 = lean_alloc_ctor(1, 1, 0);
} else {
 x_93 = x_24;
 lean_ctor_set_tag(x_93, 1);
}
lean_ctor_set(x_93, 0, x_92);
x_94 = lean_ctor_get(x_2, 8);
x_95 = lean_ctor_get(x_2, 9);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
x_96 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_96, 0, x_83);
lean_ctor_set(x_96, 1, x_84);
lean_ctor_set(x_96, 2, x_85);
lean_ctor_set(x_96, 3, x_86);
lean_ctor_set(x_96, 4, x_87);
lean_ctor_set(x_96, 5, x_88);
lean_ctor_set(x_96, 6, x_89);
lean_ctor_set(x_96, 7, x_93);
lean_ctor_set(x_96, 8, x_94);
lean_ctor_set(x_96, 9, x_95);
x_97 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_97, 0, x_96);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_80);
return x_98;
}
}
}
else
{
lean_object* x_113; 
lean_dec(x_22);
lean_dec(x_10);
lean_dec(x_4);
x_113 = lean_box(0);
lean_ctor_set(x_18, 0, x_113);
return x_18;
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_18, 0);
x_115 = lean_ctor_get(x_18, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_18);
x_116 = lean_task_get_own(x_114);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 x_118 = x_116;
} else {
 lean_dec_ref(x_116);
 x_118 = lean_box(0);
}
x_119 = lean_ctor_get(x_4, 1);
lean_inc(x_119);
x_160 = lean_ctor_get(x_119, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_160, 1);
lean_inc(x_161);
x_162 = lean_ctor_get(x_161, 2);
lean_inc(x_162);
lean_dec(x_161);
x_163 = l_Lean_Syntax_getTailPos_x3f(x_162, x_12);
lean_dec(x_162);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; 
lean_dec(x_160);
x_164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_164, 0, x_6);
lean_ctor_set(x_164, 1, x_6);
x_120 = x_164;
goto block_159;
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_165 = lean_ctor_get(x_163, 0);
lean_inc(x_165);
lean_dec(x_163);
x_166 = lean_ctor_get(x_160, 0);
lean_inc(x_166);
lean_dec(x_160);
x_167 = lean_ctor_get(x_166, 3);
lean_inc(x_167);
lean_dec(x_166);
x_168 = l_Lean_FileMap_utf8PosToLspPos(x_167, x_165);
lean_dec(x_165);
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
lean_dec(x_168);
x_170 = lean_unsigned_to_nat(1u);
x_171 = lean_nat_add(x_169, x_170);
lean_dec(x_169);
x_172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_6);
x_120 = x_172;
goto block_159;
}
block_159:
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
lean_inc(x_120);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_120);
x_122 = lean_mk_empty_array_with_capacity(x_6);
x_123 = lean_unsigned_to_nat(8u);
x_124 = lean_unsigned_to_nat(2u);
x_125 = lean_nat_shiftl(x_123, x_124);
x_126 = lean_unsigned_to_nat(3u);
x_127 = lean_nat_div(x_125, x_126);
lean_dec(x_125);
x_128 = l_Nat_nextPowerOfTwo(x_127);
lean_dec(x_127);
x_129 = lean_box(0);
x_130 = lean_mk_array(x_128, x_129);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_6);
lean_ctor_set(x_131, 1, x_130);
x_132 = lean_array_get_size(x_117);
x_133 = l_Array_toSubarray___redArg(x_117, x_6, x_132);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_122);
lean_ctor_set(x_134, 1, x_131);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
x_136 = l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__3(x_12, x_121, x_10, x_14, x_15, x_135, x_4, x_115);
lean_dec(x_4);
lean_dec(x_10);
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_137, 1);
lean_inc(x_138);
lean_dec(x_137);
x_139 = lean_ctor_get(x_136, 1);
lean_inc(x_139);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_140 = x_136;
} else {
 lean_dec_ref(x_136);
 x_140 = lean_box(0);
}
x_141 = lean_ctor_get(x_138, 0);
lean_inc(x_141);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_142 = x_138;
} else {
 lean_dec_ref(x_138);
 x_142 = lean_box(0);
}
x_143 = lean_ctor_get(x_2, 0);
x_144 = lean_ctor_get(x_2, 1);
x_145 = lean_ctor_get(x_2, 2);
x_146 = lean_ctor_get(x_2, 3);
x_147 = lean_ctor_get(x_2, 4);
x_148 = lean_ctor_get(x_2, 5);
x_149 = lean_ctor_get(x_2, 6);
x_150 = l_Lean_Server_FileWorker_EditableDocument_versionedIdentifier(x_119);
lean_dec(x_119);
if (lean_is_scalar(x_142)) {
 x_151 = lean_alloc_ctor(0, 2, 0);
} else {
 x_151 = x_142;
}
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_141);
x_152 = l_Lean_Lsp_WorkspaceEdit_ofTextDocumentEdit(x_151);
if (lean_is_scalar(x_118)) {
 x_153 = lean_alloc_ctor(1, 1, 0);
} else {
 x_153 = x_118;
 lean_ctor_set_tag(x_153, 1);
}
lean_ctor_set(x_153, 0, x_152);
x_154 = lean_ctor_get(x_2, 8);
x_155 = lean_ctor_get(x_2, 9);
lean_inc(x_155);
lean_inc(x_154);
lean_inc(x_149);
lean_inc(x_148);
lean_inc(x_147);
lean_inc(x_146);
lean_inc(x_145);
lean_inc(x_144);
lean_inc(x_143);
x_156 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_156, 0, x_143);
lean_ctor_set(x_156, 1, x_144);
lean_ctor_set(x_156, 2, x_145);
lean_ctor_set(x_156, 3, x_146);
lean_ctor_set(x_156, 4, x_147);
lean_ctor_set(x_156, 5, x_148);
lean_ctor_set(x_156, 6, x_149);
lean_ctor_set(x_156, 7, x_153);
lean_ctor_set(x_156, 8, x_154);
lean_ctor_set(x_156, 9, x_155);
x_157 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_157, 0, x_156);
if (lean_is_scalar(x_140)) {
 x_158 = lean_alloc_ctor(0, 2, 0);
} else {
 x_158 = x_140;
}
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_139);
return x_158;
}
}
else
{
lean_object* x_173; lean_object* x_174; 
lean_dec(x_116);
lean_dec(x_10);
lean_dec(x_4);
x_173 = lean_box(0);
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_115);
return x_174;
}
}
}
else
{
lean_object* x_175; 
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_1);
x_175 = lean_box(0);
lean_ctor_set(x_8, 0, x_175);
return x_8;
}
}
else
{
lean_object* x_176; lean_object* x_177; uint8_t x_178; 
x_176 = lean_ctor_get(x_8, 0);
x_177 = lean_ctor_get(x_8, 1);
lean_inc(x_177);
lean_inc(x_176);
lean_dec(x_8);
x_178 = l_Array_isEmpty___redArg(x_176);
if (x_178 == 0)
{
lean_object* x_179; size_t x_180; size_t x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_179 = lean_mk_string_unchecked("$/lean/queryModule", 18, 18);
x_180 = lean_array_size(x_176);
x_181 = lean_usize_of_nat(x_6);
lean_inc(x_176);
x_182 = l_Array_mapMUnsafe_map___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2(x_180, x_181, x_176);
x_183 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_183, 0, x_1);
lean_ctor_set(x_183, 1, x_182);
lean_inc(x_4);
x_184 = l_Lean_Server_RequestM_sendServerRequest___at___Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__3___redArg(x_179, x_183, x_4, x_177);
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_184, 1);
lean_inc(x_186);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 lean_ctor_release(x_184, 1);
 x_187 = x_184;
} else {
 lean_dec_ref(x_184);
 x_187 = lean_box(0);
}
x_188 = lean_task_get_own(x_185);
if (lean_obj_tag(x_188) == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
lean_dec(x_187);
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 x_190 = x_188;
} else {
 lean_dec_ref(x_188);
 x_190 = lean_box(0);
}
x_191 = lean_ctor_get(x_4, 1);
lean_inc(x_191);
x_232 = lean_ctor_get(x_191, 0);
lean_inc(x_232);
x_233 = lean_ctor_get(x_232, 1);
lean_inc(x_233);
x_234 = lean_ctor_get(x_233, 2);
lean_inc(x_234);
lean_dec(x_233);
x_235 = l_Lean_Syntax_getTailPos_x3f(x_234, x_178);
lean_dec(x_234);
if (lean_obj_tag(x_235) == 0)
{
lean_object* x_236; 
lean_dec(x_232);
x_236 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_236, 0, x_6);
lean_ctor_set(x_236, 1, x_6);
x_192 = x_236;
goto block_231;
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_237 = lean_ctor_get(x_235, 0);
lean_inc(x_237);
lean_dec(x_235);
x_238 = lean_ctor_get(x_232, 0);
lean_inc(x_238);
lean_dec(x_232);
x_239 = lean_ctor_get(x_238, 3);
lean_inc(x_239);
lean_dec(x_238);
x_240 = l_Lean_FileMap_utf8PosToLspPos(x_239, x_237);
lean_dec(x_237);
x_241 = lean_ctor_get(x_240, 0);
lean_inc(x_241);
lean_dec(x_240);
x_242 = lean_unsigned_to_nat(1u);
x_243 = lean_nat_add(x_241, x_242);
lean_dec(x_241);
x_244 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_244, 0, x_243);
lean_ctor_set(x_244, 1, x_6);
x_192 = x_244;
goto block_231;
}
block_231:
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
lean_inc(x_192);
x_193 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_192);
x_194 = lean_mk_empty_array_with_capacity(x_6);
x_195 = lean_unsigned_to_nat(8u);
x_196 = lean_unsigned_to_nat(2u);
x_197 = lean_nat_shiftl(x_195, x_196);
x_198 = lean_unsigned_to_nat(3u);
x_199 = lean_nat_div(x_197, x_198);
lean_dec(x_197);
x_200 = l_Nat_nextPowerOfTwo(x_199);
lean_dec(x_199);
x_201 = lean_box(0);
x_202 = lean_mk_array(x_200, x_201);
x_203 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_203, 0, x_6);
lean_ctor_set(x_203, 1, x_202);
x_204 = lean_array_get_size(x_189);
x_205 = l_Array_toSubarray___redArg(x_189, x_6, x_204);
x_206 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_206, 0, x_194);
lean_ctor_set(x_206, 1, x_203);
x_207 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_207, 0, x_205);
lean_ctor_set(x_207, 1, x_206);
x_208 = l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__3(x_178, x_193, x_176, x_180, x_181, x_207, x_4, x_186);
lean_dec(x_4);
lean_dec(x_176);
x_209 = lean_ctor_get(x_208, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_209, 1);
lean_inc(x_210);
lean_dec(x_209);
x_211 = lean_ctor_get(x_208, 1);
lean_inc(x_211);
if (lean_is_exclusive(x_208)) {
 lean_ctor_release(x_208, 0);
 lean_ctor_release(x_208, 1);
 x_212 = x_208;
} else {
 lean_dec_ref(x_208);
 x_212 = lean_box(0);
}
x_213 = lean_ctor_get(x_210, 0);
lean_inc(x_213);
if (lean_is_exclusive(x_210)) {
 lean_ctor_release(x_210, 0);
 lean_ctor_release(x_210, 1);
 x_214 = x_210;
} else {
 lean_dec_ref(x_210);
 x_214 = lean_box(0);
}
x_215 = lean_ctor_get(x_2, 0);
x_216 = lean_ctor_get(x_2, 1);
x_217 = lean_ctor_get(x_2, 2);
x_218 = lean_ctor_get(x_2, 3);
x_219 = lean_ctor_get(x_2, 4);
x_220 = lean_ctor_get(x_2, 5);
x_221 = lean_ctor_get(x_2, 6);
x_222 = l_Lean_Server_FileWorker_EditableDocument_versionedIdentifier(x_191);
lean_dec(x_191);
if (lean_is_scalar(x_214)) {
 x_223 = lean_alloc_ctor(0, 2, 0);
} else {
 x_223 = x_214;
}
lean_ctor_set(x_223, 0, x_222);
lean_ctor_set(x_223, 1, x_213);
x_224 = l_Lean_Lsp_WorkspaceEdit_ofTextDocumentEdit(x_223);
if (lean_is_scalar(x_190)) {
 x_225 = lean_alloc_ctor(1, 1, 0);
} else {
 x_225 = x_190;
 lean_ctor_set_tag(x_225, 1);
}
lean_ctor_set(x_225, 0, x_224);
x_226 = lean_ctor_get(x_2, 8);
x_227 = lean_ctor_get(x_2, 9);
lean_inc(x_227);
lean_inc(x_226);
lean_inc(x_221);
lean_inc(x_220);
lean_inc(x_219);
lean_inc(x_218);
lean_inc(x_217);
lean_inc(x_216);
lean_inc(x_215);
x_228 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_228, 0, x_215);
lean_ctor_set(x_228, 1, x_216);
lean_ctor_set(x_228, 2, x_217);
lean_ctor_set(x_228, 3, x_218);
lean_ctor_set(x_228, 4, x_219);
lean_ctor_set(x_228, 5, x_220);
lean_ctor_set(x_228, 6, x_221);
lean_ctor_set(x_228, 7, x_225);
lean_ctor_set(x_228, 8, x_226);
lean_ctor_set(x_228, 9, x_227);
x_229 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_229, 0, x_228);
if (lean_is_scalar(x_212)) {
 x_230 = lean_alloc_ctor(0, 2, 0);
} else {
 x_230 = x_212;
}
lean_ctor_set(x_230, 0, x_229);
lean_ctor_set(x_230, 1, x_211);
return x_230;
}
}
else
{
lean_object* x_245; lean_object* x_246; 
lean_dec(x_188);
lean_dec(x_176);
lean_dec(x_4);
x_245 = lean_box(0);
if (lean_is_scalar(x_187)) {
 x_246 = lean_alloc_ctor(0, 2, 0);
} else {
 x_246 = x_187;
}
lean_ctor_set(x_246, 0, x_245);
lean_ctor_set(x_246, 1, x_186);
return x_246;
}
}
else
{
lean_object* x_247; lean_object* x_248; 
lean_dec(x_176);
lean_dec(x_4);
lean_dec(x_1);
x_247 = lean_box(0);
x_248 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_248, 0, x_247);
lean_ctor_set(x_248, 1, x_177);
return x_248;
}
}
}
else
{
uint8_t x_249; 
lean_dec(x_4);
lean_dec(x_1);
x_249 = !lean_is_exclusive(x_8);
if (x_249 == 0)
{
return x_8;
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_250 = lean_ctor_get(x_8, 0);
x_251 = lean_ctor_get(x_8, 1);
lean_inc(x_251);
lean_inc(x_250);
lean_dec(x_8);
x_252 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_252, 0, x_250);
lean_ctor_set(x_252, 1, x_251);
return x_252;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__0_spec__0___redArg(x_1, x_2, x_7, x_8, x_5, x_6);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__0_spec__0(x_1, x_2, x_8, x_9, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_filterMapM___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; size_t x_8; size_t x_9; lean_object* x_10; 
x_7 = lean_unbox(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_10 = l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2(x_7, x_2, x_3, x_8, x_9, x_6);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__3_spec__3___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__3_spec__3___redArg___lam__0(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__3_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_8 = lean_unbox(x_1);
lean_dec(x_1);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_11 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__3_spec__3___redArg(x_8, x_2, x_3, x_9, x_10, x_6, x_7);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__3_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_12 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__3_spec__3(x_9, x_2, x_3, x_10, x_11, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_12 = l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__3(x_9, x_2, x_3, x_10, x_11, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
lean_object* initialize_Lean_Server_FileWorker_Utils(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Lsp_Internal(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Server_Requests(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Server_Completion_CompletionInfoSelection(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Server_CodeActions_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Server_Completion_CompletionUtils(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Server_CodeActions_UnknownIdentifier(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Server_FileWorker_Utils(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp_Internal(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_Requests(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_Completion_CompletionInfoSelection(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_CodeActions_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_Completion_CompletionUtils(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Server_FileWorker_importAllUnknownIdentifiersProvider = _init_l_Lean_Server_FileWorker_importAllUnknownIdentifiersProvider();
lean_mark_persistent(l_Lean_Server_FileWorker_importAllUnknownIdentifiersProvider);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
