// Lean compiler output
// Module: Lean.Server.FileWorker
// Imports: Init.System.IO Std.Sync.Channel Lean.Data.RBMap Lean.Environment Lean.Data.Lsp Lean.Data.Json.FromToJson Lean.Util.FileSetupInfo Lean.LoadDynlib Lean.Language.Lean Lean.Server.Utils Lean.Server.AsyncList Lean.Server.References Lean.Server.FileWorker.Utils Lean.Server.FileWorker.RequestHandling Lean.Server.FileWorker.WidgetRequests Lean.Server.FileWorker.SetupFile Lean.Server.Rpc.Basic Lean.Widget.InteractiveDiagnostic Lean.Server.Completion.ImportCompletion Lean.Server.CodeActions.UnknownIdentifier
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
lean_object* l_Lean_JsonNumber_fromNat(lean_object*);
lean_object* l_Lean_Server_FileWorker_RpcSession_new(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_updateDocument(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Language_Lean_process(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleImportCompletionRequest___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_WorkerContext_initPendingServerRequest___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FileMap_lspRangeToUtf8Range(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_Server_FileWorker_mainLoop_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_setupImports___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ImportCompletion_collectAvailableImports(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleRpcRelease_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_sendFileProgress_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___IO_FS_Stream_readRequestAs___at___IO_FS_Stream_readLspRequestAs___at___Lean_Server_FileWorker_initAndRunWorker_spec__0_spec__0_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readNotificationAs___at___IO_FS_Stream_readLspNotificationAs___at___Lean_Server_FileWorker_initAndRunWorker_spec__9_spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_WorkerContext_modifyGetPartialHandler___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handlePostRequestSpecialCases___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Lsp_Extra_0__Lean_Lsp_fromJsonRpcConnectParams____x40_Lean_Data_Lsp_Extra___hyg_1992_(lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___Lean_Server_FileWorker_handlePostRequestSpecialCases_spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Server_handleOnDidChange(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_cancel(lean_object*, lean_object*);
lean_object* l_Lean_Server_FileWorker_setupFile(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Server_FileWorker_runRefreshTasks_spec__3_spec__3___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handlePreRequestSpecialCases_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Channel_forAsync___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_handleFinished_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Server_FileWorker_runRefreshTasks_spec__3_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___at___Lean_Server_FileWorker_mainLoop_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleResponse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleRequest___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_initAndRunWorker_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_JsonNumber_toString(lean_object*);
lean_object* l_Lean_Json_toStructured_x3f___at___IO_FS_Stream_writeLspRequest___at___Lean_Lsp_Ipc_shutdown_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_server_reportDelayMs;
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_sendFileProgress_spec__6___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_Server_FileWorker_queueRequest_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_Server_FileWorker_handleRpcConnect_spec__0_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Lsp_Extra_0__Lean_Lsp_toJsonLeanFileProgressParams____x40_Lean_Data_Lsp_Extra___hyg_1231_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___at___Lean_Server_FileWorker_mainLoop_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleRpcConnect___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Language_SnapshotTask_get___redArg(lean_object*);
lean_object* l_EIO_ofExcept(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
lean_object* l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_initAndRunWorker_spec__11___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Language_Lean_Types_0__Lean_Language_Lean_pushOpt___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Server_FileWorker_handlePreRequestSpecialCases_x3f_spec__6(size_t, size_t, lean_object*, lean_object*);
lean_object* lean_io_check_canceled(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleResponse___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_Server_FileWorker_initializeWorker_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_sendFileProgress_spec__3(size_t, size_t, lean_object*);
lean_object* l___private_Lean_Data_Lsp_Diagnostics_0__Lean_Lsp_fromJsonPublishDiagnosticsParams____x40_Lean_Data_Lsp_Diagnostics___hyg_2484_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at___Lean_Server_FileWorker_handleDidChange_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___redArg(lean_object*);
lean_object* lean_io_promise_new(lean_object*);
lean_object* l_IO_CancelToken_isSet(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_sendServerRequest(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_sendFileProgress_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleRpcRelease___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleRequest___lam__0___boxed(lean_object*);
lean_object* l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_fromJsonClientInfo____x40_Lean_Data_Lsp_InitShutdown___hyg_70_(lean_object*);
LEAN_EXPORT uint8_t l_Array_qsort_sort___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_sendFileProgress_spec__6___redArg___lam__0(lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Lsp_Diagnostics_0__Lean_Lsp_toJsonDiagnosticRelatedInformation____x40_Lean_Data_Lsp_Diagnostics___hyg_1088_(lean_object*);
lean_object* l_Lean_Widget_InteractiveDiagnostic_toDiagnostic(lean_object*);
lean_object* l_Lean_Server_ServerTask_IO_mapTaskCostly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_sendFileProgress_spec__6___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_setupImports___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_handleNode___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___IO_FS_Stream_readRequestAs___at___IO_FS_Stream_readLspRequestAs___at___Lean_Server_FileWorker_initAndRunWorker_spec__0_spec__0_spec__5___boxed(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Server_mkFileProgressNotification(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_handleFinished_spec__0(lean_object*, size_t, size_t, lean_object*);
lean_object* l_List_forIn_x27_loop___at___Lean_KVMap_mergeBy_spec__0___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Server_FileWorker_importAllUnknownIdentifiersProvider;
uint8_t lean_uint64_dec_lt(uint64_t, uint64_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_setupImports___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_updateDocument___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___Lean_Server_FileWorker_initializeWorker_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_rpcReleaseRef(size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleNotification(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Server_FileWorker_WorkerContext_modifyGetPartialHandler_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleRpcRelease___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_ServerTask_IO_mapTaskCheap___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_initializeWorker_mkLspOutputChannel(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_updatePendingRequests___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___Lean_Server_FileWorker_WorkerContext_resolveServerRequestResponse_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleStatefulPreRequestSpecialCases___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_setupImports___lam__4___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Widget_instRpcEncodableDiagnosticWith_enc____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853____at___Lean_Server_FileWorker_handlePreRequestSpecialCases_x3f_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2299_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_Server_FileWorker_handleRpcConnect_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_setBlack___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Server_FileWorker_initializeWorker_spec__0(lean_object*, size_t, size_t, lean_object*);
lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanStaleDependencyParams____x40_Lean_Data_Lsp_Internal___hyg_2481_(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Server_FileWorker_handlePostRequestSpecialCases_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_runRefreshTasks_spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_RequestM_mapRequestTaskCostly___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleCancelRequest___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_WorkerContext_initPendingServerRequest(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_ordRequestID____x40_Lean_Data_JsonRpc___hyg_126_(lean_object*, lean_object*);
lean_object* l_Lean_Server_ServerTask_mapCheap___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Server_FileWorker_waitUnknownIdentifierRanges(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleResponse___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_runRefreshTasks_spec__5_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_parseParams___at___Lean_Server_FileWorker_handleStatefulPreRequestSpecialCases_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_initializeWorker_mkLspOutputChannel___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_sendUntypedServerRequest(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_sendFileProgress_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handlePreRequestSpecialCases_x3f___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_runRefreshTasks___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleStaleDependency___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_WorkerContext_initPendingServerRequest___at___Lean_Server_FileWorker_sendServerRequest___at___Lean_Server_FileWorker_runRefreshTasks_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_Promise_result_x21___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_sendFileProgress_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_handleNode_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_updatePendingRequests___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handlePostRequestSpecialCases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleResponseError___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_publishDiagnostics(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_WorkerContext_initPendingServerRequest___at___Lean_Server_FileWorker_sendServerRequest___at___Lean_Server_FileWorker_sendUntypedServerRequest_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_server_worker_main(lean_object*, lean_object*);
lean_object* l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Array_contains___at___Lean_Server_FileWorker_handlePostRequestSpecialCases_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_emitRequestResponse___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_updatePendingRequests___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at___Lean_Server_FileWorker_queueRequest_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_initializeWorker_getImportClosure_x3f(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lean_Server_RequestM_checkCancelled(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspRequestAs___at___Lean_Server_FileWorker_initAndRunWorker_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_WorkerContext_initPendingServerRequest___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Lsp_Capabilities_0__Lean_Lsp_fromJsonClientCapabilities____x40_Lean_Data_Lsp_Capabilities___hyg_1347_(lean_object*);
lean_object* l_Lean_Server_RequestCancellationToken_cancelByEdit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleGetInteractiveDiagnosticsRequest___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_balRight(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_mkPublishDiagnosticsNotification(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_Server_FileWorker_handleCancelRequest_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_mainLoop(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_mkIleanInfoNotification___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_sendFileProgress_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_RequestM_parseRequestParams___at___Lean_Server_registerLspRequestHandler___at___Lean_Server_initFn____x40_Lean_Server_CodeActions_Basic___hyg_1538__spec__0_spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_String_crlfToLf(lean_object*);
lean_object* lean_get_stdout(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Server_FileWorker_runRefreshTasks_spec__3_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_publishDiagnostics_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleNotification___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_partialLspRequestHandlerMethods(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleRpcKeepAlive(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_Server_FileWorker_handleRpcConnect_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_ofExcept___at___IO_Process_output_spec__0___redArg(lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Lsp_LanguageFeatures_0__Lean_Lsp_toJsonCompletionList____x40_Lean_Data_Lsp_LanguageFeatures___hyg_2889_(lean_object*);
lean_object* l_Lean_Server_findModuleRefs(lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleDidChange___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_handleFinished_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Lsp_CodeActions_0__Lean_Lsp_toJsonCodeAction____x40_Lean_Data_Lsp_CodeActions___hyg_1131_(lean_object*);
lean_object* l_Lean_Lsp_DiagnosticWith_fullRange(lean_object*, lean_object*);
lean_object* l_Std_CloseableChannel_new___redArg(lean_object*, lean_object*);
lean_object* lean_io_promise_resolve(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker___hyg_753_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at___Lean_Server_FileWorker_handleRpcConnect_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_WorkerContext_modifyPartialHandler(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleCancelRequest(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleRequest(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_enc____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853____at___Lean_Server_FileWorker_handlePreRequestSpecialCases_x3f_spec__2(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Array_contains___at___Lean_Server_FileWorker_handlePostRequestSpecialCases_spec__1_spec__1(lean_object*, lean_object*, size_t, size_t);
lean_object* l_IO_CancelToken_new(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_initializeWorker(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_mono_ms_now(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Server_FileWorker_runRefreshTasks_spec__3_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_task_pure(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_WorkerContext_initPendingServerRequest___redArg___lam__0(lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Lsp_Extra_0__Lean_Lsp_fromJsonRpcKeepAliveParams____x40_Lean_Data_Lsp_Extra___hyg_2827_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleCancelRequest___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_appendTrees___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleImportCompletionRequest___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_mkIleanInfoFinalNotification___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Lsp_LanguageFeatures_0__Lean_Lsp_fromJsonCompletionParams____x40_Lean_Data_Lsp_LanguageFeatures___hyg_2953_(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_runRefreshTasks_spec__5_spec__5___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_sendFileProgress_spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_initializeWorker___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_JsonNumber_fromInt(lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_parseParams___at___Lean_Server_FileWorker_handleStatefulPreRequestSpecialCases_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_sendServerRequest___at___Lean_Server_FileWorker_sendUntypedServerRequest_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_Server_FileWorker_handleRpcConnect_spec__0_spec__0___redArg(lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_WorkerContext_initPendingServerRequest___at___Lean_Server_FileWorker_sendServerRequest___at___Lean_Server_FileWorker_runRefreshTasks_spec__0_spec__0___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Server_FileWorker_runRefreshTasks_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Server_FileWorker_runRefreshTasks_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_handleTasks_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_initAndRunWorker_writeErrorDiag(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_Server_FileWorker_mainLoop_spec__0_spec__0(lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_handleFinished(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleStaleDependency(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Server_FileWorker_runRefreshTasks_spec__3_spec__3___redArg___lam__1(lean_object*, uint8_t, lean_object*);
lean_object* l_Std_Channel_Sync_send___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_initAndRunWorker_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_documentUriFromModule_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_sendFileProgress(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at___Lean_Server_FileWorker_handleCancelRequest_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleImportCompletionRequest___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_emitRequestResponse___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t lean_uint32_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleResponseError(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Prod_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_queueRequest___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_WorkerContext_initPendingServerRequest___at___Lean_Server_FileWorker_sendServerRequest___at___Lean_Server_FileWorker_sendUntypedServerRequest_spec__0_spec__0___redArg___lam__0(lean_object*);
lean_object* l_IO_FS_Stream_readLspMessage(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_mkIleanInfoUpdateNotification(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_parseParams___at___Lean_Server_FileWorker_handleStatefulPreRequestSpecialCases_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___IO_FS_Stream_readRequestAs___at___IO_FS_Stream_readLspRequestAs___at___Lean_Server_FileWorker_initAndRunWorker_spec__0_spec__0_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_updatePendingRequests(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleResponseError___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Widget_instRpcEncodableMsgEmbed_enc____x40_Lean_Widget_InteractiveDiagnostic___hyg_570_(lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
uint8_t l_ImportCompletion_isImportCompletionRequest(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_WorkerContext_initPendingServerRequest___at___Lean_Server_FileWorker_sendServerRequest___at___Lean_Server_FileWorker_runRefreshTasks_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_setupImports___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleRpcKeepAlive___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_WorkerContext_initPendingServerRequest___at___Lean_Server_FileWorker_sendServerRequest___at___Lean_Server_FileWorker_sendUntypedServerRequest_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_FileWorker_RpcSession_keptAlive(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___IO_FS_Stream_readRequestAs___at___IO_FS_Stream_readLspRequestAs___at___Lean_Server_FileWorker_initAndRunWorker_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Lsp_Diagnostics_0__Lean_Lsp_toJsonPublishDiagnosticsParams____x40_Lean_Data_Lsp_Diagnostics___hyg_2428_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_WorkerContext_resolveServerRequestResponse(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_wait_any(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_sendFileProgress_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_handleTasks_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT uint8_t l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_Server_FileWorker_handleRpcConnect_spec__0_spec__0___redArg___lam__0(uint64_t, uint64_t);
lean_object* l_Lean_Option_register___at___Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Options___hyg_5__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Server_FileWorker_runRefreshTasks_sleepWithCancellation_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___Lean_Server_FileWorker_handlePreRequestSpecialCases_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Lsp_instFromJsonCancelParams;
lean_object* l_IO_CancelToken_set(lean_object*, lean_object*);
lean_object* l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps(lean_object*);
lean_object* l_Lean_Server_mkFileProgressAtPosNotification(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_handleFinished_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_async;
lean_object* l_IO_sleep(uint32_t, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___Lean_Server_FileWorker_initializeWorker_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_setupImports___lam__2(uint8_t, lean_object*);
lean_object* l_Lean_Language_mkIncrementalProcessor(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FileMap_ofString(lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_Lean_Language_SnapshotTask_finished(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleImportCompletionRequest(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_initializeWorker___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_parseParams___at___Lean_Server_FileWorker_handleStatefulPreRequestSpecialCases_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_WorkerContext_initPendingServerRequest___at___Lean_Server_FileWorker_sendServerRequest___at___Lean_Server_FileWorker_runRefreshTasks_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FileMap_utf8PosToLspPos(lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Window_0__fromJsonShowMessageParams____x40_Lean_Data_Lsp_Window___hyg_139__spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Server_DocumentMeta_mkInputContext(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_sendServerRequest___at___Lean_Server_FileWorker_runRefreshTasks_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_sendFileProgress_spec__5(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_Server_FileWorker_queueRequest_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_WorkerContext_resolveServerRequestResponse___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_RequestM_asTask___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_runRefreshTasks_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_get_stdin(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_initializeWorker_mkLspOutputChannel___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_JsonRpc_instInhabitedMessage;
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___at___Lean_Server_FileWorker_handleCancelRequest_spec__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_get_stderr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___IO_FS_Stream_readRequestAs___at___IO_FS_Stream_readLspRequestAs___at___Lean_Server_FileWorker_initAndRunWorker_spec__0_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___Lean_Server_FileWorker_handlePreRequestSpecialCases_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_Server_FileWorker_handleRpcConnect_spec__0_spec__0(lean_object*, lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Server_FileWorker_runRefreshTasks_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___Lean_Server_FileWorker_handlePreRequestSpecialCases_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Language_diagnosticsOfHeaderError(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_handleNode___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_find___at___Lean_Server_wrapRpcProcedure___at___Lean_Server_registerBuiltinRpcProcedure___at___Lean_Widget_initFn____x40_Lean_Server_FileWorker_WidgetRequests___hyg_394__spec__0_spec__0_spec__0___redArg(lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at___Lean_Server_FileWorker_handleCancelRequest_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_WorkerContext_modifyGetPartialHandler___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Widget_instRpcEncodableDiagnosticWith_enc____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853____at___Lean_Server_FileWorker_handlePreRequestSpecialCases_x3f_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Json_getObjValAs_x3f___at___IO_FS_Stream_readRequestAs___at___IO_FS_Stream_readLspRequestAs___at___Lean_Server_FileWorker_initAndRunWorker_spec__0_spec__0_spec__5_spec__5(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_handleNode___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_MessageLog_hasUnreported(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_runRefreshTasks(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanImportClosureParams____x40_Lean_Data_Lsp_Internal___hyg_2431_(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_publishDiagnostics_spec__0(size_t, size_t, lean_object*);
lean_object* l_Lean_Server_RequestCancellationToken_cancelByCancelRequest(lean_object*, lean_object*);
lean_object* l_Lean_Server_RequestError_toLspResponseError(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleRpcRelease(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_WorkerContext_updateRequestsInFlight(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_queueRequest___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handlePreRequestSpecialCases_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleRpcConnect___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_handleNode_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Server_RequestError_rpcNeedsReconnect;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handlePreRequestSpecialCases_x3f___lam__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_sendFileProgress_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___at___Lean_Server_FileWorker_mainLoop_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handlePreRequestSpecialCases_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_get_set_stderr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleDidChange(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___IO_FS_Stream_readRequestAs___at___IO_FS_Stream_readLspRequestAs___at___Lean_Server_FileWorker_initAndRunWorker_spec__0_spec__0_spec__4___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Server_ServerTask_hasFinished(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___IO_FS_Stream_readRequestAs___at___IO_FS_Stream_readLspRequestAs___at___Lean_Server_FileWorker_initAndRunWorker_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspNotificationAs___at___Lean_Server_FileWorker_initAndRunWorker_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at___Lean_Server_FileWorker_handleDidChange_spec__0___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Language_Snapshot_Diagnostics_empty;
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_mkIleanInfoFinalNotification(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_handleTasks(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_opt___at_____private_Lean_Widget_InteractiveCode_0__Lean_Widget_toJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveCode___hyg_552__spec__0(lean_object*, lean_object*);
lean_object* lean_task_get_own(lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_sendFileProgress_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_HeaderSyntax_imports(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at___Lean_Server_FileWorker_handleRpcConnect_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_emitRequestResponse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_handleNode_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_RequestM_runInIO(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___IO_FS_Stream_readRequestAs___at___IO_FS_Stream_readLspRequestAs___at___Lean_Server_FileWorker_initAndRunWorker_spec__0_spec__0_spec__2(lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_handleNode_spec__2(lean_object*, size_t, size_t, lean_object*);
lean_object* l_String_Range_toLspRange(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_WorkerContext_updateRequestsInFlight___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___IO_FS_Stream_readRequestAs___at___IO_FS_Stream_readLspRequestAs___at___Lean_Server_FileWorker_initAndRunWorker_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___at___Lean_RBNode_foldM___at___Lean_Server_FileWorker_mainLoop_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_runRefreshTasks_sleepWithCancellation(uint32_t, lean_object*);
lean_object* l_Lean_Server_ModuleRefs_toLspModuleRefs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Json_getObjValAs_x3f___at___IO_FS_Stream_readRequestAs___at___IO_FS_Stream_readLspRequestAs___at___Lean_Server_FileWorker_initAndRunWorker_spec__0_spec__0_spec__5_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_emitRequestResponse___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Lsp_instFromJsonRpcReleaseParams;
lean_object* l_IO_throwServerError(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_runRefreshTasks_spec__5_spec__5___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___Lean_Server_FileWorker_WorkerContext_resolveServerRequestResponse_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Widget_instRpcEncodableDiagnosticWith_enc____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853____at___Lean_Server_FileWorker_handlePreRequestSpecialCases_x3f_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_RequestCancellationToken_wasCancelledByCancelRequest(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_setupImports(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_opt___at___IO_FS_Stream_writeMessage_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_parseParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_sendFileProgress___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_ServerTask_IO_asTask(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_readMessage(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___IO_FS_Stream_readRequestAs___at___IO_FS_Stream_readLspRequestAs___at___Lean_Server_FileWorker_initAndRunWorker_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_fromJsonInitializationOptions____x40_Lean_Data_Lsp_InitShutdown___hyg_343_(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readRequestAs___at___IO_FS_Stream_readLspRequestAs___at___Lean_Server_FileWorker_initAndRunWorker_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleStaleDependency___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_setupImports___lam__4(lean_object*);
lean_object* l_IO_FS_Stream_writeLspMessage(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonRange____x40_Lean_Data_Lsp_Basic___hyg_615_(lean_object*);
uint32_t lean_uint32_sub(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at___Lean_Server_FileWorker_mainLoop_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_WorkerContext_modifyGetPartialHandler___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleRpcRelease_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_Server_FileWorker_mainLoop_spec__0_spec__0___redArg(uint64_t, lean_object*);
uint8_t l_Lean_RBNode_isBlack___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_emitRequestResponse_emitResponse___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_handleNode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Option_set___at___Lean_Environment_realizeConst_spec__2(lean_object*, lean_object*, uint8_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___IO_FS_Stream_readRequestAs___at___IO_FS_Stream_readLspRequestAs___at___Lean_Server_FileWorker_initAndRunWorker_spec__0_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_Server_FileWorker_mainLoop_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_sendFileProgress_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_parseParams___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_mkIleanInfoNotification(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___Lean_Json_opt___at_____private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1558__spec__0_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_WorkerContext_updateRequestsInFlight___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_queueRequest(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_publishDiagnostics_spec__1(lean_object*);
lean_object* l_Lean_Server_FileWorker_RpcSession_hasExpired(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_handleTasks_spec__1(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleImportCompletionRequest___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots___lam__0(lean_object*);
lean_object* l___private_Lean_Data_Lsp_Extra_0__Lean_Lsp_fromJsonLeanDidOpenTextDocumentParams____x40_Lean_Data_Lsp_Extra___hyg_203_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_sendServerRequest___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___at___Lean_Server_FileWorker_handleCancelRequest_spec__1___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go(lean_object*);
lean_object* l_Lean_Environment_allImportedModuleNames(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_instInhabitedPartialHandlerInfo;
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___at___Lean_Server_FileWorker_mainLoop_spec__0(lean_object*, uint64_t, lean_object*);
lean_object* l_Lean_Widget_TaggedText_mapM___at___Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc____x40_Lean_Widget_InteractiveGoal___hyg_5__spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Server_FileWorker_runRefreshTasks_spec__3_spec__3___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleStaleDependency___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_WorkerContext_initPendingServerRequest___at___Lean_Server_FileWorker_sendServerRequest___at___Lean_Server_FileWorker_runRefreshTasks_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_initAndRunWorker_spec__11(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_WorkerContext_initPendingServerRequest___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at___Lean_Server_FileWorker_handleDidChange_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_get_task_state(lean_object*, lean_object*);
lean_object* l_Lean_Server_FileWorker_importAllUnknownIdentifiersCodeAction(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_parseParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handlePostRequestSpecialCases___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_exit(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at___Lean_Server_FileWorker_handleDidChange_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___Lean_Server_FileWorker_WorkerContext_initPendingServerRequest___at___Lean_Server_FileWorker_sendServerRequest___at___Lean_Server_FileWorker_sendUntypedServerRequest_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_sendServerRequest___at___Lean_Server_FileWorker_sendUntypedServerRequest_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Server_FileWorker_initializeWorker_spec__4(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Array_append(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_ServerTask_BaseIO_asTask___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_queueRequest___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleStatefulPreRequestSpecialCases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_queueRequest___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_toStructured_x3f___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Server_foldDocumentChanges(lean_object*, lean_object*);
lean_object* l_Lean_Server_RequestM_readDoc___at___Lean_Server_RequestM_withWaitFindSnapAtPos_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_instImpl____x40_Lean_Server_FileWorker___hyg_804_;
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_initializeWorker_mkLspOutputChannel___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Server_FileWorker_handleGetInteractiveDiagnosticsRequest_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_sendServerRequest___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_RBNode_isRed___redArg(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleRpcConnect(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___IO_FS_Stream_readRequestAs___at___IO_FS_Stream_readLspRequestAs___at___Lean_Server_FileWorker_initAndRunWorker_spec__0_spec__0_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Server_FileWorker_handlePostRequestSpecialCases_spec__0___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_instDecidableNot___redArg(uint8_t);
lean_object* l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___Lean_Server_registerLspRequestHandler___at___Lean_Server_initFn____x40_Lean_Server_CodeActions_Basic___hyg_1213__spec__0_spec__2(size_t, size_t, lean_object*);
lean_object* l_Lean_Server_RequestCancellationToken_new(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_WorkerContext_initPendingServerRequest___at___Lean_Server_FileWorker_sendServerRequest___at___Lean_Server_FileWorker_sendUntypedServerRequest_spec__0_spec__0___redArg___lam__0___boxed(lean_object*);
extern lean_object* l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_parseParams___at___Lean_Server_FileWorker_handleStatefulPreRequestSpecialCases_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_getNat_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_sendServerRequest___at___Lean_Server_FileWorker_runRefreshTasks_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_instInhabitedReportSnapshotsState;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_parseParams___at___Lean_Server_FileWorker_handleStatefulPreRequestSpecialCases_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_Server_FileWorker_handleCancelRequest_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleRpcConnect___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_emitRequestResponse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_WorkerContext_initPendingServerRequest___at___Lean_Server_FileWorker_sendServerRequest___at___Lean_Server_FileWorker_sendUntypedServerRequest_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at___Lean_Server_FileWorker_handleRpcConnect_spec__0(lean_object*, lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_handleNode___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_uint8_of_nat(lean_object*);
lean_object* l___private_Lean_Data_Lsp_CodeActions_0__Lean_Lsp_fromJsonCodeActionParams____x40_Lean_Data_Lsp_CodeActions___hyg_390_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handlePreRequestSpecialCases_x3f___lam__2___boxed(lean_object*, lean_object*);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___Lean_Server_FileWorker_WorkerContext_resolveServerRequestResponse_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_WorkerContext_modifyPartialHandler___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_toJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveDiagnostic___hyg_2611_(lean_object*);
lean_object* l_Std_Channel_send___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleResponseError___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Lsp_Extra_0__Lean_Lsp_fromJsonLeanFileProgressParams____x40_Lean_Data_Lsp_Extra___hyg_1125_(lean_object*);
uint8_t lean_uint32_dec_lt(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_runRefreshTasks_spec__5_spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Server_FileWorker_runRefreshTasks_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_insert___at___Lean_Json_mkObj_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Server_FileWorker_handleStaleDependency_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_instTypeNameMemorizedInteractiveDiagnostics;
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_sendFileProgress_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___at___Lean_Server_FileWorker_mainLoop_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_RBNode_find___at_____private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readRequestAs___at___IO_FS_Stream_readLspRequestAs___at___Lean_Server_FileWorker_initAndRunWorker_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_emitRequestResponse_emitResponse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_handleTasks_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Server_FileWorker_initializeWorker_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots___lam__1(lean_object*, lean_object*, uint32_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_RequestM_parseRequestParams___at___Lean_Server_registerLspRequestHandler___at___Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_409__spec__0_spec__1___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Language_SnapshotTask_map___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_IO_FS_Stream_withPrefix(lean_object*, lean_object*);
lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_ordRequestID____x40_Lean_Data_JsonRpc___hyg_126____boxed(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleRpcRelease___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_runRefreshTasks_spec__5_spec__5___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___at___Lean_Server_FileWorker_mainLoop_spec__0___redArg(uint64_t, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handlePreRequestSpecialCases_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Widget_instRpcEncodableDiagnosticWith_enc____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853____at___Lean_Server_FileWorker_handlePreRequestSpecialCases_x3f_spec__2_spec__4(size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at___Lean_Server_FileWorker_handleRpcConnect_spec__0___redArg(lean_object*, uint64_t, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Server_FileWorker_WidgetRequests_0__Lean_Widget_fromJsonGetInteractiveDiagnosticsParams____x40_Lean_Server_FileWorker_WidgetRequests___hyg_1658_(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_runRefreshTasks_spec__5_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_sendFileProgress_spec__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_appendTR(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___Lean_Server_FileWorker_handlePostRequestSpecialCases_spec__1(lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_putStrLn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_handleTasks___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_handleNode_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_runRefreshTasks_sleepWithCancellation___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2193_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___at___Lean_RBNode_foldM___at___Lean_Server_FileWorker_mainLoop_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleCancelRequest___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleImportCompletionRequest___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_WorkerContext_initPendingServerRequest___at___Lean_Server_FileWorker_sendServerRequest___at___Lean_Server_FileWorker_sendUntypedServerRequest_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at___Lean_Server_FileWorker_mainLoop_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___Lean_Server_FileWorker_WorkerContext_initPendingServerRequest___at___Lean_Server_FileWorker_sendServerRequest___at___Lean_Server_FileWorker_sendUntypedServerRequest_spec__0_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Widget_TaggedText_0__Lean_Widget_toJsonTaggedText____x40_Lean_Widget_TaggedText___hyg_621____at___Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc____x40_Lean_Widget_InteractiveGoal___hyg_5__spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handlePreRequestSpecialCases_x3f___lam__1(lean_object*);
lean_object* lean_array_get_size(lean_object*);
extern lean_object* l_Lean_Elab_inServer;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleGetInteractiveDiagnosticsRequest(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_mkFileProgressDoneNotification(lean_object*);
lean_object* l_Lean_Server_moduleFromDocumentUri(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Server_FileWorker_handlePreRequestSpecialCases_x3f_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_RequestM_parseRequestParams___at___Lean_Server_handleCodeActionResolve_spec__0___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Server_RequestError_requestCancelled;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Server_FileWorker_initializeWorker_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Server_FileWorker_handleStaleDependency_spec__0(lean_object*, size_t, size_t, lean_object*);
lean_object* lean_int_neg(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_MessageLog_toArray(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___Lean_Server_FileWorker_sendServerRequest___at___Lean_Server_FileWorker_runRefreshTasks_spec__0_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_Server_FileWorker_initializeWorker_spec__1_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Server_FileWorker_runRefreshTasks_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Widget_msgToInteractiveDiagnostic(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_initAndRunWorker(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleRpcKeepAlive___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_WorkerContext_modifyGetPartialHandler(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Widget_instRpcEncodableDiagnosticWith_enc____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853____at___Lean_Server_FileWorker_handlePreRequestSpecialCases_x3f_spec__2_spec__2(size_t, size_t, lean_object*, lean_object*);
lean_object* l_ImportCompletion_find(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_balLeft___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readNotificationAs___at___IO_FS_Stream_readLspNotificationAs___at___Lean_Server_FileWorker_initAndRunWorker_spec__9_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_emitRequestResponse_emitResponse___lam__0(uint8_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader(lean_object*, lean_object*);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
lean_object* l_Lean_Option_setIfNotSet___at___Lean_Language_Lean_process_processHeader_spec__1(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___at___Lean_RBNode_foldM___at___Lean_Server_FileWorker_mainLoop_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_emitRequestResponse_emitResponse(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams___at___Lean_Server_RequestM_parseRequestParams___at___Lean_Server_FileWorker_handlePreRequestSpecialCases_x3f_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_importsLoadedRef;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleRequest___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Lsp_Extra_0__Lean_Lsp_toJsonRpcConnected____x40_Lean_Data_Lsp_Extra___hyg_2176_(uint64_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Server_FileWorker_handleGetInteractiveDiagnosticsRequest_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_handleLspRequest(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_mkImportClosureNotification(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleRpcKeepAlive___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleResponse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Server_FileWorker_runRefreshTasks_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___Lean_Server_FileWorker_initializeWorker_spec__3(lean_object*);
lean_object* l_Lean_Widget_TaggedText_stripTags___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at___Lean_Server_FileWorker_queueRequest_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___Lean_Server_FileWorker_WorkerContext_resolveServerRequestResponse_spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_maybeTee(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Widget_instRpcEncodableDiagnosticWith_enc____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853____at___Lean_Server_FileWorker_handlePreRequestSpecialCases_x3f_spec__2_spec__3(size_t, size_t, lean_object*, lean_object*);
lean_object* l_Lean_Server_RequestError_invalidParams(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at___Lean_Server_FileWorker_mainLoop_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Lsp_ClientCapabilities_silentDiagnosticSupport(lean_object*);
lean_object* l___private_Lean_Data_Lsp_CodeActions_0__Lean_Lsp_fromJsonCodeAction____x40_Lean_Data_Lsp_CodeActions___hyg_1205_(lean_object*);
lean_object* l___private_Lean_Data_Lsp_Workspace_0__Lean_Lsp_fromJsonWorkspaceFolder____x40_Lean_Data_Lsp_Workspace___hyg_77_(lean_object*);
lean_object* l_Lean_Json_getInt_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_mkIleanInfoUpdateNotification___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker___hyg_2716_(lean_object*);
static lean_object* _init_l_Lean_Server_FileWorker_instInhabitedPartialHandlerInfo() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_mk_string_unchecked("", 0, 0);
x_2 = lean_box(0);
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Server_FileWorker_WorkerContext_modifyGetPartialHandler_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Server_FileWorker_instInhabitedPartialHandlerInfo;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_WorkerContext_modifyGetPartialHandler___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_20; 
x_5 = lean_ctor_get(x_1, 4);
x_6 = lean_st_ref_take(x_5, x_4);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_20 = l_Lean_RBNode_find___at_____private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1___redArg(x_7, x_2);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_21 = lean_mk_string_unchecked("Lean.Data.RBMap", 15, 15);
x_22 = lean_mk_string_unchecked("Lean.RBMap.find!", 16, 16);
x_23 = lean_unsigned_to_nat(389u);
x_24 = lean_unsigned_to_nat(14u);
x_25 = lean_mk_string_unchecked("key is not in the map", 21, 21);
x_26 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_21, x_22, x_23, x_24, x_25);
lean_dec(x_25);
lean_dec(x_22);
lean_dec(x_21);
x_27 = l_panic___at___Lean_Server_FileWorker_WorkerContext_modifyGetPartialHandler_spec__0(x_26);
x_9 = x_27;
goto block_19;
}
else
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_20, 0);
lean_inc(x_28);
lean_dec(x_20);
x_9 = x_28;
goto block_19;
}
block_19:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_apply_1(x_3, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_RBNode_insert___at___Lean_Json_mkObj_spec__0___redArg(x_7, x_2, x_12);
x_14 = lean_st_ref_set(x_5, x_13, x_8);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
lean_ctor_set(x_14, 0, x_11);
return x_14;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_WorkerContext_modifyGetPartialHandler(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Server_FileWorker_WorkerContext_modifyGetPartialHandler___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_WorkerContext_modifyGetPartialHandler___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_FileWorker_WorkerContext_modifyGetPartialHandler___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_WorkerContext_modifyGetPartialHandler___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Server_FileWorker_WorkerContext_modifyGetPartialHandler(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_WorkerContext_modifyPartialHandler(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 4);
x_6 = lean_st_ref_take(x_5, x_4);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_RBNode_find___at_____private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1___redArg(x_7, x_2);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
lean_dec(x_3);
lean_dec(x_2);
x_10 = lean_st_ref_set(x_5, x_7, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_apply_1(x_3, x_11);
x_13 = l_Lean_RBNode_insert___at___Lean_Json_mkObj_spec__0___redArg(x_7, x_2, x_12);
x_14 = lean_st_ref_set(x_5, x_13, x_8);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_WorkerContext_modifyPartialHandler___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_FileWorker_WorkerContext_modifyPartialHandler(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_WorkerContext_updateRequestsInFlight___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_apply_1(x_1, x_4);
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set(x_7, 2, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_WorkerContext_updateRequestsInFlight(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_WorkerContext_updateRequestsInFlight___lam__0), 2, 1);
lean_closure_set(x_5, 0, x_3);
x_6 = l_Lean_Server_FileWorker_WorkerContext_modifyPartialHandler(x_1, x_2, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_WorkerContext_updateRequestsInFlight___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_FileWorker_WorkerContext_updateRequestsInFlight(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_WorkerContext_initPendingServerRequest___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_apply_1(x_1, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
lean_free_object(x_2);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_box(3);
x_8 = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(x_8, 0, x_6);
x_9 = lean_unbox(x_7);
lean_ctor_set_uint8(x_8, sizeof(void*)*1, x_9);
return x_8;
}
else
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
lean_dec(x_5);
lean_ctor_set(x_2, 0, x_10);
return x_2;
}
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_apply_1(x_1, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_box(3);
x_15 = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(x_15, 0, x_13);
x_16 = lean_unbox(x_14);
lean_ctor_set_uint8(x_15, sizeof(void*)*1, x_16);
return x_15;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_12, 0);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
}
else
{
uint8_t x_19; 
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_2);
if (x_19 == 0)
{
return x_2;
}
else
{
uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
x_21 = lean_ctor_get(x_2, 0);
lean_inc(x_21);
lean_dec(x_2);
x_22 = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set_uint8(x_22, sizeof(void*)*1, x_20);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_WorkerContext_initPendingServerRequest___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_5 = lean_io_promise_new(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_2, 5);
x_9 = lean_st_ref_take(x_8, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_alloc_closure((void*)(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_ordRequestID____x40_Lean_Data_JsonRpc___hyg_126____boxed), 2, 0);
lean_inc(x_6);
x_13 = l_Std_DTreeMap_Internal_Impl_insert(lean_box(0), lean_box(0), x_12, x_3, x_6, x_10, lean_box(0));
x_14 = lean_st_ref_set(x_8, x_13, x_11);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
x_17 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_WorkerContext_initPendingServerRequest___redArg___lam__0), 2, 1);
lean_closure_set(x_17, 0, x_1);
x_18 = l_IO_Promise_result_x21___redArg(x_6);
lean_dec(x_6);
x_19 = l_Lean_Server_ServerTask_mapCheap___redArg(x_17, x_18);
lean_ctor_set(x_14, 0, x_19);
return x_14;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_dec(x_14);
x_21 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_WorkerContext_initPendingServerRequest___redArg___lam__0), 2, 1);
lean_closure_set(x_21, 0, x_1);
x_22 = l_IO_Promise_result_x21___redArg(x_6);
lean_dec(x_6);
x_23 = l_Lean_Server_ServerTask_mapCheap___redArg(x_21, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_20);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_WorkerContext_initPendingServerRequest(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Server_FileWorker_WorkerContext_initPendingServerRequest___redArg(x_2, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_WorkerContext_initPendingServerRequest___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_FileWorker_WorkerContext_initPendingServerRequest___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_WorkerContext_initPendingServerRequest___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Server_FileWorker_WorkerContext_initPendingServerRequest(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___Lean_Server_FileWorker_WorkerContext_resolveServerRequestResponse_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 2);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 3);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 4);
lean_inc(x_6);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 lean_ctor_release(x_2, 3);
 lean_ctor_release(x_2, 4);
 x_7 = x_2;
} else {
 lean_dec_ref(x_2);
 x_7 = lean_box(0);
}
lean_inc(x_3);
lean_inc(x_1);
x_8 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_ordRequestID____x40_Lean_Data_JsonRpc___hyg_126_(x_1, x_3);
switch (x_8) {
case 0:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Std_DTreeMap_Internal_Impl_erase___at___Lean_Server_FileWorker_WorkerContext_resolveServerRequestResponse_spec__0___redArg(x_1, x_5);
x_10 = lean_unsigned_to_nat(1u);
if (lean_obj_tag(x_9) == 0)
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_6, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_6, 2);
lean_inc(x_14);
x_15 = lean_ctor_get(x_6, 3);
lean_inc(x_15);
x_16 = lean_ctor_get(x_6, 4);
lean_inc(x_16);
x_17 = lean_unsigned_to_nat(3u);
x_18 = lean_nat_mul(x_17, x_11);
x_19 = lean_nat_dec_lt(x_18, x_12);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_20 = lean_nat_add(x_10, x_11);
lean_dec(x_11);
x_21 = lean_nat_add(x_20, x_12);
lean_dec(x_12);
lean_dec(x_20);
if (lean_is_scalar(x_7)) {
 x_22 = lean_alloc_ctor(0, 5, 0);
} else {
 x_22 = x_7;
}
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_3);
lean_ctor_set(x_22, 2, x_4);
lean_ctor_set(x_22, 3, x_9);
lean_ctor_set(x_22, 4, x_6);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 lean_ctor_release(x_6, 4);
 x_23 = x_6;
} else {
 lean_dec_ref(x_6);
 x_23 = lean_box(0);
}
x_24 = lean_ctor_get(x_15, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_15, 1);
lean_inc(x_25);
x_26 = lean_ctor_get(x_15, 2);
lean_inc(x_26);
x_27 = lean_ctor_get(x_15, 3);
lean_inc(x_27);
x_28 = lean_ctor_get(x_15, 4);
lean_inc(x_28);
x_29 = lean_ctor_get(x_16, 0);
lean_inc(x_29);
x_30 = lean_nat_shiftl(x_29, x_10);
x_31 = lean_nat_dec_lt(x_24, x_30);
lean_dec(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_42; 
lean_dec(x_24);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 lean_ctor_release(x_15, 2);
 lean_ctor_release(x_15, 3);
 lean_ctor_release(x_15, 4);
 x_32 = x_15;
} else {
 lean_dec_ref(x_15);
 x_32 = lean_box(0);
}
x_33 = lean_nat_add(x_10, x_11);
lean_dec(x_11);
x_34 = lean_nat_add(x_33, x_12);
lean_dec(x_12);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_27, 0);
lean_inc(x_49);
x_42 = x_49;
goto block_48;
}
else
{
lean_object* x_50; 
x_50 = lean_unsigned_to_nat(0u);
x_42 = x_50;
goto block_48;
}
block_41:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_nat_add(x_36, x_37);
lean_dec(x_37);
lean_dec(x_36);
if (lean_is_scalar(x_32)) {
 x_39 = lean_alloc_ctor(0, 5, 0);
} else {
 x_39 = x_32;
}
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_13);
lean_ctor_set(x_39, 2, x_14);
lean_ctor_set(x_39, 3, x_28);
lean_ctor_set(x_39, 4, x_16);
if (lean_is_scalar(x_23)) {
 x_40 = lean_alloc_ctor(0, 5, 0);
} else {
 x_40 = x_23;
}
lean_ctor_set(x_40, 0, x_34);
lean_ctor_set(x_40, 1, x_25);
lean_ctor_set(x_40, 2, x_26);
lean_ctor_set(x_40, 3, x_35);
lean_ctor_set(x_40, 4, x_39);
return x_40;
}
block_48:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_nat_add(x_33, x_42);
lean_dec(x_42);
lean_dec(x_33);
if (lean_is_scalar(x_7)) {
 x_44 = lean_alloc_ctor(0, 5, 0);
} else {
 x_44 = x_7;
}
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_3);
lean_ctor_set(x_44, 2, x_4);
lean_ctor_set(x_44, 3, x_9);
lean_ctor_set(x_44, 4, x_27);
x_45 = lean_nat_add(x_10, x_29);
lean_dec(x_29);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_28, 0);
lean_inc(x_46);
x_35 = x_44;
x_36 = x_45;
x_37 = x_46;
goto block_41;
}
else
{
lean_object* x_47; 
x_47 = lean_unsigned_to_nat(0u);
x_35 = x_44;
x_36 = x_45;
x_37 = x_47;
goto block_41;
}
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_7);
x_51 = lean_nat_add(x_10, x_11);
lean_dec(x_11);
x_52 = lean_nat_add(x_51, x_12);
lean_dec(x_12);
x_53 = lean_nat_add(x_51, x_24);
lean_dec(x_24);
lean_dec(x_51);
lean_inc(x_9);
if (lean_is_scalar(x_23)) {
 x_54 = lean_alloc_ctor(0, 5, 0);
} else {
 x_54 = x_23;
}
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_3);
lean_ctor_set(x_54, 2, x_4);
lean_ctor_set(x_54, 3, x_9);
lean_ctor_set(x_54, 4, x_15);
x_55 = !lean_is_exclusive(x_9);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_56 = lean_ctor_get(x_9, 4);
lean_dec(x_56);
x_57 = lean_ctor_get(x_9, 3);
lean_dec(x_57);
x_58 = lean_ctor_get(x_9, 2);
lean_dec(x_58);
x_59 = lean_ctor_get(x_9, 1);
lean_dec(x_59);
x_60 = lean_ctor_get(x_9, 0);
lean_dec(x_60);
lean_ctor_set(x_9, 4, x_16);
lean_ctor_set(x_9, 3, x_54);
lean_ctor_set(x_9, 2, x_14);
lean_ctor_set(x_9, 1, x_13);
lean_ctor_set(x_9, 0, x_52);
return x_9;
}
else
{
lean_object* x_61; 
lean_dec(x_9);
x_61 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_61, 0, x_52);
lean_ctor_set(x_61, 1, x_13);
lean_ctor_set(x_61, 2, x_14);
lean_ctor_set(x_61, 3, x_54);
lean_ctor_set(x_61, 4, x_16);
return x_61;
}
}
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_9, 0);
lean_inc(x_62);
x_63 = lean_nat_add(x_10, x_62);
lean_dec(x_62);
if (lean_is_scalar(x_7)) {
 x_64 = lean_alloc_ctor(0, 5, 0);
} else {
 x_64 = x_7;
}
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_3);
lean_ctor_set(x_64, 2, x_4);
lean_ctor_set(x_64, 3, x_9);
lean_ctor_set(x_64, 4, x_6);
return x_64;
}
}
else
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_6, 3);
lean_inc(x_65);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_6, 4);
lean_inc(x_66);
if (lean_obj_tag(x_66) == 0)
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_6);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_68 = lean_ctor_get(x_6, 0);
x_69 = lean_ctor_get(x_6, 1);
x_70 = lean_ctor_get(x_6, 2);
x_71 = lean_ctor_get(x_6, 4);
lean_dec(x_71);
x_72 = lean_ctor_get(x_6, 3);
lean_dec(x_72);
x_73 = lean_ctor_get(x_65, 0);
lean_inc(x_73);
x_74 = lean_nat_add(x_10, x_68);
lean_dec(x_68);
x_75 = lean_nat_add(x_10, x_73);
lean_dec(x_73);
lean_ctor_set(x_6, 4, x_65);
lean_ctor_set(x_6, 3, x_9);
lean_ctor_set(x_6, 2, x_4);
lean_ctor_set(x_6, 1, x_3);
lean_ctor_set(x_6, 0, x_75);
if (lean_is_scalar(x_7)) {
 x_76 = lean_alloc_ctor(0, 5, 0);
} else {
 x_76 = x_7;
}
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_69);
lean_ctor_set(x_76, 2, x_70);
lean_ctor_set(x_76, 3, x_6);
lean_ctor_set(x_76, 4, x_66);
return x_76;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_77 = lean_ctor_get(x_6, 0);
x_78 = lean_ctor_get(x_6, 1);
x_79 = lean_ctor_get(x_6, 2);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_6);
x_80 = lean_ctor_get(x_65, 0);
lean_inc(x_80);
x_81 = lean_nat_add(x_10, x_77);
lean_dec(x_77);
x_82 = lean_nat_add(x_10, x_80);
lean_dec(x_80);
x_83 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_3);
lean_ctor_set(x_83, 2, x_4);
lean_ctor_set(x_83, 3, x_9);
lean_ctor_set(x_83, 4, x_65);
if (lean_is_scalar(x_7)) {
 x_84 = lean_alloc_ctor(0, 5, 0);
} else {
 x_84 = x_7;
}
lean_ctor_set(x_84, 0, x_81);
lean_ctor_set(x_84, 1, x_78);
lean_ctor_set(x_84, 2, x_79);
lean_ctor_set(x_84, 3, x_83);
lean_ctor_set(x_84, 4, x_66);
return x_84;
}
}
else
{
uint8_t x_85; 
x_85 = !lean_is_exclusive(x_6);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_86 = lean_ctor_get(x_6, 4);
lean_dec(x_86);
x_87 = lean_ctor_get(x_6, 3);
lean_dec(x_87);
x_88 = lean_ctor_get(x_6, 0);
lean_dec(x_88);
x_89 = !lean_is_exclusive(x_65);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_90 = lean_ctor_get(x_65, 1);
x_91 = lean_ctor_get(x_65, 2);
x_92 = lean_ctor_get(x_65, 4);
lean_dec(x_92);
x_93 = lean_ctor_get(x_65, 3);
lean_dec(x_93);
x_94 = lean_ctor_get(x_65, 0);
lean_dec(x_94);
x_95 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_65, 4, x_66);
lean_ctor_set(x_65, 3, x_66);
lean_ctor_set(x_65, 2, x_4);
lean_ctor_set(x_65, 1, x_3);
lean_ctor_set(x_65, 0, x_10);
lean_ctor_set(x_6, 3, x_66);
lean_ctor_set(x_6, 0, x_10);
if (lean_is_scalar(x_7)) {
 x_96 = lean_alloc_ctor(0, 5, 0);
} else {
 x_96 = x_7;
}
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_90);
lean_ctor_set(x_96, 2, x_91);
lean_ctor_set(x_96, 3, x_65);
lean_ctor_set(x_96, 4, x_6);
return x_96;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_97 = lean_ctor_get(x_65, 1);
x_98 = lean_ctor_get(x_65, 2);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_65);
x_99 = lean_unsigned_to_nat(3u);
x_100 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_100, 0, x_10);
lean_ctor_set(x_100, 1, x_3);
lean_ctor_set(x_100, 2, x_4);
lean_ctor_set(x_100, 3, x_66);
lean_ctor_set(x_100, 4, x_66);
lean_ctor_set(x_6, 3, x_66);
lean_ctor_set(x_6, 0, x_10);
if (lean_is_scalar(x_7)) {
 x_101 = lean_alloc_ctor(0, 5, 0);
} else {
 x_101 = x_7;
}
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_97);
lean_ctor_set(x_101, 2, x_98);
lean_ctor_set(x_101, 3, x_100);
lean_ctor_set(x_101, 4, x_6);
return x_101;
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_102 = lean_ctor_get(x_6, 1);
x_103 = lean_ctor_get(x_6, 2);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_6);
x_104 = lean_ctor_get(x_65, 1);
lean_inc(x_104);
x_105 = lean_ctor_get(x_65, 2);
lean_inc(x_105);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 lean_ctor_release(x_65, 2);
 lean_ctor_release(x_65, 3);
 lean_ctor_release(x_65, 4);
 x_106 = x_65;
} else {
 lean_dec_ref(x_65);
 x_106 = lean_box(0);
}
x_107 = lean_unsigned_to_nat(3u);
if (lean_is_scalar(x_106)) {
 x_108 = lean_alloc_ctor(0, 5, 0);
} else {
 x_108 = x_106;
}
lean_ctor_set(x_108, 0, x_10);
lean_ctor_set(x_108, 1, x_3);
lean_ctor_set(x_108, 2, x_4);
lean_ctor_set(x_108, 3, x_66);
lean_ctor_set(x_108, 4, x_66);
x_109 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_109, 0, x_10);
lean_ctor_set(x_109, 1, x_102);
lean_ctor_set(x_109, 2, x_103);
lean_ctor_set(x_109, 3, x_66);
lean_ctor_set(x_109, 4, x_66);
if (lean_is_scalar(x_7)) {
 x_110 = lean_alloc_ctor(0, 5, 0);
} else {
 x_110 = x_7;
}
lean_ctor_set(x_110, 0, x_107);
lean_ctor_set(x_110, 1, x_104);
lean_ctor_set(x_110, 2, x_105);
lean_ctor_set(x_110, 3, x_108);
lean_ctor_set(x_110, 4, x_109);
return x_110;
}
}
}
else
{
lean_object* x_111; 
x_111 = lean_ctor_get(x_6, 4);
lean_inc(x_111);
if (lean_obj_tag(x_111) == 0)
{
uint8_t x_112; 
x_112 = !lean_is_exclusive(x_6);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_113 = lean_ctor_get(x_6, 1);
x_114 = lean_ctor_get(x_6, 2);
x_115 = lean_ctor_get(x_6, 4);
lean_dec(x_115);
x_116 = lean_ctor_get(x_6, 3);
lean_dec(x_116);
x_117 = lean_ctor_get(x_6, 0);
lean_dec(x_117);
x_118 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_6, 4, x_65);
lean_ctor_set(x_6, 2, x_4);
lean_ctor_set(x_6, 1, x_3);
lean_ctor_set(x_6, 0, x_10);
if (lean_is_scalar(x_7)) {
 x_119 = lean_alloc_ctor(0, 5, 0);
} else {
 x_119 = x_7;
}
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_113);
lean_ctor_set(x_119, 2, x_114);
lean_ctor_set(x_119, 3, x_6);
lean_ctor_set(x_119, 4, x_111);
return x_119;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_120 = lean_ctor_get(x_6, 1);
x_121 = lean_ctor_get(x_6, 2);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_6);
x_122 = lean_unsigned_to_nat(3u);
x_123 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_123, 0, x_10);
lean_ctor_set(x_123, 1, x_3);
lean_ctor_set(x_123, 2, x_4);
lean_ctor_set(x_123, 3, x_65);
lean_ctor_set(x_123, 4, x_65);
if (lean_is_scalar(x_7)) {
 x_124 = lean_alloc_ctor(0, 5, 0);
} else {
 x_124 = x_7;
}
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_120);
lean_ctor_set(x_124, 2, x_121);
lean_ctor_set(x_124, 3, x_123);
lean_ctor_set(x_124, 4, x_111);
return x_124;
}
}
else
{
uint8_t x_125; 
x_125 = !lean_is_exclusive(x_6);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_126 = lean_ctor_get(x_6, 4);
lean_dec(x_126);
x_127 = lean_ctor_get(x_6, 3);
lean_dec(x_127);
lean_ctor_set(x_6, 3, x_111);
x_128 = lean_unsigned_to_nat(2u);
if (lean_is_scalar(x_7)) {
 x_129 = lean_alloc_ctor(0, 5, 0);
} else {
 x_129 = x_7;
}
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_3);
lean_ctor_set(x_129, 2, x_4);
lean_ctor_set(x_129, 3, x_111);
lean_ctor_set(x_129, 4, x_6);
return x_129;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_130 = lean_ctor_get(x_6, 0);
x_131 = lean_ctor_get(x_6, 1);
x_132 = lean_ctor_get(x_6, 2);
lean_inc(x_132);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_6);
x_133 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_133, 0, x_130);
lean_ctor_set(x_133, 1, x_131);
lean_ctor_set(x_133, 2, x_132);
lean_ctor_set(x_133, 3, x_111);
lean_ctor_set(x_133, 4, x_111);
x_134 = lean_unsigned_to_nat(2u);
if (lean_is_scalar(x_7)) {
 x_135 = lean_alloc_ctor(0, 5, 0);
} else {
 x_135 = x_7;
}
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_3);
lean_ctor_set(x_135, 2, x_4);
lean_ctor_set(x_135, 3, x_111);
lean_ctor_set(x_135, 4, x_133);
return x_135;
}
}
}
}
else
{
lean_object* x_136; 
if (lean_is_scalar(x_7)) {
 x_136 = lean_alloc_ctor(0, 5, 0);
} else {
 x_136 = x_7;
}
lean_ctor_set(x_136, 0, x_10);
lean_ctor_set(x_136, 1, x_3);
lean_ctor_set(x_136, 2, x_4);
lean_ctor_set(x_136, 3, x_6);
lean_ctor_set(x_136, 4, x_6);
return x_136;
}
}
}
case 1:
{
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
if (lean_obj_tag(x_5) == 0)
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; 
x_137 = lean_ctor_get(x_5, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_5, 1);
lean_inc(x_138);
x_139 = lean_ctor_get(x_5, 2);
lean_inc(x_139);
x_140 = lean_ctor_get(x_5, 3);
lean_inc(x_140);
x_141 = lean_ctor_get(x_5, 4);
lean_inc(x_141);
x_142 = lean_ctor_get(x_6, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_6, 1);
lean_inc(x_143);
x_144 = lean_ctor_get(x_6, 2);
lean_inc(x_144);
x_145 = lean_ctor_get(x_6, 3);
lean_inc(x_145);
x_146 = lean_ctor_get(x_6, 4);
lean_inc(x_146);
x_147 = lean_unsigned_to_nat(1u);
x_148 = lean_nat_dec_lt(x_137, x_142);
if (x_148 == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
lean_dec(x_137);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 lean_ctor_release(x_5, 2);
 lean_ctor_release(x_5, 3);
 lean_ctor_release(x_5, 4);
 x_149 = x_5;
} else {
 lean_dec_ref(x_5);
 x_149 = lean_box(0);
}
x_150 = l_Std_DTreeMap_Internal_Impl_maxView___redArg(x_138, x_139, x_140, x_141);
x_151 = lean_ctor_get(x_150, 2);
lean_inc(x_151);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; 
x_152 = lean_ctor_get(x_150, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_150, 1);
lean_inc(x_153);
lean_dec(x_150);
x_154 = lean_ctor_get(x_151, 0);
lean_inc(x_154);
x_155 = lean_unsigned_to_nat(3u);
x_156 = lean_nat_mul(x_155, x_154);
x_157 = lean_nat_dec_lt(x_156, x_142);
lean_dec(x_156);
if (x_157 == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_146);
lean_dec(x_145);
lean_dec(x_144);
lean_dec(x_143);
x_158 = lean_nat_add(x_147, x_154);
lean_dec(x_154);
x_159 = lean_nat_add(x_158, x_142);
lean_dec(x_142);
lean_dec(x_158);
if (lean_is_scalar(x_149)) {
 x_160 = lean_alloc_ctor(0, 5, 0);
} else {
 x_160 = x_149;
}
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_152);
lean_ctor_set(x_160, 2, x_153);
lean_ctor_set(x_160, 3, x_151);
lean_ctor_set(x_160, 4, x_6);
return x_160;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; uint8_t x_169; 
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 lean_ctor_release(x_6, 4);
 x_161 = x_6;
} else {
 lean_dec_ref(x_6);
 x_161 = lean_box(0);
}
x_162 = lean_ctor_get(x_145, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_145, 1);
lean_inc(x_163);
x_164 = lean_ctor_get(x_145, 2);
lean_inc(x_164);
x_165 = lean_ctor_get(x_145, 3);
lean_inc(x_165);
x_166 = lean_ctor_get(x_145, 4);
lean_inc(x_166);
x_167 = lean_ctor_get(x_146, 0);
lean_inc(x_167);
x_168 = lean_nat_shiftl(x_167, x_147);
x_169 = lean_nat_dec_lt(x_162, x_168);
lean_dec(x_168);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_180; 
lean_dec(x_162);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 lean_ctor_release(x_145, 2);
 lean_ctor_release(x_145, 3);
 lean_ctor_release(x_145, 4);
 x_170 = x_145;
} else {
 lean_dec_ref(x_145);
 x_170 = lean_box(0);
}
x_171 = lean_nat_add(x_147, x_154);
lean_dec(x_154);
x_172 = lean_nat_add(x_171, x_142);
lean_dec(x_142);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_187; 
x_187 = lean_ctor_get(x_165, 0);
lean_inc(x_187);
x_180 = x_187;
goto block_186;
}
else
{
lean_object* x_188; 
x_188 = lean_unsigned_to_nat(0u);
x_180 = x_188;
goto block_186;
}
block_179:
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_176 = lean_nat_add(x_174, x_175);
lean_dec(x_175);
lean_dec(x_174);
if (lean_is_scalar(x_170)) {
 x_177 = lean_alloc_ctor(0, 5, 0);
} else {
 x_177 = x_170;
}
lean_ctor_set(x_177, 0, x_176);
lean_ctor_set(x_177, 1, x_143);
lean_ctor_set(x_177, 2, x_144);
lean_ctor_set(x_177, 3, x_166);
lean_ctor_set(x_177, 4, x_146);
if (lean_is_scalar(x_161)) {
 x_178 = lean_alloc_ctor(0, 5, 0);
} else {
 x_178 = x_161;
}
lean_ctor_set(x_178, 0, x_172);
lean_ctor_set(x_178, 1, x_163);
lean_ctor_set(x_178, 2, x_164);
lean_ctor_set(x_178, 3, x_173);
lean_ctor_set(x_178, 4, x_177);
return x_178;
}
block_186:
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_181 = lean_nat_add(x_171, x_180);
lean_dec(x_180);
lean_dec(x_171);
if (lean_is_scalar(x_149)) {
 x_182 = lean_alloc_ctor(0, 5, 0);
} else {
 x_182 = x_149;
}
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_152);
lean_ctor_set(x_182, 2, x_153);
lean_ctor_set(x_182, 3, x_151);
lean_ctor_set(x_182, 4, x_165);
x_183 = lean_nat_add(x_147, x_167);
lean_dec(x_167);
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_184; 
x_184 = lean_ctor_get(x_166, 0);
lean_inc(x_184);
x_173 = x_182;
x_174 = x_183;
x_175 = x_184;
goto block_179;
}
else
{
lean_object* x_185; 
x_185 = lean_unsigned_to_nat(0u);
x_173 = x_182;
x_174 = x_183;
x_175 = x_185;
goto block_179;
}
}
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
lean_dec(x_167);
lean_dec(x_166);
lean_dec(x_165);
lean_dec(x_164);
lean_dec(x_163);
x_189 = lean_nat_add(x_147, x_154);
lean_dec(x_154);
x_190 = lean_nat_add(x_189, x_142);
lean_dec(x_142);
x_191 = lean_nat_add(x_189, x_162);
lean_dec(x_162);
lean_dec(x_189);
if (lean_is_scalar(x_161)) {
 x_192 = lean_alloc_ctor(0, 5, 0);
} else {
 x_192 = x_161;
}
lean_ctor_set(x_192, 0, x_191);
lean_ctor_set(x_192, 1, x_152);
lean_ctor_set(x_192, 2, x_153);
lean_ctor_set(x_192, 3, x_151);
lean_ctor_set(x_192, 4, x_145);
if (lean_is_scalar(x_149)) {
 x_193 = lean_alloc_ctor(0, 5, 0);
} else {
 x_193 = x_149;
}
lean_ctor_set(x_193, 0, x_190);
lean_ctor_set(x_193, 1, x_143);
lean_ctor_set(x_193, 2, x_144);
lean_ctor_set(x_193, 3, x_192);
lean_ctor_set(x_193, 4, x_146);
return x_193;
}
}
}
else
{
uint8_t x_194; 
x_194 = !lean_is_exclusive(x_6);
if (x_194 == 0)
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_195 = lean_ctor_get(x_6, 4);
lean_dec(x_195);
x_196 = lean_ctor_get(x_6, 3);
lean_dec(x_196);
x_197 = lean_ctor_get(x_6, 2);
lean_dec(x_197);
x_198 = lean_ctor_get(x_6, 1);
lean_dec(x_198);
x_199 = lean_ctor_get(x_6, 0);
lean_dec(x_199);
if (lean_obj_tag(x_145) == 0)
{
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_200 = lean_ctor_get(x_150, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_150, 1);
lean_inc(x_201);
lean_dec(x_150);
x_202 = lean_ctor_get(x_145, 0);
lean_inc(x_202);
x_203 = lean_nat_add(x_147, x_142);
lean_dec(x_142);
x_204 = lean_nat_add(x_147, x_202);
lean_dec(x_202);
lean_ctor_set(x_6, 4, x_145);
lean_ctor_set(x_6, 3, x_151);
lean_ctor_set(x_6, 2, x_201);
lean_ctor_set(x_6, 1, x_200);
lean_ctor_set(x_6, 0, x_204);
if (lean_is_scalar(x_149)) {
 x_205 = lean_alloc_ctor(0, 5, 0);
} else {
 x_205 = x_149;
}
lean_ctor_set(x_205, 0, x_203);
lean_ctor_set(x_205, 1, x_143);
lean_ctor_set(x_205, 2, x_144);
lean_ctor_set(x_205, 3, x_6);
lean_ctor_set(x_205, 4, x_146);
return x_205;
}
else
{
lean_object* x_206; lean_object* x_207; uint8_t x_208; 
lean_dec(x_142);
x_206 = lean_ctor_get(x_150, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_150, 1);
lean_inc(x_207);
lean_dec(x_150);
x_208 = !lean_is_exclusive(x_145);
if (x_208 == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_209 = lean_ctor_get(x_145, 1);
x_210 = lean_ctor_get(x_145, 2);
x_211 = lean_ctor_get(x_145, 4);
lean_dec(x_211);
x_212 = lean_ctor_get(x_145, 3);
lean_dec(x_212);
x_213 = lean_ctor_get(x_145, 0);
lean_dec(x_213);
x_214 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_145, 4, x_146);
lean_ctor_set(x_145, 3, x_146);
lean_ctor_set(x_145, 2, x_207);
lean_ctor_set(x_145, 1, x_206);
lean_ctor_set(x_145, 0, x_147);
lean_ctor_set(x_6, 3, x_146);
lean_ctor_set(x_6, 0, x_147);
if (lean_is_scalar(x_149)) {
 x_215 = lean_alloc_ctor(0, 5, 0);
} else {
 x_215 = x_149;
}
lean_ctor_set(x_215, 0, x_214);
lean_ctor_set(x_215, 1, x_209);
lean_ctor_set(x_215, 2, x_210);
lean_ctor_set(x_215, 3, x_145);
lean_ctor_set(x_215, 4, x_6);
return x_215;
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_216 = lean_ctor_get(x_145, 1);
x_217 = lean_ctor_get(x_145, 2);
lean_inc(x_217);
lean_inc(x_216);
lean_dec(x_145);
x_218 = lean_unsigned_to_nat(3u);
x_219 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_219, 0, x_147);
lean_ctor_set(x_219, 1, x_206);
lean_ctor_set(x_219, 2, x_207);
lean_ctor_set(x_219, 3, x_146);
lean_ctor_set(x_219, 4, x_146);
lean_ctor_set(x_6, 3, x_146);
lean_ctor_set(x_6, 0, x_147);
if (lean_is_scalar(x_149)) {
 x_220 = lean_alloc_ctor(0, 5, 0);
} else {
 x_220 = x_149;
}
lean_ctor_set(x_220, 0, x_218);
lean_ctor_set(x_220, 1, x_216);
lean_ctor_set(x_220, 2, x_217);
lean_ctor_set(x_220, 3, x_219);
lean_ctor_set(x_220, 4, x_6);
return x_220;
}
}
}
else
{
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
lean_dec(x_142);
x_221 = lean_ctor_get(x_150, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_150, 1);
lean_inc(x_222);
lean_dec(x_150);
x_223 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_6, 4, x_145);
lean_ctor_set(x_6, 2, x_222);
lean_ctor_set(x_6, 1, x_221);
lean_ctor_set(x_6, 0, x_147);
if (lean_is_scalar(x_149)) {
 x_224 = lean_alloc_ctor(0, 5, 0);
} else {
 x_224 = x_149;
}
lean_ctor_set(x_224, 0, x_223);
lean_ctor_set(x_224, 1, x_143);
lean_ctor_set(x_224, 2, x_144);
lean_ctor_set(x_224, 3, x_6);
lean_ctor_set(x_224, 4, x_146);
return x_224;
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_225 = lean_ctor_get(x_150, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_150, 1);
lean_inc(x_226);
lean_dec(x_150);
lean_ctor_set(x_6, 3, x_146);
x_227 = lean_unsigned_to_nat(2u);
if (lean_is_scalar(x_149)) {
 x_228 = lean_alloc_ctor(0, 5, 0);
} else {
 x_228 = x_149;
}
lean_ctor_set(x_228, 0, x_227);
lean_ctor_set(x_228, 1, x_225);
lean_ctor_set(x_228, 2, x_226);
lean_ctor_set(x_228, 3, x_146);
lean_ctor_set(x_228, 4, x_6);
return x_228;
}
}
}
else
{
lean_dec(x_6);
if (lean_obj_tag(x_145) == 0)
{
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_229 = lean_ctor_get(x_150, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_150, 1);
lean_inc(x_230);
lean_dec(x_150);
x_231 = lean_ctor_get(x_145, 0);
lean_inc(x_231);
x_232 = lean_nat_add(x_147, x_142);
lean_dec(x_142);
x_233 = lean_nat_add(x_147, x_231);
lean_dec(x_231);
x_234 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_234, 0, x_233);
lean_ctor_set(x_234, 1, x_229);
lean_ctor_set(x_234, 2, x_230);
lean_ctor_set(x_234, 3, x_151);
lean_ctor_set(x_234, 4, x_145);
if (lean_is_scalar(x_149)) {
 x_235 = lean_alloc_ctor(0, 5, 0);
} else {
 x_235 = x_149;
}
lean_ctor_set(x_235, 0, x_232);
lean_ctor_set(x_235, 1, x_143);
lean_ctor_set(x_235, 2, x_144);
lean_ctor_set(x_235, 3, x_234);
lean_ctor_set(x_235, 4, x_146);
return x_235;
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
lean_dec(x_142);
x_236 = lean_ctor_get(x_150, 0);
lean_inc(x_236);
x_237 = lean_ctor_get(x_150, 1);
lean_inc(x_237);
lean_dec(x_150);
x_238 = lean_ctor_get(x_145, 1);
lean_inc(x_238);
x_239 = lean_ctor_get(x_145, 2);
lean_inc(x_239);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 lean_ctor_release(x_145, 2);
 lean_ctor_release(x_145, 3);
 lean_ctor_release(x_145, 4);
 x_240 = x_145;
} else {
 lean_dec_ref(x_145);
 x_240 = lean_box(0);
}
x_241 = lean_unsigned_to_nat(3u);
if (lean_is_scalar(x_240)) {
 x_242 = lean_alloc_ctor(0, 5, 0);
} else {
 x_242 = x_240;
}
lean_ctor_set(x_242, 0, x_147);
lean_ctor_set(x_242, 1, x_236);
lean_ctor_set(x_242, 2, x_237);
lean_ctor_set(x_242, 3, x_146);
lean_ctor_set(x_242, 4, x_146);
x_243 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_243, 0, x_147);
lean_ctor_set(x_243, 1, x_143);
lean_ctor_set(x_243, 2, x_144);
lean_ctor_set(x_243, 3, x_146);
lean_ctor_set(x_243, 4, x_146);
if (lean_is_scalar(x_149)) {
 x_244 = lean_alloc_ctor(0, 5, 0);
} else {
 x_244 = x_149;
}
lean_ctor_set(x_244, 0, x_241);
lean_ctor_set(x_244, 1, x_238);
lean_ctor_set(x_244, 2, x_239);
lean_ctor_set(x_244, 3, x_242);
lean_ctor_set(x_244, 4, x_243);
return x_244;
}
}
else
{
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
lean_dec(x_142);
x_245 = lean_ctor_get(x_150, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_150, 1);
lean_inc(x_246);
lean_dec(x_150);
x_247 = lean_unsigned_to_nat(3u);
x_248 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_248, 0, x_147);
lean_ctor_set(x_248, 1, x_245);
lean_ctor_set(x_248, 2, x_246);
lean_ctor_set(x_248, 3, x_145);
lean_ctor_set(x_248, 4, x_145);
if (lean_is_scalar(x_149)) {
 x_249 = lean_alloc_ctor(0, 5, 0);
} else {
 x_249 = x_149;
}
lean_ctor_set(x_249, 0, x_247);
lean_ctor_set(x_249, 1, x_143);
lean_ctor_set(x_249, 2, x_144);
lean_ctor_set(x_249, 3, x_248);
lean_ctor_set(x_249, 4, x_146);
return x_249;
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_250 = lean_ctor_get(x_150, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_150, 1);
lean_inc(x_251);
lean_dec(x_150);
x_252 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_252, 0, x_142);
lean_ctor_set(x_252, 1, x_143);
lean_ctor_set(x_252, 2, x_144);
lean_ctor_set(x_252, 3, x_146);
lean_ctor_set(x_252, 4, x_146);
x_253 = lean_unsigned_to_nat(2u);
if (lean_is_scalar(x_149)) {
 x_254 = lean_alloc_ctor(0, 5, 0);
} else {
 x_254 = x_149;
}
lean_ctor_set(x_254, 0, x_253);
lean_ctor_set(x_254, 1, x_250);
lean_ctor_set(x_254, 2, x_251);
lean_ctor_set(x_254, 3, x_146);
lean_ctor_set(x_254, 4, x_252);
return x_254;
}
}
}
}
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; 
lean_dec(x_142);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 lean_ctor_release(x_6, 4);
 x_255 = x_6;
} else {
 lean_dec_ref(x_6);
 x_255 = lean_box(0);
}
x_256 = l_Std_DTreeMap_Internal_Impl_minView___redArg(x_143, x_144, x_145, x_146);
x_257 = lean_ctor_get(x_256, 2);
lean_inc(x_257);
if (lean_obj_tag(x_257) == 0)
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; uint8_t x_263; 
x_258 = lean_ctor_get(x_256, 0);
lean_inc(x_258);
x_259 = lean_ctor_get(x_256, 1);
lean_inc(x_259);
lean_dec(x_256);
x_260 = lean_ctor_get(x_257, 0);
lean_inc(x_260);
x_261 = lean_unsigned_to_nat(3u);
x_262 = lean_nat_mul(x_261, x_260);
x_263 = lean_nat_dec_lt(x_262, x_137);
lean_dec(x_262);
if (x_263 == 0)
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; 
lean_dec(x_141);
lean_dec(x_140);
lean_dec(x_139);
lean_dec(x_138);
x_264 = lean_nat_add(x_147, x_137);
lean_dec(x_137);
x_265 = lean_nat_add(x_264, x_260);
lean_dec(x_260);
lean_dec(x_264);
if (lean_is_scalar(x_255)) {
 x_266 = lean_alloc_ctor(0, 5, 0);
} else {
 x_266 = x_255;
}
lean_ctor_set(x_266, 0, x_265);
lean_ctor_set(x_266, 1, x_258);
lean_ctor_set(x_266, 2, x_259);
lean_ctor_set(x_266, 3, x_5);
lean_ctor_set(x_266, 4, x_257);
return x_266;
}
else
{
uint8_t x_267; 
x_267 = !lean_is_exclusive(x_5);
if (x_267 == 0)
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; uint8_t x_280; 
x_268 = lean_ctor_get(x_5, 4);
lean_dec(x_268);
x_269 = lean_ctor_get(x_5, 3);
lean_dec(x_269);
x_270 = lean_ctor_get(x_5, 2);
lean_dec(x_270);
x_271 = lean_ctor_get(x_5, 1);
lean_dec(x_271);
x_272 = lean_ctor_get(x_5, 0);
lean_dec(x_272);
x_273 = lean_ctor_get(x_140, 0);
lean_inc(x_273);
x_274 = lean_ctor_get(x_141, 0);
lean_inc(x_274);
x_275 = lean_ctor_get(x_141, 1);
lean_inc(x_275);
x_276 = lean_ctor_get(x_141, 2);
lean_inc(x_276);
x_277 = lean_ctor_get(x_141, 3);
lean_inc(x_277);
x_278 = lean_ctor_get(x_141, 4);
lean_inc(x_278);
x_279 = lean_nat_shiftl(x_273, x_147);
x_280 = lean_nat_dec_lt(x_274, x_279);
lean_dec(x_279);
if (x_280 == 0)
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_297; lean_object* x_298; 
lean_dec(x_274);
lean_free_object(x_5);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 lean_ctor_release(x_141, 2);
 lean_ctor_release(x_141, 3);
 lean_ctor_release(x_141, 4);
 x_281 = x_141;
} else {
 lean_dec_ref(x_141);
 x_281 = lean_box(0);
}
x_282 = lean_nat_add(x_147, x_137);
lean_dec(x_137);
x_283 = lean_nat_add(x_282, x_260);
lean_dec(x_282);
x_297 = lean_nat_add(x_147, x_273);
lean_dec(x_273);
if (lean_obj_tag(x_277) == 0)
{
lean_object* x_305; 
x_305 = lean_ctor_get(x_277, 0);
lean_inc(x_305);
x_298 = x_305;
goto block_304;
}
else
{
lean_object* x_306; 
x_306 = lean_unsigned_to_nat(0u);
x_298 = x_306;
goto block_304;
}
block_296:
{
lean_object* x_287; lean_object* x_288; uint8_t x_289; 
x_287 = lean_nat_add(x_284, x_286);
lean_dec(x_286);
lean_dec(x_284);
lean_inc(x_257);
if (lean_is_scalar(x_281)) {
 x_288 = lean_alloc_ctor(0, 5, 0);
} else {
 x_288 = x_281;
}
lean_ctor_set(x_288, 0, x_287);
lean_ctor_set(x_288, 1, x_258);
lean_ctor_set(x_288, 2, x_259);
lean_ctor_set(x_288, 3, x_278);
lean_ctor_set(x_288, 4, x_257);
x_289 = !lean_is_exclusive(x_257);
if (x_289 == 0)
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; 
x_290 = lean_ctor_get(x_257, 4);
lean_dec(x_290);
x_291 = lean_ctor_get(x_257, 3);
lean_dec(x_291);
x_292 = lean_ctor_get(x_257, 2);
lean_dec(x_292);
x_293 = lean_ctor_get(x_257, 1);
lean_dec(x_293);
x_294 = lean_ctor_get(x_257, 0);
lean_dec(x_294);
lean_ctor_set(x_257, 4, x_288);
lean_ctor_set(x_257, 3, x_285);
lean_ctor_set(x_257, 2, x_276);
lean_ctor_set(x_257, 1, x_275);
lean_ctor_set(x_257, 0, x_283);
return x_257;
}
else
{
lean_object* x_295; 
lean_dec(x_257);
x_295 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_295, 0, x_283);
lean_ctor_set(x_295, 1, x_275);
lean_ctor_set(x_295, 2, x_276);
lean_ctor_set(x_295, 3, x_285);
lean_ctor_set(x_295, 4, x_288);
return x_295;
}
}
block_304:
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; 
x_299 = lean_nat_add(x_297, x_298);
lean_dec(x_298);
lean_dec(x_297);
if (lean_is_scalar(x_255)) {
 x_300 = lean_alloc_ctor(0, 5, 0);
} else {
 x_300 = x_255;
}
lean_ctor_set(x_300, 0, x_299);
lean_ctor_set(x_300, 1, x_138);
lean_ctor_set(x_300, 2, x_139);
lean_ctor_set(x_300, 3, x_140);
lean_ctor_set(x_300, 4, x_277);
x_301 = lean_nat_add(x_147, x_260);
lean_dec(x_260);
if (lean_obj_tag(x_278) == 0)
{
lean_object* x_302; 
x_302 = lean_ctor_get(x_278, 0);
lean_inc(x_302);
x_284 = x_301;
x_285 = x_300;
x_286 = x_302;
goto block_296;
}
else
{
lean_object* x_303; 
x_303 = lean_unsigned_to_nat(0u);
x_284 = x_301;
x_285 = x_300;
x_286 = x_303;
goto block_296;
}
}
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; 
lean_dec(x_278);
lean_dec(x_277);
lean_dec(x_276);
lean_dec(x_275);
lean_dec(x_273);
x_307 = lean_nat_add(x_147, x_137);
lean_dec(x_137);
x_308 = lean_nat_add(x_307, x_260);
lean_dec(x_307);
x_309 = lean_nat_add(x_147, x_260);
lean_dec(x_260);
x_310 = lean_nat_add(x_309, x_274);
lean_dec(x_274);
lean_dec(x_309);
if (lean_is_scalar(x_255)) {
 x_311 = lean_alloc_ctor(0, 5, 0);
} else {
 x_311 = x_255;
}
lean_ctor_set(x_311, 0, x_310);
lean_ctor_set(x_311, 1, x_258);
lean_ctor_set(x_311, 2, x_259);
lean_ctor_set(x_311, 3, x_141);
lean_ctor_set(x_311, 4, x_257);
lean_ctor_set(x_5, 4, x_311);
lean_ctor_set(x_5, 0, x_308);
return x_5;
}
}
else
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; uint8_t x_319; 
lean_dec(x_5);
x_312 = lean_ctor_get(x_140, 0);
lean_inc(x_312);
x_313 = lean_ctor_get(x_141, 0);
lean_inc(x_313);
x_314 = lean_ctor_get(x_141, 1);
lean_inc(x_314);
x_315 = lean_ctor_get(x_141, 2);
lean_inc(x_315);
x_316 = lean_ctor_get(x_141, 3);
lean_inc(x_316);
x_317 = lean_ctor_get(x_141, 4);
lean_inc(x_317);
x_318 = lean_nat_shiftl(x_312, x_147);
x_319 = lean_nat_dec_lt(x_313, x_318);
lean_dec(x_318);
if (x_319 == 0)
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_331; lean_object* x_332; 
lean_dec(x_313);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 lean_ctor_release(x_141, 2);
 lean_ctor_release(x_141, 3);
 lean_ctor_release(x_141, 4);
 x_320 = x_141;
} else {
 lean_dec_ref(x_141);
 x_320 = lean_box(0);
}
x_321 = lean_nat_add(x_147, x_137);
lean_dec(x_137);
x_322 = lean_nat_add(x_321, x_260);
lean_dec(x_321);
x_331 = lean_nat_add(x_147, x_312);
lean_dec(x_312);
if (lean_obj_tag(x_316) == 0)
{
lean_object* x_339; 
x_339 = lean_ctor_get(x_316, 0);
lean_inc(x_339);
x_332 = x_339;
goto block_338;
}
else
{
lean_object* x_340; 
x_340 = lean_unsigned_to_nat(0u);
x_332 = x_340;
goto block_338;
}
block_330:
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; 
x_326 = lean_nat_add(x_323, x_325);
lean_dec(x_325);
lean_dec(x_323);
lean_inc(x_257);
if (lean_is_scalar(x_320)) {
 x_327 = lean_alloc_ctor(0, 5, 0);
} else {
 x_327 = x_320;
}
lean_ctor_set(x_327, 0, x_326);
lean_ctor_set(x_327, 1, x_258);
lean_ctor_set(x_327, 2, x_259);
lean_ctor_set(x_327, 3, x_317);
lean_ctor_set(x_327, 4, x_257);
if (lean_is_exclusive(x_257)) {
 lean_ctor_release(x_257, 0);
 lean_ctor_release(x_257, 1);
 lean_ctor_release(x_257, 2);
 lean_ctor_release(x_257, 3);
 lean_ctor_release(x_257, 4);
 x_328 = x_257;
} else {
 lean_dec_ref(x_257);
 x_328 = lean_box(0);
}
if (lean_is_scalar(x_328)) {
 x_329 = lean_alloc_ctor(0, 5, 0);
} else {
 x_329 = x_328;
}
lean_ctor_set(x_329, 0, x_322);
lean_ctor_set(x_329, 1, x_314);
lean_ctor_set(x_329, 2, x_315);
lean_ctor_set(x_329, 3, x_324);
lean_ctor_set(x_329, 4, x_327);
return x_329;
}
block_338:
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; 
x_333 = lean_nat_add(x_331, x_332);
lean_dec(x_332);
lean_dec(x_331);
if (lean_is_scalar(x_255)) {
 x_334 = lean_alloc_ctor(0, 5, 0);
} else {
 x_334 = x_255;
}
lean_ctor_set(x_334, 0, x_333);
lean_ctor_set(x_334, 1, x_138);
lean_ctor_set(x_334, 2, x_139);
lean_ctor_set(x_334, 3, x_140);
lean_ctor_set(x_334, 4, x_316);
x_335 = lean_nat_add(x_147, x_260);
lean_dec(x_260);
if (lean_obj_tag(x_317) == 0)
{
lean_object* x_336; 
x_336 = lean_ctor_get(x_317, 0);
lean_inc(x_336);
x_323 = x_335;
x_324 = x_334;
x_325 = x_336;
goto block_330;
}
else
{
lean_object* x_337; 
x_337 = lean_unsigned_to_nat(0u);
x_323 = x_335;
x_324 = x_334;
x_325 = x_337;
goto block_330;
}
}
}
else
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; 
lean_dec(x_317);
lean_dec(x_316);
lean_dec(x_315);
lean_dec(x_314);
lean_dec(x_312);
x_341 = lean_nat_add(x_147, x_137);
lean_dec(x_137);
x_342 = lean_nat_add(x_341, x_260);
lean_dec(x_341);
x_343 = lean_nat_add(x_147, x_260);
lean_dec(x_260);
x_344 = lean_nat_add(x_343, x_313);
lean_dec(x_313);
lean_dec(x_343);
if (lean_is_scalar(x_255)) {
 x_345 = lean_alloc_ctor(0, 5, 0);
} else {
 x_345 = x_255;
}
lean_ctor_set(x_345, 0, x_344);
lean_ctor_set(x_345, 1, x_258);
lean_ctor_set(x_345, 2, x_259);
lean_ctor_set(x_345, 3, x_141);
lean_ctor_set(x_345, 4, x_257);
x_346 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_346, 0, x_342);
lean_ctor_set(x_346, 1, x_138);
lean_ctor_set(x_346, 2, x_139);
lean_ctor_set(x_346, 3, x_140);
lean_ctor_set(x_346, 4, x_345);
return x_346;
}
}
}
}
else
{
if (lean_obj_tag(x_140) == 0)
{
uint8_t x_347; 
x_347 = !lean_is_exclusive(x_5);
if (x_347 == 0)
{
lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; 
x_348 = lean_ctor_get(x_5, 4);
lean_dec(x_348);
x_349 = lean_ctor_get(x_5, 3);
lean_dec(x_349);
x_350 = lean_ctor_get(x_5, 2);
lean_dec(x_350);
x_351 = lean_ctor_get(x_5, 1);
lean_dec(x_351);
x_352 = lean_ctor_get(x_5, 0);
lean_dec(x_352);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; 
x_353 = lean_ctor_get(x_256, 0);
lean_inc(x_353);
x_354 = lean_ctor_get(x_256, 1);
lean_inc(x_354);
lean_dec(x_256);
x_355 = lean_ctor_get(x_141, 0);
lean_inc(x_355);
x_356 = lean_nat_add(x_147, x_137);
lean_dec(x_137);
x_357 = lean_nat_add(x_147, x_355);
lean_dec(x_355);
if (lean_is_scalar(x_255)) {
 x_358 = lean_alloc_ctor(0, 5, 0);
} else {
 x_358 = x_255;
}
lean_ctor_set(x_358, 0, x_357);
lean_ctor_set(x_358, 1, x_353);
lean_ctor_set(x_358, 2, x_354);
lean_ctor_set(x_358, 3, x_141);
lean_ctor_set(x_358, 4, x_257);
lean_ctor_set(x_5, 4, x_358);
lean_ctor_set(x_5, 0, x_356);
return x_5;
}
else
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; 
lean_dec(x_137);
x_359 = lean_ctor_get(x_256, 0);
lean_inc(x_359);
x_360 = lean_ctor_get(x_256, 1);
lean_inc(x_360);
lean_dec(x_256);
x_361 = lean_unsigned_to_nat(3u);
if (lean_is_scalar(x_255)) {
 x_362 = lean_alloc_ctor(0, 5, 0);
} else {
 x_362 = x_255;
}
lean_ctor_set(x_362, 0, x_147);
lean_ctor_set(x_362, 1, x_359);
lean_ctor_set(x_362, 2, x_360);
lean_ctor_set(x_362, 3, x_141);
lean_ctor_set(x_362, 4, x_141);
lean_ctor_set(x_5, 4, x_362);
lean_ctor_set(x_5, 0, x_361);
return x_5;
}
}
else
{
lean_dec(x_5);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; 
x_363 = lean_ctor_get(x_256, 0);
lean_inc(x_363);
x_364 = lean_ctor_get(x_256, 1);
lean_inc(x_364);
lean_dec(x_256);
x_365 = lean_ctor_get(x_141, 0);
lean_inc(x_365);
x_366 = lean_nat_add(x_147, x_137);
lean_dec(x_137);
x_367 = lean_nat_add(x_147, x_365);
lean_dec(x_365);
if (lean_is_scalar(x_255)) {
 x_368 = lean_alloc_ctor(0, 5, 0);
} else {
 x_368 = x_255;
}
lean_ctor_set(x_368, 0, x_367);
lean_ctor_set(x_368, 1, x_363);
lean_ctor_set(x_368, 2, x_364);
lean_ctor_set(x_368, 3, x_141);
lean_ctor_set(x_368, 4, x_257);
x_369 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_369, 0, x_366);
lean_ctor_set(x_369, 1, x_138);
lean_ctor_set(x_369, 2, x_139);
lean_ctor_set(x_369, 3, x_140);
lean_ctor_set(x_369, 4, x_368);
return x_369;
}
else
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; 
lean_dec(x_137);
x_370 = lean_ctor_get(x_256, 0);
lean_inc(x_370);
x_371 = lean_ctor_get(x_256, 1);
lean_inc(x_371);
lean_dec(x_256);
x_372 = lean_unsigned_to_nat(3u);
if (lean_is_scalar(x_255)) {
 x_373 = lean_alloc_ctor(0, 5, 0);
} else {
 x_373 = x_255;
}
lean_ctor_set(x_373, 0, x_147);
lean_ctor_set(x_373, 1, x_370);
lean_ctor_set(x_373, 2, x_371);
lean_ctor_set(x_373, 3, x_141);
lean_ctor_set(x_373, 4, x_141);
x_374 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_374, 0, x_372);
lean_ctor_set(x_374, 1, x_138);
lean_ctor_set(x_374, 2, x_139);
lean_ctor_set(x_374, 3, x_140);
lean_ctor_set(x_374, 4, x_373);
return x_374;
}
}
}
else
{
lean_dec(x_137);
if (lean_obj_tag(x_141) == 0)
{
uint8_t x_375; 
x_375 = !lean_is_exclusive(x_5);
if (x_375 == 0)
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; uint8_t x_383; 
x_376 = lean_ctor_get(x_5, 4);
lean_dec(x_376);
x_377 = lean_ctor_get(x_5, 3);
lean_dec(x_377);
x_378 = lean_ctor_get(x_5, 2);
lean_dec(x_378);
x_379 = lean_ctor_get(x_5, 1);
lean_dec(x_379);
x_380 = lean_ctor_get(x_5, 0);
lean_dec(x_380);
x_381 = lean_ctor_get(x_256, 0);
lean_inc(x_381);
x_382 = lean_ctor_get(x_256, 1);
lean_inc(x_382);
lean_dec(x_256);
x_383 = !lean_is_exclusive(x_141);
if (x_383 == 0)
{
lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; 
x_384 = lean_ctor_get(x_141, 1);
x_385 = lean_ctor_get(x_141, 2);
x_386 = lean_ctor_get(x_141, 4);
lean_dec(x_386);
x_387 = lean_ctor_get(x_141, 3);
lean_dec(x_387);
x_388 = lean_ctor_get(x_141, 0);
lean_dec(x_388);
x_389 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_141, 4, x_140);
lean_ctor_set(x_141, 3, x_140);
lean_ctor_set(x_141, 2, x_139);
lean_ctor_set(x_141, 1, x_138);
lean_ctor_set(x_141, 0, x_147);
if (lean_is_scalar(x_255)) {
 x_390 = lean_alloc_ctor(0, 5, 0);
} else {
 x_390 = x_255;
}
lean_ctor_set(x_390, 0, x_147);
lean_ctor_set(x_390, 1, x_381);
lean_ctor_set(x_390, 2, x_382);
lean_ctor_set(x_390, 3, x_140);
lean_ctor_set(x_390, 4, x_140);
lean_ctor_set(x_5, 4, x_390);
lean_ctor_set(x_5, 3, x_141);
lean_ctor_set(x_5, 2, x_385);
lean_ctor_set(x_5, 1, x_384);
lean_ctor_set(x_5, 0, x_389);
return x_5;
}
else
{
lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; 
x_391 = lean_ctor_get(x_141, 1);
x_392 = lean_ctor_get(x_141, 2);
lean_inc(x_392);
lean_inc(x_391);
lean_dec(x_141);
x_393 = lean_unsigned_to_nat(3u);
x_394 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_394, 0, x_147);
lean_ctor_set(x_394, 1, x_138);
lean_ctor_set(x_394, 2, x_139);
lean_ctor_set(x_394, 3, x_140);
lean_ctor_set(x_394, 4, x_140);
if (lean_is_scalar(x_255)) {
 x_395 = lean_alloc_ctor(0, 5, 0);
} else {
 x_395 = x_255;
}
lean_ctor_set(x_395, 0, x_147);
lean_ctor_set(x_395, 1, x_381);
lean_ctor_set(x_395, 2, x_382);
lean_ctor_set(x_395, 3, x_140);
lean_ctor_set(x_395, 4, x_140);
lean_ctor_set(x_5, 4, x_395);
lean_ctor_set(x_5, 3, x_394);
lean_ctor_set(x_5, 2, x_392);
lean_ctor_set(x_5, 1, x_391);
lean_ctor_set(x_5, 0, x_393);
return x_5;
}
}
else
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; 
lean_dec(x_5);
x_396 = lean_ctor_get(x_256, 0);
lean_inc(x_396);
x_397 = lean_ctor_get(x_256, 1);
lean_inc(x_397);
lean_dec(x_256);
x_398 = lean_ctor_get(x_141, 1);
lean_inc(x_398);
x_399 = lean_ctor_get(x_141, 2);
lean_inc(x_399);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 lean_ctor_release(x_141, 2);
 lean_ctor_release(x_141, 3);
 lean_ctor_release(x_141, 4);
 x_400 = x_141;
} else {
 lean_dec_ref(x_141);
 x_400 = lean_box(0);
}
x_401 = lean_unsigned_to_nat(3u);
if (lean_is_scalar(x_400)) {
 x_402 = lean_alloc_ctor(0, 5, 0);
} else {
 x_402 = x_400;
}
lean_ctor_set(x_402, 0, x_147);
lean_ctor_set(x_402, 1, x_138);
lean_ctor_set(x_402, 2, x_139);
lean_ctor_set(x_402, 3, x_140);
lean_ctor_set(x_402, 4, x_140);
if (lean_is_scalar(x_255)) {
 x_403 = lean_alloc_ctor(0, 5, 0);
} else {
 x_403 = x_255;
}
lean_ctor_set(x_403, 0, x_147);
lean_ctor_set(x_403, 1, x_396);
lean_ctor_set(x_403, 2, x_397);
lean_ctor_set(x_403, 3, x_140);
lean_ctor_set(x_403, 4, x_140);
x_404 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_404, 0, x_401);
lean_ctor_set(x_404, 1, x_398);
lean_ctor_set(x_404, 2, x_399);
lean_ctor_set(x_404, 3, x_402);
lean_ctor_set(x_404, 4, x_403);
return x_404;
}
}
else
{
lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; 
lean_dec(x_139);
lean_dec(x_138);
x_405 = lean_ctor_get(x_256, 0);
lean_inc(x_405);
x_406 = lean_ctor_get(x_256, 1);
lean_inc(x_406);
lean_dec(x_256);
x_407 = lean_unsigned_to_nat(2u);
if (lean_is_scalar(x_255)) {
 x_408 = lean_alloc_ctor(0, 5, 0);
} else {
 x_408 = x_255;
}
lean_ctor_set(x_408, 0, x_407);
lean_ctor_set(x_408, 1, x_405);
lean_ctor_set(x_408, 2, x_406);
lean_ctor_set(x_408, 3, x_5);
lean_ctor_set(x_408, 4, x_141);
return x_408;
}
}
}
}
}
else
{
return x_5;
}
}
else
{
return x_6;
}
}
default: 
{
lean_object* x_409; lean_object* x_410; 
x_409 = l_Std_DTreeMap_Internal_Impl_erase___at___Lean_Server_FileWorker_WorkerContext_resolveServerRequestResponse_spec__0___redArg(x_1, x_6);
x_410 = lean_unsigned_to_nat(1u);
if (lean_obj_tag(x_409) == 0)
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; uint8_t x_419; 
x_411 = lean_ctor_get(x_409, 0);
lean_inc(x_411);
x_412 = lean_ctor_get(x_5, 0);
lean_inc(x_412);
x_413 = lean_ctor_get(x_5, 1);
lean_inc(x_413);
x_414 = lean_ctor_get(x_5, 2);
lean_inc(x_414);
x_415 = lean_ctor_get(x_5, 3);
lean_inc(x_415);
x_416 = lean_ctor_get(x_5, 4);
lean_inc(x_416);
x_417 = lean_unsigned_to_nat(3u);
x_418 = lean_nat_mul(x_417, x_411);
x_419 = lean_nat_dec_lt(x_418, x_412);
lean_dec(x_418);
if (x_419 == 0)
{
lean_object* x_420; lean_object* x_421; lean_object* x_422; 
lean_dec(x_416);
lean_dec(x_415);
lean_dec(x_414);
lean_dec(x_413);
x_420 = lean_nat_add(x_410, x_412);
lean_dec(x_412);
x_421 = lean_nat_add(x_420, x_411);
lean_dec(x_411);
lean_dec(x_420);
if (lean_is_scalar(x_7)) {
 x_422 = lean_alloc_ctor(0, 5, 0);
} else {
 x_422 = x_7;
}
lean_ctor_set(x_422, 0, x_421);
lean_ctor_set(x_422, 1, x_3);
lean_ctor_set(x_422, 2, x_4);
lean_ctor_set(x_422, 3, x_5);
lean_ctor_set(x_422, 4, x_409);
return x_422;
}
else
{
lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; uint8_t x_431; 
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 lean_ctor_release(x_5, 2);
 lean_ctor_release(x_5, 3);
 lean_ctor_release(x_5, 4);
 x_423 = x_5;
} else {
 lean_dec_ref(x_5);
 x_423 = lean_box(0);
}
x_424 = lean_ctor_get(x_415, 0);
lean_inc(x_424);
x_425 = lean_ctor_get(x_416, 0);
lean_inc(x_425);
x_426 = lean_ctor_get(x_416, 1);
lean_inc(x_426);
x_427 = lean_ctor_get(x_416, 2);
lean_inc(x_427);
x_428 = lean_ctor_get(x_416, 3);
lean_inc(x_428);
x_429 = lean_ctor_get(x_416, 4);
lean_inc(x_429);
x_430 = lean_nat_shiftl(x_424, x_410);
x_431 = lean_nat_dec_lt(x_425, x_430);
lean_dec(x_430);
if (x_431 == 0)
{
lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_442; lean_object* x_443; 
lean_dec(x_425);
if (lean_is_exclusive(x_416)) {
 lean_ctor_release(x_416, 0);
 lean_ctor_release(x_416, 1);
 lean_ctor_release(x_416, 2);
 lean_ctor_release(x_416, 3);
 lean_ctor_release(x_416, 4);
 x_432 = x_416;
} else {
 lean_dec_ref(x_416);
 x_432 = lean_box(0);
}
x_433 = lean_nat_add(x_410, x_412);
lean_dec(x_412);
x_434 = lean_nat_add(x_433, x_411);
lean_dec(x_433);
x_442 = lean_nat_add(x_410, x_424);
lean_dec(x_424);
if (lean_obj_tag(x_428) == 0)
{
lean_object* x_450; 
x_450 = lean_ctor_get(x_428, 0);
lean_inc(x_450);
x_443 = x_450;
goto block_449;
}
else
{
lean_object* x_451; 
x_451 = lean_unsigned_to_nat(0u);
x_443 = x_451;
goto block_449;
}
block_441:
{
lean_object* x_438; lean_object* x_439; lean_object* x_440; 
x_438 = lean_nat_add(x_435, x_437);
lean_dec(x_437);
lean_dec(x_435);
if (lean_is_scalar(x_432)) {
 x_439 = lean_alloc_ctor(0, 5, 0);
} else {
 x_439 = x_432;
}
lean_ctor_set(x_439, 0, x_438);
lean_ctor_set(x_439, 1, x_3);
lean_ctor_set(x_439, 2, x_4);
lean_ctor_set(x_439, 3, x_429);
lean_ctor_set(x_439, 4, x_409);
if (lean_is_scalar(x_423)) {
 x_440 = lean_alloc_ctor(0, 5, 0);
} else {
 x_440 = x_423;
}
lean_ctor_set(x_440, 0, x_434);
lean_ctor_set(x_440, 1, x_426);
lean_ctor_set(x_440, 2, x_427);
lean_ctor_set(x_440, 3, x_436);
lean_ctor_set(x_440, 4, x_439);
return x_440;
}
block_449:
{
lean_object* x_444; lean_object* x_445; lean_object* x_446; 
x_444 = lean_nat_add(x_442, x_443);
lean_dec(x_443);
lean_dec(x_442);
if (lean_is_scalar(x_7)) {
 x_445 = lean_alloc_ctor(0, 5, 0);
} else {
 x_445 = x_7;
}
lean_ctor_set(x_445, 0, x_444);
lean_ctor_set(x_445, 1, x_413);
lean_ctor_set(x_445, 2, x_414);
lean_ctor_set(x_445, 3, x_415);
lean_ctor_set(x_445, 4, x_428);
x_446 = lean_nat_add(x_410, x_411);
lean_dec(x_411);
if (lean_obj_tag(x_429) == 0)
{
lean_object* x_447; 
x_447 = lean_ctor_get(x_429, 0);
lean_inc(x_447);
x_435 = x_446;
x_436 = x_445;
x_437 = x_447;
goto block_441;
}
else
{
lean_object* x_448; 
x_448 = lean_unsigned_to_nat(0u);
x_435 = x_446;
x_436 = x_445;
x_437 = x_448;
goto block_441;
}
}
}
else
{
lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; uint8_t x_457; 
lean_dec(x_429);
lean_dec(x_428);
lean_dec(x_427);
lean_dec(x_426);
lean_dec(x_424);
lean_dec(x_7);
x_452 = lean_nat_add(x_410, x_412);
lean_dec(x_412);
x_453 = lean_nat_add(x_452, x_411);
lean_dec(x_452);
x_454 = lean_nat_add(x_410, x_411);
lean_dec(x_411);
x_455 = lean_nat_add(x_454, x_425);
lean_dec(x_425);
lean_dec(x_454);
lean_inc(x_409);
if (lean_is_scalar(x_423)) {
 x_456 = lean_alloc_ctor(0, 5, 0);
} else {
 x_456 = x_423;
}
lean_ctor_set(x_456, 0, x_455);
lean_ctor_set(x_456, 1, x_3);
lean_ctor_set(x_456, 2, x_4);
lean_ctor_set(x_456, 3, x_416);
lean_ctor_set(x_456, 4, x_409);
x_457 = !lean_is_exclusive(x_409);
if (x_457 == 0)
{
lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; 
x_458 = lean_ctor_get(x_409, 4);
lean_dec(x_458);
x_459 = lean_ctor_get(x_409, 3);
lean_dec(x_459);
x_460 = lean_ctor_get(x_409, 2);
lean_dec(x_460);
x_461 = lean_ctor_get(x_409, 1);
lean_dec(x_461);
x_462 = lean_ctor_get(x_409, 0);
lean_dec(x_462);
lean_ctor_set(x_409, 4, x_456);
lean_ctor_set(x_409, 3, x_415);
lean_ctor_set(x_409, 2, x_414);
lean_ctor_set(x_409, 1, x_413);
lean_ctor_set(x_409, 0, x_453);
return x_409;
}
else
{
lean_object* x_463; 
lean_dec(x_409);
x_463 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_463, 0, x_453);
lean_ctor_set(x_463, 1, x_413);
lean_ctor_set(x_463, 2, x_414);
lean_ctor_set(x_463, 3, x_415);
lean_ctor_set(x_463, 4, x_456);
return x_463;
}
}
}
}
else
{
lean_object* x_464; lean_object* x_465; lean_object* x_466; 
x_464 = lean_ctor_get(x_409, 0);
lean_inc(x_464);
x_465 = lean_nat_add(x_410, x_464);
lean_dec(x_464);
if (lean_is_scalar(x_7)) {
 x_466 = lean_alloc_ctor(0, 5, 0);
} else {
 x_466 = x_7;
}
lean_ctor_set(x_466, 0, x_465);
lean_ctor_set(x_466, 1, x_3);
lean_ctor_set(x_466, 2, x_4);
lean_ctor_set(x_466, 3, x_5);
lean_ctor_set(x_466, 4, x_409);
return x_466;
}
}
else
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_467; 
x_467 = lean_ctor_get(x_5, 3);
lean_inc(x_467);
if (lean_obj_tag(x_467) == 0)
{
lean_object* x_468; 
x_468 = lean_ctor_get(x_5, 4);
lean_inc(x_468);
if (lean_obj_tag(x_468) == 0)
{
uint8_t x_469; 
x_469 = !lean_is_exclusive(x_5);
if (x_469 == 0)
{
lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; 
x_470 = lean_ctor_get(x_5, 0);
x_471 = lean_ctor_get(x_5, 1);
x_472 = lean_ctor_get(x_5, 2);
x_473 = lean_ctor_get(x_5, 4);
lean_dec(x_473);
x_474 = lean_ctor_get(x_5, 3);
lean_dec(x_474);
x_475 = lean_ctor_get(x_468, 0);
lean_inc(x_475);
x_476 = lean_nat_add(x_410, x_470);
lean_dec(x_470);
x_477 = lean_nat_add(x_410, x_475);
lean_dec(x_475);
lean_ctor_set(x_5, 4, x_409);
lean_ctor_set(x_5, 3, x_468);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 0, x_477);
if (lean_is_scalar(x_7)) {
 x_478 = lean_alloc_ctor(0, 5, 0);
} else {
 x_478 = x_7;
}
lean_ctor_set(x_478, 0, x_476);
lean_ctor_set(x_478, 1, x_471);
lean_ctor_set(x_478, 2, x_472);
lean_ctor_set(x_478, 3, x_467);
lean_ctor_set(x_478, 4, x_5);
return x_478;
}
else
{
lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; 
x_479 = lean_ctor_get(x_5, 0);
x_480 = lean_ctor_get(x_5, 1);
x_481 = lean_ctor_get(x_5, 2);
lean_inc(x_481);
lean_inc(x_480);
lean_inc(x_479);
lean_dec(x_5);
x_482 = lean_ctor_get(x_468, 0);
lean_inc(x_482);
x_483 = lean_nat_add(x_410, x_479);
lean_dec(x_479);
x_484 = lean_nat_add(x_410, x_482);
lean_dec(x_482);
x_485 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_485, 0, x_484);
lean_ctor_set(x_485, 1, x_3);
lean_ctor_set(x_485, 2, x_4);
lean_ctor_set(x_485, 3, x_468);
lean_ctor_set(x_485, 4, x_409);
if (lean_is_scalar(x_7)) {
 x_486 = lean_alloc_ctor(0, 5, 0);
} else {
 x_486 = x_7;
}
lean_ctor_set(x_486, 0, x_483);
lean_ctor_set(x_486, 1, x_480);
lean_ctor_set(x_486, 2, x_481);
lean_ctor_set(x_486, 3, x_467);
lean_ctor_set(x_486, 4, x_485);
return x_486;
}
}
else
{
uint8_t x_487; 
x_487 = !lean_is_exclusive(x_5);
if (x_487 == 0)
{
lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; 
x_488 = lean_ctor_get(x_5, 1);
x_489 = lean_ctor_get(x_5, 2);
x_490 = lean_ctor_get(x_5, 4);
lean_dec(x_490);
x_491 = lean_ctor_get(x_5, 3);
lean_dec(x_491);
x_492 = lean_ctor_get(x_5, 0);
lean_dec(x_492);
x_493 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_5, 3, x_468);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 0, x_410);
if (lean_is_scalar(x_7)) {
 x_494 = lean_alloc_ctor(0, 5, 0);
} else {
 x_494 = x_7;
}
lean_ctor_set(x_494, 0, x_493);
lean_ctor_set(x_494, 1, x_488);
lean_ctor_set(x_494, 2, x_489);
lean_ctor_set(x_494, 3, x_467);
lean_ctor_set(x_494, 4, x_5);
return x_494;
}
else
{
lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; 
x_495 = lean_ctor_get(x_5, 1);
x_496 = lean_ctor_get(x_5, 2);
lean_inc(x_496);
lean_inc(x_495);
lean_dec(x_5);
x_497 = lean_unsigned_to_nat(3u);
x_498 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_498, 0, x_410);
lean_ctor_set(x_498, 1, x_3);
lean_ctor_set(x_498, 2, x_4);
lean_ctor_set(x_498, 3, x_468);
lean_ctor_set(x_498, 4, x_468);
if (lean_is_scalar(x_7)) {
 x_499 = lean_alloc_ctor(0, 5, 0);
} else {
 x_499 = x_7;
}
lean_ctor_set(x_499, 0, x_497);
lean_ctor_set(x_499, 1, x_495);
lean_ctor_set(x_499, 2, x_496);
lean_ctor_set(x_499, 3, x_467);
lean_ctor_set(x_499, 4, x_498);
return x_499;
}
}
}
else
{
lean_object* x_500; 
x_500 = lean_ctor_get(x_5, 4);
lean_inc(x_500);
if (lean_obj_tag(x_500) == 0)
{
uint8_t x_501; 
x_501 = !lean_is_exclusive(x_5);
if (x_501 == 0)
{
lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; uint8_t x_507; 
x_502 = lean_ctor_get(x_5, 1);
x_503 = lean_ctor_get(x_5, 2);
x_504 = lean_ctor_get(x_5, 4);
lean_dec(x_504);
x_505 = lean_ctor_get(x_5, 3);
lean_dec(x_505);
x_506 = lean_ctor_get(x_5, 0);
lean_dec(x_506);
x_507 = !lean_is_exclusive(x_500);
if (x_507 == 0)
{
lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; 
x_508 = lean_ctor_get(x_500, 1);
x_509 = lean_ctor_get(x_500, 2);
x_510 = lean_ctor_get(x_500, 4);
lean_dec(x_510);
x_511 = lean_ctor_get(x_500, 3);
lean_dec(x_511);
x_512 = lean_ctor_get(x_500, 0);
lean_dec(x_512);
x_513 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_500, 4, x_467);
lean_ctor_set(x_500, 3, x_467);
lean_ctor_set(x_500, 2, x_503);
lean_ctor_set(x_500, 1, x_502);
lean_ctor_set(x_500, 0, x_410);
lean_ctor_set(x_5, 4, x_467);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 0, x_410);
if (lean_is_scalar(x_7)) {
 x_514 = lean_alloc_ctor(0, 5, 0);
} else {
 x_514 = x_7;
}
lean_ctor_set(x_514, 0, x_513);
lean_ctor_set(x_514, 1, x_508);
lean_ctor_set(x_514, 2, x_509);
lean_ctor_set(x_514, 3, x_500);
lean_ctor_set(x_514, 4, x_5);
return x_514;
}
else
{
lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; 
x_515 = lean_ctor_get(x_500, 1);
x_516 = lean_ctor_get(x_500, 2);
lean_inc(x_516);
lean_inc(x_515);
lean_dec(x_500);
x_517 = lean_unsigned_to_nat(3u);
x_518 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_518, 0, x_410);
lean_ctor_set(x_518, 1, x_502);
lean_ctor_set(x_518, 2, x_503);
lean_ctor_set(x_518, 3, x_467);
lean_ctor_set(x_518, 4, x_467);
lean_ctor_set(x_5, 4, x_467);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 0, x_410);
if (lean_is_scalar(x_7)) {
 x_519 = lean_alloc_ctor(0, 5, 0);
} else {
 x_519 = x_7;
}
lean_ctor_set(x_519, 0, x_517);
lean_ctor_set(x_519, 1, x_515);
lean_ctor_set(x_519, 2, x_516);
lean_ctor_set(x_519, 3, x_518);
lean_ctor_set(x_519, 4, x_5);
return x_519;
}
}
else
{
lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; 
x_520 = lean_ctor_get(x_5, 1);
x_521 = lean_ctor_get(x_5, 2);
lean_inc(x_521);
lean_inc(x_520);
lean_dec(x_5);
x_522 = lean_ctor_get(x_500, 1);
lean_inc(x_522);
x_523 = lean_ctor_get(x_500, 2);
lean_inc(x_523);
if (lean_is_exclusive(x_500)) {
 lean_ctor_release(x_500, 0);
 lean_ctor_release(x_500, 1);
 lean_ctor_release(x_500, 2);
 lean_ctor_release(x_500, 3);
 lean_ctor_release(x_500, 4);
 x_524 = x_500;
} else {
 lean_dec_ref(x_500);
 x_524 = lean_box(0);
}
x_525 = lean_unsigned_to_nat(3u);
if (lean_is_scalar(x_524)) {
 x_526 = lean_alloc_ctor(0, 5, 0);
} else {
 x_526 = x_524;
}
lean_ctor_set(x_526, 0, x_410);
lean_ctor_set(x_526, 1, x_520);
lean_ctor_set(x_526, 2, x_521);
lean_ctor_set(x_526, 3, x_467);
lean_ctor_set(x_526, 4, x_467);
x_527 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_527, 0, x_410);
lean_ctor_set(x_527, 1, x_3);
lean_ctor_set(x_527, 2, x_4);
lean_ctor_set(x_527, 3, x_467);
lean_ctor_set(x_527, 4, x_467);
if (lean_is_scalar(x_7)) {
 x_528 = lean_alloc_ctor(0, 5, 0);
} else {
 x_528 = x_7;
}
lean_ctor_set(x_528, 0, x_525);
lean_ctor_set(x_528, 1, x_522);
lean_ctor_set(x_528, 2, x_523);
lean_ctor_set(x_528, 3, x_526);
lean_ctor_set(x_528, 4, x_527);
return x_528;
}
}
else
{
lean_object* x_529; lean_object* x_530; 
x_529 = lean_unsigned_to_nat(2u);
if (lean_is_scalar(x_7)) {
 x_530 = lean_alloc_ctor(0, 5, 0);
} else {
 x_530 = x_7;
}
lean_ctor_set(x_530, 0, x_529);
lean_ctor_set(x_530, 1, x_3);
lean_ctor_set(x_530, 2, x_4);
lean_ctor_set(x_530, 3, x_5);
lean_ctor_set(x_530, 4, x_500);
return x_530;
}
}
}
else
{
lean_object* x_531; 
if (lean_is_scalar(x_7)) {
 x_531 = lean_alloc_ctor(0, 5, 0);
} else {
 x_531 = x_7;
}
lean_ctor_set(x_531, 0, x_410);
lean_ctor_set(x_531, 1, x_3);
lean_ctor_set(x_531, 2, x_4);
lean_ctor_set(x_531, 3, x_5);
lean_ctor_set(x_531, 4, x_5);
return x_531;
}
}
}
}
}
else
{
lean_dec(x_1);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___Lean_Server_FileWorker_WorkerContext_resolveServerRequestResponse_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DTreeMap_Internal_Impl_erase___at___Lean_Server_FileWorker_WorkerContext_resolveServerRequestResponse_spec__0___redArg(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___Lean_Server_FileWorker_WorkerContext_resolveServerRequestResponse_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 3);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 4);
lean_inc(x_6);
lean_dec(x_1);
lean_inc(x_2);
x_7 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_ordRequestID____x40_Lean_Data_JsonRpc___hyg_126_(x_2, x_3);
switch (x_7) {
case 0:
{
lean_dec(x_6);
lean_dec(x_4);
x_1 = x_5;
goto _start;
}
case 1:
{
lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_4);
return x_9;
}
default: 
{
lean_dec(x_5);
lean_dec(x_4);
x_1 = x_6;
goto _start;
}
}
}
else
{
lean_object* x_11; 
lean_dec(x_2);
x_11 = lean_box(0);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___Lean_Server_FileWorker_WorkerContext_resolveServerRequestResponse_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___Lean_Server_FileWorker_WorkerContext_resolveServerRequestResponse_spec__1___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_WorkerContext_resolveServerRequestResponse(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_5 = lean_ctor_get(x_1, 5);
x_6 = lean_st_ref_take(x_5, x_4);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
lean_inc(x_7);
lean_inc(x_2);
x_9 = l_Std_DTreeMap_Internal_Impl_erase___at___Lean_Server_FileWorker_WorkerContext_resolveServerRequestResponse_spec__0___redArg(x_2, x_7);
x_10 = lean_st_ref_set(x_5, x_9, x_8);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 1);
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
x_14 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___Lean_Server_FileWorker_WorkerContext_resolveServerRequestResponse_spec__1___redArg(x_7, x_2);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
lean_dec(x_3);
x_15 = lean_box(0);
lean_ctor_set(x_10, 0, x_15);
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_free_object(x_10);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_io_promise_resolve(x_3, x_16, x_12);
lean_dec(x_16);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_10, 1);
lean_inc(x_18);
lean_dec(x_10);
x_19 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___Lean_Server_FileWorker_WorkerContext_resolveServerRequestResponse_spec__1___redArg(x_7, x_2);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_3);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_18);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_io_promise_resolve(x_3, x_22, x_18);
lean_dec(x_22);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_WorkerContext_resolveServerRequestResponse___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_FileWorker_WorkerContext_resolveServerRequestResponse(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_mkIleanInfoNotification(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_5 = lean_ctor_get(x_2, 3);
lean_inc(x_5);
x_6 = lean_box(1);
x_7 = lean_box(0);
x_8 = lean_unbox(x_6);
x_9 = lean_unbox(x_7);
x_10 = l_Lean_Server_findModuleRefs(x_5, x_3, x_8, x_9);
x_11 = l_Lean_Server_ModuleRefs_toLspModuleRefs(x_10, x_4);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_2, 2);
lean_inc(x_14);
lean_dec(x_2);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set(x_11, 0, x_16);
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_11, 0);
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_11);
x_19 = lean_ctor_get(x_2, 2);
lean_inc(x_19);
lean_dec(x_2);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_17);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_18);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_mkIleanInfoNotification___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_mkIleanInfoNotification(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_mkIleanInfoUpdateNotification(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_mk_string_unchecked("$/lean/ileanInfoUpdate", 22, 22);
x_5 = l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_mkIleanInfoNotification(x_4, x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_mkIleanInfoUpdateNotification___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_mkIleanInfoUpdateNotification(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_mkIleanInfoFinalNotification(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_mk_string_unchecked("$/lean/ileanInfoFinal", 21, 21);
x_5 = l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_mkIleanInfoNotification(x_4, x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_mkIleanInfoFinalNotification___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_mkIleanInfoFinalNotification(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_mkImportClosureNotification(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_mk_string_unchecked("$/lean/importClosure", 20, 20);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instInhabitedReportSnapshotsState() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; uint8_t x_5; 
x_1 = lean_box(0);
x_2 = l_Array_empty(lean_box(0));
lean_inc(x_2);
x_3 = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
x_4 = lean_unbox(x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*2, x_4);
x_5 = lean_unbox(x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*2 + 1, x_5);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker___hyg_753_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = lean_mk_string_unchecked("server", 6, 6);
x_3 = lean_mk_string_unchecked("reportDelayMs", 13, 13);
lean_inc(x_3);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_unsigned_to_nat(200u);
x_6 = lean_mk_string_unchecked("(server) time in milliseconds to wait before reporting progress and diagnostics on document edit in order to reduce flickering\n\nThis option can only be set on the command line, not in the lakefile or via `set_option`.", 217, 217);
lean_inc(x_2);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 2, x_6);
x_8 = lean_mk_string_unchecked("Lean", 4, 4);
x_9 = lean_mk_string_unchecked("Server", 6, 6);
x_10 = lean_mk_string_unchecked("FileWorker", 10, 10);
x_11 = l_Lean_Name_mkStr5(x_8, x_9, x_10, x_2, x_3);
x_12 = l_Lean_Option_register___at___Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Options___hyg_5__spec__0(x_4, x_7, x_11, x_1);
lean_dec(x_7);
return x_12;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instImpl____x40_Lean_Server_FileWorker___hyg_804_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Server", 6, 6);
x_3 = lean_mk_string_unchecked("FileWorker", 10, 10);
x_4 = lean_mk_string_unchecked("MemorizedInteractiveDiagnostics", 31, 31);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instTypeNameMemorizedInteractiveDiagnostics() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Server_FileWorker_instImpl____x40_Lean_Server_FileWorker___hyg_804_;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_publishDiagnostics_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_8 = l_Lean_Widget_InteractiveDiagnostic_toDiagnostic(x_5);
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
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_publishDiagnostics_spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Data_Lsp_Diagnostics_0__Lean_Lsp_toJsonPublishDiagnosticsParams____x40_Lean_Data_Lsp_Diagnostics___hyg_2428_(x_1);
if (lean_obj_tag(x_2) == 5)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; 
lean_ctor_set_tag(x_2, 1);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_2);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_mk_string_unchecked("expected structured object, got '", 33, 33);
x_9 = lean_unsigned_to_nat(80u);
x_10 = l_Lean_Json_pretty(x_2, x_9);
x_11 = lean_string_append(x_8, x_10);
lean_dec(x_10);
x_12 = lean_mk_string_unchecked("'", 1, 1);
x_13 = lean_string_append(x_11, x_12);
lean_dec(x_12);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_publishDiagnostics(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; lean_object* x_15; size_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_26; lean_object* x_27; 
x_4 = lean_ctor_get(x_1, 3);
lean_inc(x_4);
x_5 = lean_st_ref_get(x_4, x_3);
lean_dec(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_2, 3);
lean_inc(x_8);
x_9 = lean_st_ref_get(x_8, x_7);
lean_dec(x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_12 = x_9;
} else {
 lean_dec_ref(x_9);
 x_12 = lean_box(0);
}
x_13 = l_Array_append(lean_box(0), x_6, x_10);
lean_dec(x_10);
x_14 = lean_array_size(x_13);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_usize_of_nat(x_15);
x_17 = l_Array_mapMUnsafe_map___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_publishDiagnostics_spec__0(x_14, x_16, x_13);
x_18 = lean_ctor_get(x_2, 0);
lean_inc(x_18);
lean_dec(x_2);
x_19 = l_Lean_Server_mkPublishDiagnosticsNotification(x_18, x_17);
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
lean_dec(x_1);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_26 = lean_ctor_get(x_19, 1);
lean_inc(x_26);
lean_dec(x_19);
x_27 = l_Lean_Json_toStructured_x3f___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_publishDiagnostics_spec__1(x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
lean_dec(x_27);
x_28 = lean_box(0);
x_22 = x_28;
goto block_25;
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_27);
if (x_29 == 0)
{
x_22 = x_27;
goto block_25;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 0);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_22 = x_31;
goto block_25;
}
}
block_25:
{
lean_object* x_23; lean_object* x_24; 
if (lean_is_scalar(x_12)) {
 x_23 = lean_alloc_ctor(1, 2, 0);
} else {
 x_23 = x_12;
 lean_ctor_set_tag(x_23, 1);
}
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Std_Channel_Sync_send___redArg(x_20, x_23, x_11);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_publishDiagnostics_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_publishDiagnostics_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_sendFileProgress_spec__0_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_2, x_3);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_array_uget(x_1, x_2);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
if (lean_obj_tag(x_13) == 0)
{
x_5 = x_4;
goto block_10;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_array_push(x_4, x_14);
x_5 = x_15;
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
LEAN_EXPORT lean_object* l_Array_filterMapM___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_sendFileProgress_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_mk_empty_array_with_capacity(x_4);
x_6 = lean_nat_dec_lt(x_2, x_3);
if (x_6 == 0)
{
return x_5;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_1);
x_8 = lean_nat_dec_le(x_3, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
return x_5;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_usize_of_nat(x_2);
x_10 = lean_usize_of_nat(x_3);
x_11 = l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_sendFileProgress_spec__0_spec__0(x_1, x_9, x_10, x_5);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_sendFileProgress_spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_box(0);
x_8 = lean_array_uset(x_4, x_3, x_7);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 3);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_String_Range_toLspRange(x_10, x_6);
lean_dec(x_6);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_usize_of_nat(x_12);
x_14 = lean_usize_add(x_3, x_13);
x_15 = lean_array_uset(x_8, x_3, x_11);
x_3 = x_14;
x_4 = x_15;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_sendFileProgress_spec__3(size_t x_1, size_t x_2, lean_object* x_3) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_box(0);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_9, 0, x_5);
x_10 = lean_unbox(x_8);
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_10);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_usize_of_nat(x_11);
x_13 = lean_usize_add(x_2, x_12);
x_14 = lean_array_uset(x_7, x_2, x_9);
x_2 = x_13;
x_3 = x_14;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_sendFileProgress_spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Data_Lsp_Extra_0__Lean_Lsp_toJsonLeanFileProgressParams____x40_Lean_Data_Lsp_Extra___hyg_1231_(x_1);
if (lean_obj_tag(x_2) == 5)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; 
lean_ctor_set_tag(x_2, 1);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_2);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_mk_string_unchecked("expected structured object, got '", 33, 33);
x_9 = lean_unsigned_to_nat(80u);
x_10 = l_Lean_Json_pretty(x_2, x_9);
x_11 = lean_string_append(x_8, x_10);
lean_dec(x_10);
x_12 = lean_mk_string_unchecked("'", 1, 1);
x_13 = lean_string_append(x_11, x_12);
lean_dec(x_12);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_sendFileProgress_spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_6 = lean_unsigned_to_nat(1u);
x_12 = lean_array_uget(x_1, x_2);
x_13 = lean_array_get_size(x_4);
x_14 = lean_nat_sub(x_13, x_6);
x_15 = lean_nat_dec_lt(x_14, x_13);
lean_dec(x_13);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_14);
x_16 = lean_array_push(x_4, x_12);
x_7 = x_16;
goto block_11;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_array_fget(x_4, x_14);
lean_dec(x_14);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_12, 0);
lean_inc(x_19);
x_20 = lean_nat_dec_lt(x_18, x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_27; uint8_t x_28; 
x_21 = lean_array_pop(x_4);
x_22 = lean_ctor_get(x_17, 0);
lean_inc(x_22);
lean_dec(x_17);
x_27 = lean_ctor_get(x_12, 1);
lean_inc(x_27);
lean_dec(x_12);
x_28 = lean_nat_dec_le(x_18, x_27);
if (x_28 == 0)
{
lean_dec(x_27);
x_23 = x_18;
goto block_26;
}
else
{
lean_dec(x_18);
x_23 = x_27;
goto block_26;
}
block_26:
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_array_push(x_21, x_24);
x_7 = x_25;
goto block_11;
}
}
else
{
lean_object* x_29; 
lean_dec(x_18);
lean_dec(x_17);
x_29 = lean_array_push(x_4, x_12);
x_7 = x_29;
goto block_11;
}
}
block_11:
{
size_t x_8; size_t x_9; 
x_8 = lean_usize_of_nat(x_6);
x_9 = lean_usize_add(x_2, x_8);
x_2 = x_9;
x_4 = x_7;
goto _start;
}
}
else
{
return x_4;
}
}
}
LEAN_EXPORT uint8_t l_Array_qsort_sort___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_sendFileProgress_spec__6___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_nat_dec_lt(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_sendFileProgress_spec__6___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_lt(x_2, x_3);
if (x_4 == 0)
{
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_alloc_closure((void*)(l_Array_qsort_sort___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_sendFileProgress_spec__6___redArg___lam__0___boxed), 2, 0);
lean_inc(x_2);
x_6 = l_Array_qpartition___redArg(x_1, x_5, x_2, x_3);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_nat_dec_le(x_3, x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l_Array_qsort_sort___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_sendFileProgress_spec__6___redArg(x_8, x_2, x_7);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_7, x_11);
lean_dec(x_7);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
else
{
lean_dec(x_7);
lean_dec(x_2);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_sendFileProgress_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_qsort_sort___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_sendFileProgress_spec__6___redArg(x_2, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_sendFileProgress(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_19; lean_object* x_20; lean_object* x_37; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_19 = lean_unsigned_to_nat(0u);
x_46 = lean_array_get_size(x_3);
x_47 = l_Array_filterMapM___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_sendFileProgress_spec__0(x_3, x_19, x_46);
lean_dec(x_46);
x_48 = lean_array_get_size(x_47);
x_49 = lean_nat_dec_eq(x_48, x_19);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_55; 
x_50 = lean_unsigned_to_nat(1u);
x_51 = lean_nat_sub(x_48, x_50);
lean_dec(x_48);
x_55 = lean_nat_dec_le(x_19, x_51);
if (x_55 == 0)
{
lean_inc(x_51);
x_52 = x_51;
goto block_54;
}
else
{
x_52 = x_19;
goto block_54;
}
block_54:
{
lean_object* x_53; 
x_53 = l_Array_qsort_sort___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_sendFileProgress_spec__6___redArg(x_47, x_52, x_51);
lean_dec(x_51);
x_37 = x_53;
goto block_45;
}
}
else
{
lean_dec(x_48);
x_37 = x_47;
goto block_45;
}
block_18:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Std_Channel_Sync_send___redArg(x_7, x_9, x_5);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_4);
lean_ctor_set(x_10, 0, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_10);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_4);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
block_36:
{
size_t x_21; size_t x_22; lean_object* x_23; size_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_21 = lean_array_size(x_20);
x_22 = lean_usize_of_nat(x_19);
lean_inc(x_2);
x_23 = l_Array_mapMUnsafe_map___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_sendFileProgress_spec__2(x_2, x_21, x_22, x_20);
x_24 = lean_array_size(x_23);
x_25 = l_Array_mapMUnsafe_map___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_sendFileProgress_spec__3(x_24, x_22, x_23);
x_26 = lean_ctor_get(x_1, 0);
lean_inc(x_26);
lean_dec(x_1);
x_27 = lean_ctor_get(x_2, 0);
lean_inc(x_27);
lean_dec(x_2);
x_28 = l_Lean_Server_mkFileProgressNotification(x_27, x_25);
lean_dec(x_27);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_Lean_Json_toStructured_x3f___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_sendFileProgress_spec__4(x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
lean_dec(x_31);
x_32 = lean_box(0);
x_6 = x_29;
x_7 = x_26;
x_8 = x_32;
goto block_18;
}
else
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_31);
if (x_33 == 0)
{
x_6 = x_29;
x_7 = x_26;
x_8 = x_31;
goto block_18;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_31, 0);
lean_inc(x_34);
lean_dec(x_31);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_6 = x_29;
x_7 = x_26;
x_8 = x_35;
goto block_18;
}
}
}
block_45:
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_mk_empty_array_with_capacity(x_19);
x_39 = lean_array_get_size(x_37);
x_40 = lean_nat_dec_lt(x_19, x_39);
if (x_40 == 0)
{
lean_dec(x_39);
lean_dec(x_37);
x_20 = x_38;
goto block_36;
}
else
{
uint8_t x_41; 
x_41 = lean_nat_dec_le(x_39, x_39);
if (x_41 == 0)
{
lean_dec(x_39);
lean_dec(x_37);
x_20 = x_38;
goto block_36;
}
else
{
size_t x_42; size_t x_43; lean_object* x_44; 
x_42 = lean_usize_of_nat(x_19);
x_43 = lean_usize_of_nat(x_39);
lean_dec(x_39);
x_44 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_sendFileProgress_spec__5(x_37, x_42, x_43, x_38);
lean_dec(x_37);
x_20 = x_44;
goto block_36;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_sendFileProgress_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_sendFileProgress_spec__0_spec__0(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_sendFileProgress_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_filterMapM___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_sendFileProgress_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_sendFileProgress_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_sendFileProgress_spec__2(x_1, x_5, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_sendFileProgress_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_sendFileProgress_spec__3(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_sendFileProgress_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_sendFileProgress_spec__5(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_sendFileProgress_spec__6___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_qsort_sort___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_sendFileProgress_spec__6___redArg___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_sendFileProgress_spec__6___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_qsort_sort___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_sendFileProgress_spec__6___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_sendFileProgress_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_qsort_sort___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_sendFileProgress_spec__6(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_sendFileProgress___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_sendFileProgress(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_handleNode_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2299_(x_1);
if (lean_obj_tag(x_2) == 5)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; 
lean_ctor_set_tag(x_2, 1);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_2);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_mk_string_unchecked("expected structured object, got '", 33, 33);
x_9 = lean_unsigned_to_nat(80u);
x_10 = l_Lean_Json_pretty(x_2, x_9);
x_11 = lean_string_append(x_8, x_10);
lean_dec(x_10);
x_12 = lean_mk_string_unchecked("'", 1, 1);
x_13 = lean_string_append(x_11, x_12);
lean_dec(x_12);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_handleNode_spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_4, x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_6);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; 
x_11 = lean_array_uget(x_5, x_4);
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_12, 3);
x_14 = lean_ctor_get_uint8(x_2, sizeof(void*)*10);
x_15 = l_Lean_Widget_msgToInteractiveDiagnostic(x_13, x_11, x_14, x_7);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_box(0);
x_19 = lean_array_uset(x_5, x_4, x_18);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_usize_of_nat(x_20);
x_22 = lean_usize_add(x_4, x_21);
x_23 = lean_array_uset(x_19, x_4, x_16);
x_4 = x_22;
x_5 = x_23;
x_7 = x_17;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_handleNode_spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_2, x_3);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_uget(x_1, x_2);
x_13 = lean_ctor_get_uint8(x_12, sizeof(void*)*5 + 2);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_array_push(x_4, x_12);
x_5 = x_14;
goto block_10;
}
else
{
lean_dec(x_12);
x_5 = x_4;
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
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_handleNode___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_32; uint8_t x_69; 
x_69 = lean_ctor_get_uint8(x_5, sizeof(void*)*2 + 1);
if (x_69 == 0)
{
uint8_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; 
x_70 = lean_ctor_get_uint8(x_5, sizeof(void*)*2);
x_71 = lean_ctor_get(x_5, 0);
x_72 = lean_ctor_get(x_5, 1);
x_73 = lean_ctor_get(x_1, 0);
lean_inc(x_73);
x_74 = lean_ctor_get_uint8(x_73, sizeof(void*)*4);
lean_dec(x_73);
lean_inc(x_72);
lean_inc(x_71);
x_75 = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(x_75, 0, x_71);
lean_ctor_set(x_75, 1, x_72);
lean_ctor_set_uint8(x_75, sizeof(void*)*2, x_70);
lean_ctor_set_uint8(x_75, sizeof(void*)*2 + 1, x_74);
x_32 = x_75;
goto block_68;
}
else
{
uint8_t x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_76 = lean_ctor_get_uint8(x_5, sizeof(void*)*2);
x_77 = lean_ctor_get(x_5, 0);
x_78 = lean_ctor_get(x_5, 1);
lean_inc(x_78);
lean_inc(x_77);
x_79 = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
lean_ctor_set_uint8(x_79, sizeof(void*)*2, x_76);
lean_ctor_set_uint8(x_79, sizeof(void*)*2 + 1, x_69);
x_32 = x_79;
goto block_68;
}
block_19:
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_box(0);
x_12 = lean_ctor_get_uint8(x_9, sizeof(void*)*2);
x_13 = lean_ctor_get(x_9, 0);
lean_inc(x_13);
x_14 = lean_array_push(x_13, x_7);
x_15 = lean_ctor_get_uint8(x_9, sizeof(void*)*2 + 1);
lean_dec(x_9);
x_16 = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_8);
lean_ctor_set_uint8(x_16, sizeof(void*)*2, x_12);
lean_ctor_set_uint8(x_16, sizeof(void*)*2 + 1, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_11);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_10);
return x_18;
}
block_31:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Std_Channel_Sync_send___redArg(x_21, x_26, x_23);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_unsigned_to_nat(0u);
x_30 = lean_mk_empty_array_with_capacity(x_29);
x_7 = x_20;
x_8 = x_30;
x_9 = x_22;
x_10 = x_28;
goto block_19;
}
block_68:
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_1, 0);
lean_inc(x_33);
lean_dec(x_1);
x_34 = lean_ctor_get(x_33, 2);
lean_inc(x_34);
lean_dec(x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_3);
lean_dec(x_2);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_32);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_6);
return x_37;
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_34);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_39 = lean_ctor_get(x_34, 0);
x_40 = lean_ctor_get(x_32, 1);
lean_inc(x_40);
lean_inc(x_39);
x_41 = lean_array_push(x_40, x_39);
x_42 = lean_ctor_get_uint8(x_32, sizeof(void*)*2);
if (x_42 == 0)
{
lean_free_object(x_34);
lean_dec(x_3);
lean_dec(x_2);
x_7 = x_39;
x_8 = x_41;
x_9 = x_32;
x_10 = x_6;
goto block_19;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_43 = lean_ctor_get(x_2, 0);
lean_inc(x_43);
lean_dec(x_2);
x_44 = l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_mkIleanInfoUpdateNotification(x_43, x_41, x_6);
lean_dec(x_41);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_ctor_get(x_3, 0);
lean_inc(x_47);
lean_dec(x_3);
x_48 = lean_ctor_get(x_45, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_45, 1);
lean_inc(x_49);
lean_dec(x_45);
x_50 = l_Lean_Json_toStructured_x3f___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_handleNode_spec__0(x_49);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; 
lean_dec(x_50);
lean_free_object(x_34);
x_51 = lean_box(0);
x_20 = x_39;
x_21 = x_47;
x_22 = x_32;
x_23 = x_46;
x_24 = x_48;
x_25 = x_51;
goto block_31;
}
else
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_50, 0);
lean_inc(x_52);
lean_dec(x_50);
lean_ctor_set(x_34, 0, x_52);
x_20 = x_39;
x_21 = x_47;
x_22 = x_32;
x_23 = x_46;
x_24 = x_48;
x_25 = x_34;
goto block_31;
}
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_53 = lean_ctor_get(x_34, 0);
lean_inc(x_53);
lean_dec(x_34);
x_54 = lean_ctor_get(x_32, 1);
lean_inc(x_54);
lean_inc(x_53);
x_55 = lean_array_push(x_54, x_53);
x_56 = lean_ctor_get_uint8(x_32, sizeof(void*)*2);
if (x_56 == 0)
{
lean_dec(x_3);
lean_dec(x_2);
x_7 = x_53;
x_8 = x_55;
x_9 = x_32;
x_10 = x_6;
goto block_19;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_57 = lean_ctor_get(x_2, 0);
lean_inc(x_57);
lean_dec(x_2);
x_58 = l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_mkIleanInfoUpdateNotification(x_57, x_55, x_6);
lean_dec(x_55);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_ctor_get(x_3, 0);
lean_inc(x_61);
lean_dec(x_3);
x_62 = lean_ctor_get(x_59, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_59, 1);
lean_inc(x_63);
lean_dec(x_59);
x_64 = l_Lean_Json_toStructured_x3f___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_handleNode_spec__0(x_63);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; 
lean_dec(x_64);
x_65 = lean_box(0);
x_20 = x_53;
x_21 = x_61;
x_22 = x_32;
x_23 = x_60;
x_24 = x_62;
x_25 = x_65;
goto block_31;
}
else
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_64, 0);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_66);
x_20 = x_53;
x_21 = x_61;
x_22 = x_32;
x_23 = x_60;
x_24 = x_62;
x_25 = x_67;
goto block_31;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_handleNode___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
x_8 = lean_st_ref_take(x_7, x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Array_append(lean_box(0), x_9, x_4);
x_12 = lean_st_ref_set(x_7, x_11, x_10);
lean_dec(x_7);
x_13 = lean_ctor_get_uint8(x_5, sizeof(void*)*2);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_3);
lean_dec(x_1);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_box(0);
x_16 = lean_apply_3(x_2, x_15, x_5, x_14);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_dec(x_12);
x_18 = l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_publishDiagnostics(x_3, x_1, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_apply_3(x_2, x_19, x_5, x_20);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_handleNode(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
lean_inc(x_1);
lean_inc(x_2);
lean_inc(x_3);
x_6 = lean_alloc_closure((void*)(l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_handleNode___lam__0___boxed), 6, 3);
lean_closure_set(x_6, 0, x_3);
lean_closure_set(x_6, 1, x_2);
lean_closure_set(x_6, 2, x_1);
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = l_Lean_MessageLog_hasUnreported(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
x_11 = lean_box(0);
x_12 = l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_handleNode___lam__0(x_3, x_2, x_1, x_11, x_4, x_5);
lean_dec(x_4);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_55; lean_object* x_56; 
lean_dec(x_3);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_dec(x_8);
if (lean_obj_tag(x_13) == 0)
{
x_55 = x_4;
x_56 = x_5;
goto block_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_13, 0);
lean_inc(x_70);
x_71 = lean_st_ref_get(x_70, x_5);
lean_dec(x_70);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; 
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_55 = x_4;
x_56 = x_73;
goto block_69;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_74 = lean_ctor_get(x_71, 1);
lean_inc(x_74);
lean_dec(x_71);
x_75 = lean_ctor_get(x_72, 0);
lean_inc(x_75);
lean_dec(x_72);
x_76 = l_Lean_Server_FileWorker_instImpl____x40_Lean_Server_FileWorker___hyg_804_;
x_77 = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(x_75, x_76);
lean_dec(x_75);
if (lean_obj_tag(x_77) == 0)
{
x_55 = x_4;
x_56 = x_74;
goto block_69;
}
else
{
lean_object* x_78; lean_object* x_79; 
lean_dec(x_13);
lean_dec(x_9);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
lean_dec(x_77);
x_79 = l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_handleNode___lam__1(x_2, x_6, x_1, x_78, x_4, x_74);
lean_dec(x_78);
return x_79;
}
}
}
block_54:
{
size_t x_17; lean_object* x_18; size_t x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_array_size(x_14);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_usize_of_nat(x_18);
x_20 = l_Array_mapMUnsafe_map___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_handleNode_spec__1(x_2, x_1, x_17, x_19, x_14, x_15, x_16);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_handleNode___lam__1(x_2, x_6, x_1, x_23, x_24, x_22);
lean_dec(x_23);
return x_25;
}
else
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_20, 1);
lean_inc(x_26);
lean_dec(x_20);
x_27 = !lean_is_exclusive(x_21);
if (x_27 == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_13);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_29 = lean_ctor_get(x_21, 0);
x_30 = lean_ctor_get(x_21, 1);
x_31 = lean_ctor_get(x_13, 0);
x_32 = l_Lean_Server_FileWorker_instImpl____x40_Lean_Server_FileWorker___hyg_804_;
lean_inc(x_29);
lean_ctor_set(x_21, 1, x_29);
lean_ctor_set(x_21, 0, x_32);
lean_ctor_set(x_13, 0, x_21);
x_33 = lean_st_ref_set(x_31, x_13, x_26);
lean_dec(x_31);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_handleNode___lam__1(x_2, x_6, x_1, x_29, x_30, x_34);
lean_dec(x_29);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_36 = lean_ctor_get(x_21, 0);
x_37 = lean_ctor_get(x_21, 1);
x_38 = lean_ctor_get(x_13, 0);
lean_inc(x_38);
lean_dec(x_13);
x_39 = l_Lean_Server_FileWorker_instImpl____x40_Lean_Server_FileWorker___hyg_804_;
lean_inc(x_36);
lean_ctor_set(x_21, 1, x_36);
lean_ctor_set(x_21, 0, x_39);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_21);
x_41 = lean_st_ref_set(x_38, x_40, x_26);
lean_dec(x_38);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_43 = l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_handleNode___lam__1(x_2, x_6, x_1, x_36, x_37, x_42);
lean_dec(x_36);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_44 = lean_ctor_get(x_21, 0);
x_45 = lean_ctor_get(x_21, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_21);
x_46 = lean_ctor_get(x_13, 0);
lean_inc(x_46);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 x_47 = x_13;
} else {
 lean_dec_ref(x_13);
 x_47 = lean_box(0);
}
x_48 = l_Lean_Server_FileWorker_instImpl____x40_Lean_Server_FileWorker___hyg_804_;
lean_inc(x_44);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_44);
if (lean_is_scalar(x_47)) {
 x_50 = lean_alloc_ctor(1, 1, 0);
} else {
 x_50 = x_47;
}
lean_ctor_set(x_50, 0, x_49);
x_51 = lean_st_ref_set(x_46, x_50, x_26);
lean_dec(x_46);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec(x_51);
x_53 = l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_handleNode___lam__1(x_2, x_6, x_1, x_44, x_45, x_52);
lean_dec(x_44);
return x_53;
}
}
}
block_69:
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_57 = l_Lean_MessageLog_toArray(x_9);
lean_dec(x_9);
x_58 = lean_ctor_get(x_1, 7);
lean_inc(x_58);
x_59 = lean_ctor_get(x_58, 4);
lean_inc(x_59);
lean_dec(x_58);
x_60 = l_Lean_Lsp_ClientCapabilities_silentDiagnosticSupport(x_59);
lean_dec(x_59);
if (x_60 == 0)
{
if (x_10 == 0)
{
x_14 = x_57;
x_15 = x_55;
x_16 = x_56;
goto block_54;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_61 = lean_unsigned_to_nat(0u);
x_62 = lean_array_get_size(x_57);
x_63 = lean_mk_empty_array_with_capacity(x_61);
x_64 = lean_nat_dec_lt(x_61, x_62);
if (x_64 == 0)
{
lean_dec(x_62);
lean_dec(x_57);
x_14 = x_63;
x_15 = x_55;
x_16 = x_56;
goto block_54;
}
else
{
uint8_t x_65; 
x_65 = lean_nat_dec_le(x_62, x_62);
if (x_65 == 0)
{
lean_dec(x_62);
lean_dec(x_57);
x_14 = x_63;
x_15 = x_55;
x_16 = x_56;
goto block_54;
}
else
{
size_t x_66; size_t x_67; lean_object* x_68; 
x_66 = lean_usize_of_nat(x_61);
x_67 = lean_usize_of_nat(x_62);
lean_dec(x_62);
x_68 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_handleNode_spec__2(x_57, x_66, x_67, x_63);
lean_dec(x_57);
x_14 = x_68;
x_15 = x_55;
x_16 = x_56;
goto block_54;
}
}
}
}
else
{
x_14 = x_57;
x_15 = x_55;
x_16 = x_56;
goto block_54;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_handleNode_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l_Array_mapMUnsafe_map___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_handleNode_spec__1(x_1, x_2, x_8, x_9, x_5, x_6, x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_handleNode_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_handleNode_spec__2(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_handleNode___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_handleNode___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_handleNode___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_handleNode___lam__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_handleFinished_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_20; lean_object* x_21; lean_object* x_25; lean_object* x_26; lean_object* x_29; lean_object* x_30; lean_object* x_32; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_box(0);
x_8 = lean_array_uset(x_4, x_3, x_7);
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
x_32 = lean_ctor_get(x_1, 1);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_6, 1);
lean_inc(x_33);
x_29 = x_32;
x_30 = x_33;
goto block_31;
}
else
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_6, 1);
lean_inc(x_34);
if (lean_obj_tag(x_34) == 0)
{
x_29 = x_32;
x_30 = x_34;
goto block_31;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_35 = lean_ctor_get(x_32, 0);
lean_inc(x_35);
lean_dec(x_32);
x_36 = lean_ctor_get(x_34, 0);
lean_inc(x_36);
lean_dec(x_34);
x_42 = lean_ctor_get(x_35, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_36, 0);
lean_inc(x_43);
x_44 = lean_nat_dec_le(x_42, x_43);
if (x_44 == 0)
{
lean_dec(x_43);
x_37 = x_42;
goto block_41;
}
else
{
lean_dec(x_42);
x_37 = x_43;
goto block_41;
}
block_41:
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = lean_nat_dec_le(x_38, x_39);
if (x_40 == 0)
{
lean_dec(x_38);
x_25 = x_37;
x_26 = x_39;
goto block_28;
}
else
{
lean_dec(x_39);
x_25 = x_37;
x_26 = x_38;
goto block_28;
}
}
}
}
block_19:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_6, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_6, 3);
lean_inc(x_12);
lean_dec(x_6);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_10);
lean_ctor_set(x_13, 2, x_11);
lean_ctor_set(x_13, 3, x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_usize_of_nat(x_14);
x_16 = lean_usize_add(x_3, x_15);
x_17 = lean_array_uset(x_8, x_3, x_13);
x_3 = x_16;
x_4 = x_17;
goto _start;
}
block_24:
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_10 = x_23;
goto block_19;
}
block_28:
{
uint8_t x_27; 
x_27 = lean_nat_dec_le(x_25, x_26);
if (x_27 == 0)
{
lean_dec(x_26);
lean_inc(x_25);
x_20 = x_25;
x_21 = x_25;
goto block_24;
}
else
{
x_20 = x_25;
x_21 = x_26;
goto block_24;
}
}
block_31:
{
if (lean_obj_tag(x_30) == 0)
{
x_10 = x_29;
goto block_19;
}
else
{
lean_dec(x_29);
x_10 = x_30;
goto block_19;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_handleFinished_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_eq(x_4, x_5);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; 
x_10 = lean_array_uget(x_3, x_4);
lean_inc(x_2);
lean_inc(x_1);
x_11 = l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_handleFinished(x_1, x_2, x_10, x_7, x_8);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = l_Array_append(lean_box(0), x_6, x_14);
lean_dec(x_14);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_usize_of_nat(x_17);
x_19 = lean_usize_add(x_4, x_18);
x_4 = x_19;
x_6 = x_16;
x_7 = x_15;
x_8 = x_13;
goto _start;
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_2);
lean_dec(x_1);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_6);
lean_ctor_set(x_21, 1, x_7);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_8);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_handleFinished(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_3, 3);
lean_inc(x_6);
x_7 = lean_io_get_task_state(x_6, x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 2)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_task_get_own(x_6);
lean_inc(x_10);
lean_inc(x_2);
lean_inc(x_1);
x_11 = l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_handleNode(x_1, x_2, x_10, x_4, x_9);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; lean_object* x_20; size_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_15 = lean_ctor_get(x_11, 1);
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_ctor_get(x_13, 0);
lean_dec(x_17);
x_18 = lean_ctor_get(x_10, 1);
lean_inc(x_18);
lean_dec(x_10);
x_19 = lean_array_size(x_18);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_usize_of_nat(x_20);
x_22 = l_Array_mapMUnsafe_map___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_handleFinished_spec__0(x_3, x_19, x_21, x_18);
x_23 = l_Array_empty(lean_box(0));
x_24 = lean_array_get_size(x_22);
x_25 = lean_nat_dec_lt(x_20, x_24);
if (x_25 == 0)
{
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_2);
lean_dec(x_1);
lean_ctor_set(x_13, 0, x_23);
return x_11;
}
else
{
uint8_t x_26; 
x_26 = lean_nat_dec_le(x_24, x_24);
if (x_26 == 0)
{
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_2);
lean_dec(x_1);
lean_ctor_set(x_13, 0, x_23);
return x_11;
}
else
{
size_t x_27; lean_object* x_28; 
lean_free_object(x_13);
lean_free_object(x_11);
x_27 = lean_usize_of_nat(x_24);
lean_dec(x_24);
x_28 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_handleFinished_spec__1(x_1, x_2, x_22, x_21, x_27, x_23, x_16, x_15);
lean_dec(x_22);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; size_t x_32; lean_object* x_33; size_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_29 = lean_ctor_get(x_11, 1);
x_30 = lean_ctor_get(x_13, 1);
lean_inc(x_30);
lean_dec(x_13);
x_31 = lean_ctor_get(x_10, 1);
lean_inc(x_31);
lean_dec(x_10);
x_32 = lean_array_size(x_31);
x_33 = lean_unsigned_to_nat(0u);
x_34 = lean_usize_of_nat(x_33);
x_35 = l_Array_mapMUnsafe_map___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_handleFinished_spec__0(x_3, x_32, x_34, x_31);
x_36 = l_Array_empty(lean_box(0));
x_37 = lean_array_get_size(x_35);
x_38 = lean_nat_dec_lt(x_33, x_37);
if (x_38 == 0)
{
lean_object* x_39; 
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_2);
lean_dec(x_1);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_30);
lean_ctor_set(x_11, 0, x_39);
return x_11;
}
else
{
uint8_t x_40; 
x_40 = lean_nat_dec_le(x_37, x_37);
if (x_40 == 0)
{
lean_object* x_41; 
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_2);
lean_dec(x_1);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_36);
lean_ctor_set(x_41, 1, x_30);
lean_ctor_set(x_11, 0, x_41);
return x_11;
}
else
{
size_t x_42; lean_object* x_43; 
lean_free_object(x_11);
x_42 = lean_usize_of_nat(x_37);
lean_dec(x_37);
x_43 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_handleFinished_spec__1(x_1, x_2, x_35, x_34, x_42, x_36, x_30, x_29);
lean_dec(x_35);
return x_43;
}
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; size_t x_49; lean_object* x_50; size_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_44 = lean_ctor_get(x_11, 0);
x_45 = lean_ctor_get(x_11, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_11);
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
x_48 = lean_ctor_get(x_10, 1);
lean_inc(x_48);
lean_dec(x_10);
x_49 = lean_array_size(x_48);
x_50 = lean_unsigned_to_nat(0u);
x_51 = lean_usize_of_nat(x_50);
x_52 = l_Array_mapMUnsafe_map___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_handleFinished_spec__0(x_3, x_49, x_51, x_48);
x_53 = l_Array_empty(lean_box(0));
x_54 = lean_array_get_size(x_52);
x_55 = lean_nat_dec_lt(x_50, x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_54);
lean_dec(x_52);
lean_dec(x_2);
lean_dec(x_1);
if (lean_is_scalar(x_47)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_47;
}
lean_ctor_set(x_56, 0, x_53);
lean_ctor_set(x_56, 1, x_46);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_45);
return x_57;
}
else
{
uint8_t x_58; 
x_58 = lean_nat_dec_le(x_54, x_54);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_54);
lean_dec(x_52);
lean_dec(x_2);
lean_dec(x_1);
if (lean_is_scalar(x_47)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_47;
}
lean_ctor_set(x_59, 0, x_53);
lean_ctor_set(x_59, 1, x_46);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_45);
return x_60;
}
else
{
size_t x_61; lean_object* x_62; 
lean_dec(x_47);
x_61 = lean_usize_of_nat(x_54);
lean_dec(x_54);
x_62 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_handleFinished_spec__1(x_1, x_2, x_52, x_51, x_61, x_53, x_46, x_45);
lean_dec(x_52);
return x_62;
}
}
}
}
else
{
uint8_t x_63; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_63 = !lean_is_exclusive(x_7);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_64 = lean_ctor_get(x_7, 0);
lean_dec(x_64);
x_65 = lean_unsigned_to_nat(1u);
x_66 = lean_mk_empty_array_with_capacity(x_65);
x_67 = lean_array_push(x_66, x_3);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_4);
lean_ctor_set(x_7, 0, x_68);
return x_7;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_69 = lean_ctor_get(x_7, 1);
lean_inc(x_69);
lean_dec(x_7);
x_70 = lean_unsigned_to_nat(1u);
x_71 = lean_mk_empty_array_with_capacity(x_70);
x_72 = lean_array_push(x_71, x_3);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_4);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_69);
return x_74;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_handleFinished_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_handleFinished_spec__0(x_1, x_5, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_handleFinished_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_11 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_handleFinished_spec__1(x_1, x_2, x_3, x_9, x_10, x_6, x_7, x_8);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_handleTasks_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_8 = lean_ctor_get(x_5, 3);
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
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_handleTasks_spec__1(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_3, x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_array_uget(x_2, x_3);
x_9 = lean_ctor_get(x_8, 3);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_io_get_task_state(x_9, x_6);
lean_dec(x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_13 = x_10;
} else {
 lean_dec_ref(x_10);
 x_13 = lean_box(0);
}
x_14 = lean_box(1);
if (lean_obj_tag(x_11) == 2)
{
x_15 = x_5;
goto block_18;
}
else
{
lean_dec(x_11);
if (x_1 == 0)
{
lean_object* x_19; size_t x_20; size_t x_21; 
lean_dec(x_13);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_usize_of_nat(x_19);
x_21 = lean_usize_add(x_3, x_20);
x_3 = x_21;
x_6 = x_12;
goto _start;
}
else
{
x_15 = x_5;
goto block_18;
}
}
block_18:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
if (lean_is_scalar(x_13)) {
 x_17 = lean_alloc_ctor(0, 2, 0);
} else {
 x_17 = x_13;
}
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_12);
return x_17;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_5);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_6);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_handleTasks(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_36; uint8_t x_37; 
x_36 = l_IO_CancelToken_isSet(x_3, x_6);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_63; 
x_38 = lean_ctor_get(x_36, 0);
x_39 = lean_ctor_get(x_36, 1);
x_63 = lean_unbox(x_38);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
lean_free_object(x_36);
x_64 = l_Array_empty(lean_box(0));
x_65 = lean_unsigned_to_nat(0u);
x_66 = lean_array_get_size(x_4);
x_67 = lean_nat_dec_lt(x_65, x_66);
if (x_67 == 0)
{
lean_dec(x_66);
lean_dec(x_4);
x_40 = x_64;
x_41 = x_5;
x_42 = x_39;
goto block_62;
}
else
{
uint8_t x_68; 
x_68 = lean_nat_dec_le(x_66, x_66);
if (x_68 == 0)
{
lean_dec(x_66);
lean_dec(x_4);
x_40 = x_64;
x_41 = x_5;
x_42 = x_39;
goto block_62;
}
else
{
size_t x_69; size_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_69 = lean_usize_of_nat(x_65);
x_70 = lean_usize_of_nat(x_66);
lean_dec(x_66);
lean_inc(x_2);
lean_inc(x_1);
x_71 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_handleFinished_spec__1(x_1, x_2, x_4, x_69, x_70, x_64, x_5, x_39);
lean_dec(x_4);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = lean_ctor_get(x_72, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_72, 1);
lean_inc(x_75);
lean_dec(x_72);
x_40 = x_74;
x_41 = x_75;
x_42 = x_73;
goto block_62;
}
}
}
else
{
lean_object* x_76; lean_object* x_77; 
lean_dec(x_38);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_76 = lean_box(0);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_5);
lean_ctor_set(x_36, 0, x_77);
return x_36;
}
block_62:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
lean_inc(x_2);
lean_inc(x_1);
x_43 = l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_sendFileProgress(x_1, x_2, x_40, x_41, x_42);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_unsigned_to_nat(0u);
x_48 = lean_array_get_size(x_40);
x_49 = lean_nat_dec_lt(x_47, x_48);
if (x_49 == 0)
{
lean_dec(x_38);
x_19 = x_47;
x_20 = x_48;
x_21 = x_40;
x_22 = x_46;
x_23 = x_45;
goto block_35;
}
else
{
if (x_49 == 0)
{
lean_dec(x_38);
x_19 = x_47;
x_20 = x_48;
x_21 = x_40;
x_22 = x_46;
x_23 = x_45;
goto block_35;
}
else
{
size_t x_50; size_t x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_50 = lean_usize_of_nat(x_47);
x_51 = lean_usize_of_nat(x_48);
x_52 = lean_unbox(x_38);
lean_dec(x_38);
x_53 = l_Array_anyMUnsafe_any___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_handleTasks_spec__1(x_52, x_40, x_50, x_51, x_46, x_45);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_unbox(x_55);
lean_dec(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_53, 1);
lean_inc(x_57);
lean_dec(x_53);
x_58 = lean_ctor_get(x_54, 1);
lean_inc(x_58);
lean_dec(x_54);
x_19 = x_47;
x_20 = x_48;
x_21 = x_40;
x_22 = x_58;
x_23 = x_57;
goto block_35;
}
else
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_48);
x_59 = lean_ctor_get(x_53, 1);
lean_inc(x_59);
lean_dec(x_53);
x_60 = lean_ctor_get(x_54, 1);
lean_inc(x_60);
lean_dec(x_54);
x_4 = x_40;
x_5 = x_60;
x_6 = x_59;
goto _start;
}
}
}
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_103; 
x_78 = lean_ctor_get(x_36, 0);
x_79 = lean_ctor_get(x_36, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_36);
x_103 = lean_unbox(x_78);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; 
x_104 = l_Array_empty(lean_box(0));
x_105 = lean_unsigned_to_nat(0u);
x_106 = lean_array_get_size(x_4);
x_107 = lean_nat_dec_lt(x_105, x_106);
if (x_107 == 0)
{
lean_dec(x_106);
lean_dec(x_4);
x_80 = x_104;
x_81 = x_5;
x_82 = x_79;
goto block_102;
}
else
{
uint8_t x_108; 
x_108 = lean_nat_dec_le(x_106, x_106);
if (x_108 == 0)
{
lean_dec(x_106);
lean_dec(x_4);
x_80 = x_104;
x_81 = x_5;
x_82 = x_79;
goto block_102;
}
else
{
size_t x_109; size_t x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_109 = lean_usize_of_nat(x_105);
x_110 = lean_usize_of_nat(x_106);
lean_dec(x_106);
lean_inc(x_2);
lean_inc(x_1);
x_111 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_handleFinished_spec__1(x_1, x_2, x_4, x_109, x_110, x_104, x_5, x_79);
lean_dec(x_4);
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec(x_111);
x_114 = lean_ctor_get(x_112, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_112, 1);
lean_inc(x_115);
lean_dec(x_112);
x_80 = x_114;
x_81 = x_115;
x_82 = x_113;
goto block_102;
}
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_dec(x_78);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_116 = lean_box(0);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_5);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_79);
return x_118;
}
block_102:
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
lean_inc(x_2);
lean_inc(x_1);
x_83 = l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_sendFileProgress(x_1, x_2, x_80, x_81, x_82);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = lean_unsigned_to_nat(0u);
x_88 = lean_array_get_size(x_80);
x_89 = lean_nat_dec_lt(x_87, x_88);
if (x_89 == 0)
{
lean_dec(x_78);
x_19 = x_87;
x_20 = x_88;
x_21 = x_80;
x_22 = x_86;
x_23 = x_85;
goto block_35;
}
else
{
if (x_89 == 0)
{
lean_dec(x_78);
x_19 = x_87;
x_20 = x_88;
x_21 = x_80;
x_22 = x_86;
x_23 = x_85;
goto block_35;
}
else
{
size_t x_90; size_t x_91; uint8_t x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_90 = lean_usize_of_nat(x_87);
x_91 = lean_usize_of_nat(x_88);
x_92 = lean_unbox(x_78);
lean_dec(x_78);
x_93 = l_Array_anyMUnsafe_any___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_handleTasks_spec__1(x_92, x_80, x_90, x_91, x_86, x_85);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_unbox(x_95);
lean_dec(x_95);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_93, 1);
lean_inc(x_97);
lean_dec(x_93);
x_98 = lean_ctor_get(x_94, 1);
lean_inc(x_98);
lean_dec(x_94);
x_19 = x_87;
x_20 = x_88;
x_21 = x_80;
x_22 = x_98;
x_23 = x_97;
goto block_35;
}
else
{
lean_object* x_99; lean_object* x_100; 
lean_dec(x_88);
x_99 = lean_ctor_get(x_93, 1);
lean_inc(x_99);
lean_dec(x_93);
x_100 = lean_ctor_get(x_94, 1);
lean_inc(x_100);
lean_dec(x_94);
x_4 = x_80;
x_5 = x_100;
x_6 = x_99;
goto _start;
}
}
}
}
}
block_18:
{
size_t x_10; lean_object* x_11; size_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_array_size(x_7);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_usize_of_nat(x_11);
lean_inc(x_7);
x_13 = l_Array_mapMUnsafe_map___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_handleTasks_spec__0(x_10, x_12, x_7);
x_14 = lean_array_to_list(x_13);
x_15 = lean_io_wait_any(x_14, x_9);
lean_dec(x_14);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_4 = x_7;
x_5 = x_8;
x_6 = x_16;
goto _start;
}
block_35:
{
uint8_t x_24; 
x_24 = lean_nat_dec_lt(x_19, x_20);
lean_dec(x_20);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_21);
lean_dec(x_2);
lean_dec(x_1);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_22);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_23);
return x_27;
}
else
{
uint8_t x_28; 
x_28 = lean_ctor_get_uint8(x_22, sizeof(void*)*2);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; 
lean_inc(x_2);
lean_inc(x_1);
x_29 = l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_publishDiagnostics(x_1, x_2, x_23);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_ctor_get(x_22, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_22, 1);
lean_inc(x_32);
x_33 = lean_ctor_get_uint8(x_22, sizeof(void*)*2 + 1);
lean_dec(x_22);
x_34 = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_32);
lean_ctor_set_uint8(x_34, sizeof(void*)*2, x_24);
lean_ctor_set_uint8(x_34, sizeof(void*)*2 + 1, x_33);
x_7 = x_21;
x_8 = x_34;
x_9 = x_30;
goto block_18;
}
else
{
x_7 = x_21;
x_8 = x_22;
x_9 = x_23;
goto block_18;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_handleTasks_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_handleTasks_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_handleTasks_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; size_t x_8; size_t x_9; lean_object* x_10; 
x_7 = lean_unbox(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l_Array_anyMUnsafe_any___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_handleTasks_spec__1(x_7, x_2, x_8, x_9, x_5, x_6);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_handleTasks___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_handleTasks(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots___lam__0(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots___lam__1(lean_object* x_1, lean_object* x_2, uint32_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_20; lean_object* x_21; lean_object* x_36; lean_object* x_37; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_118; 
x_60 = l_IO_sleep(x_3, x_6);
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_62 = x_60;
} else {
 lean_dec_ref(x_60);
 x_62 = lean_box(0);
}
x_63 = lean_box(0);
x_64 = lean_ctor_get(x_1, 1);
lean_inc(x_64);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_118 = lean_ctor_get(x_64, 3);
lean_inc(x_118);
lean_dec(x_64);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; 
lean_dec(x_5);
x_119 = lean_box(0);
x_66 = x_119;
goto block_117;
}
else
{
uint8_t x_120; 
x_120 = !lean_is_exclusive(x_118);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; lean_object* x_127; 
x_121 = lean_ctor_get(x_118, 0);
x_122 = lean_ctor_get(x_121, 1);
lean_inc(x_122);
lean_dec(x_121);
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
x_125 = lean_box(1);
x_126 = lean_unbox(x_125);
x_127 = l_Lean_Language_SnapshotTask_map___redArg(x_122, x_5, x_123, x_124, x_126);
lean_ctor_set(x_118, 0, x_127);
x_66 = x_118;
goto block_117;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; lean_object* x_134; lean_object* x_135; 
x_128 = lean_ctor_get(x_118, 0);
lean_inc(x_128);
lean_dec(x_118);
x_129 = lean_ctor_get(x_128, 1);
lean_inc(x_129);
lean_dec(x_128);
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
x_132 = lean_box(1);
x_133 = lean_unbox(x_132);
x_134 = l_Lean_Language_SnapshotTask_map___redArg(x_129, x_5, x_130, x_131, x_133);
x_135 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_135, 0, x_134);
x_66 = x_135;
goto block_117;
}
}
block_19:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Std_Channel_Sync_send___redArg(x_7, x_11, x_9);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
x_15 = lean_box(0);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
block_35:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_22 = lean_ctor_get(x_1, 0);
lean_inc(x_22);
lean_dec(x_1);
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
lean_dec(x_20);
x_24 = l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_mkIleanInfoFinalNotification(x_22, x_23, x_21);
lean_dec(x_23);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_ctor_get(x_2, 0);
lean_inc(x_27);
lean_dec(x_2);
x_28 = lean_ctor_get(x_25, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
lean_dec(x_25);
x_30 = l_Lean_Json_toStructured_x3f___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_handleNode_spec__0(x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; 
lean_dec(x_30);
x_31 = lean_box(0);
x_7 = x_27;
x_8 = x_28;
x_9 = x_26;
x_10 = x_31;
goto block_19;
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_30);
if (x_32 == 0)
{
x_7 = x_27;
x_8 = x_28;
x_9 = x_26;
x_10 = x_30;
goto block_19;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_30, 0);
lean_inc(x_33);
lean_dec(x_30);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_7 = x_27;
x_8 = x_28;
x_9 = x_26;
x_10 = x_34;
goto block_19;
}
}
}
block_41:
{
uint8_t x_38; 
x_38 = lean_ctor_get_uint8(x_36, sizeof(void*)*2);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
lean_inc(x_1);
lean_inc(x_2);
x_39 = l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_publishDiagnostics(x_2, x_1, x_37);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
x_20 = x_36;
x_21 = x_40;
goto block_35;
}
else
{
x_20 = x_36;
x_21 = x_37;
goto block_35;
}
}
block_50:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_42);
lean_ctor_set(x_47, 1, x_46);
x_48 = l_Std_Channel_send___redArg(x_44, x_47, x_45);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec(x_48);
x_36 = x_43;
x_37 = x_49;
goto block_41;
}
block_59:
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_53);
lean_ctor_set(x_56, 1, x_55);
x_57 = l_Std_Channel_send___redArg(x_52, x_56, x_54);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec(x_57);
x_36 = x_51;
x_37 = x_58;
goto block_41;
}
block_117:
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; uint8_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_67 = lean_unsigned_to_nat(0u);
x_68 = lean_mk_empty_array_with_capacity(x_67);
lean_inc(x_68);
x_69 = l___private_Lean_Language_Lean_Types_0__Lean_Language_Lean_pushOpt___redArg(x_66, x_68);
if (lean_is_scalar(x_62)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_62;
}
lean_ctor_set(x_70, 0, x_65);
lean_ctor_set(x_70, 1, x_69);
x_71 = l_Lean_Language_SnapshotTask_finished(lean_box(0), x_63, x_70);
x_72 = lean_unsigned_to_nat(1u);
x_73 = lean_mk_empty_array_with_capacity(x_72);
x_74 = lean_array_push(x_73, x_71);
x_75 = lean_box(0);
lean_inc(x_68);
x_76 = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(x_76, 0, x_68);
lean_ctor_set(x_76, 1, x_68);
x_77 = lean_unbox(x_75);
lean_ctor_set_uint8(x_76, sizeof(void*)*2, x_77);
x_78 = lean_unbox(x_75);
lean_ctor_set_uint8(x_76, sizeof(void*)*2 + 1, x_78);
lean_inc(x_1);
lean_inc(x_2);
x_79 = l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_handleTasks(x_2, x_1, x_4, x_74, x_76, x_61);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_83 = l_IO_CancelToken_isSet(x_4, x_81);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_unbox(x_84);
lean_dec(x_84);
if (x_85 == 0)
{
uint8_t x_86; 
x_86 = lean_ctor_get_uint8(x_82, sizeof(void*)*2 + 1);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_87 = lean_ctor_get(x_83, 1);
lean_inc(x_87);
lean_dec(x_83);
x_88 = lean_ctor_get(x_2, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_1, 0);
lean_inc(x_89);
x_90 = l_Lean_Server_mkFileProgressDoneNotification(x_89);
lean_dec(x_89);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
x_93 = l_Lean_Json_toStructured_x3f___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_sendFileProgress_spec__4(x_92);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; 
lean_dec(x_93);
x_94 = lean_box(0);
x_42 = x_91;
x_43 = x_82;
x_44 = x_88;
x_45 = x_87;
x_46 = x_94;
goto block_50;
}
else
{
uint8_t x_95; 
x_95 = !lean_is_exclusive(x_93);
if (x_95 == 0)
{
x_42 = x_91;
x_43 = x_82;
x_44 = x_88;
x_45 = x_87;
x_46 = x_93;
goto block_50;
}
else
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_93, 0);
lean_inc(x_96);
lean_dec(x_93);
x_97 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_97, 0, x_96);
x_42 = x_91;
x_43 = x_82;
x_44 = x_88;
x_45 = x_87;
x_46 = x_97;
goto block_50;
}
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_98 = lean_ctor_get(x_83, 1);
lean_inc(x_98);
lean_dec(x_83);
x_99 = lean_ctor_get(x_2, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_1, 0);
lean_inc(x_100);
x_101 = lean_box(1);
x_102 = lean_unbox(x_101);
x_103 = l_Lean_Server_mkFileProgressAtPosNotification(x_100, x_67, x_102);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
x_106 = l_Lean_Json_toStructured_x3f___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots_sendFileProgress_spec__4(x_105);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; 
lean_dec(x_106);
x_107 = lean_box(0);
x_51 = x_82;
x_52 = x_99;
x_53 = x_104;
x_54 = x_98;
x_55 = x_107;
goto block_59;
}
else
{
uint8_t x_108; 
x_108 = !lean_is_exclusive(x_106);
if (x_108 == 0)
{
x_51 = x_82;
x_52 = x_99;
x_53 = x_104;
x_54 = x_98;
x_55 = x_106;
goto block_59;
}
else
{
lean_object* x_109; lean_object* x_110; 
x_109 = lean_ctor_get(x_106, 0);
lean_inc(x_109);
lean_dec(x_106);
x_110 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_110, 0, x_109);
x_51 = x_82;
x_52 = x_99;
x_53 = x_104;
x_54 = x_98;
x_55 = x_110;
goto block_59;
}
}
}
}
else
{
uint8_t x_111; 
lean_dec(x_82);
lean_dec(x_2);
lean_dec(x_1);
x_111 = !lean_is_exclusive(x_83);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; 
x_112 = lean_ctor_get(x_83, 0);
lean_dec(x_112);
x_113 = lean_box(0);
lean_ctor_set(x_83, 0, x_113);
return x_83;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_83, 1);
lean_inc(x_114);
lean_dec(x_83);
x_115 = lean_box(0);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_114);
return x_116;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint32_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_alloc_closure((void*)(l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots___lam__0), 1, 0);
x_6 = lean_ctor_get(x_1, 9);
lean_inc(x_6);
x_7 = l_Lean_Server_FileWorker_server_reportDelayMs;
x_8 = l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(x_6, x_7);
lean_dec(x_6);
x_9 = lean_uint32_of_nat(x_8);
lean_dec(x_8);
x_10 = lean_box_uint32(x_9);
x_11 = lean_alloc_closure((void*)(l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots___lam__1___boxed), 6, 5);
lean_closure_set(x_11, 0, x_2);
lean_closure_set(x_11, 1, x_1);
lean_closure_set(x_11, 2, x_10);
lean_closure_set(x_11, 3, x_3);
lean_closure_set(x_11, 4, x_5);
x_12 = l_Lean_Server_ServerTask_BaseIO_asTask___redArg(x_11, x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint32_t x_7; lean_object* x_8; 
x_7 = lean_unbox_uint32(x_3);
lean_dec(x_3);
x_8 = l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots___lam__1(x_1, x_2, x_7, x_4, x_5, x_6);
lean_dec(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker___hyg_2716_(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_setupImports___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_38; lean_object* x_39; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_5);
lean_inc(x_6);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_ctor_get(x_1, 3);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_string_utf8_byte_size(x_11);
lean_dec(x_11);
x_13 = l_Lean_FileMap_utf8PosToLspPos(x_10, x_12);
lean_dec(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_6);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_box(2);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_box(0);
x_19 = lean_box(0);
x_20 = lean_box(0);
x_21 = lean_box(0);
x_22 = lean_box(0);
x_23 = lean_box(0);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_25, 0, x_9);
lean_ctor_set(x_25, 1, x_15);
lean_ctor_set(x_25, 2, x_17);
lean_ctor_set(x_25, 3, x_18);
lean_ctor_set(x_25, 4, x_19);
lean_ctor_set(x_25, 5, x_20);
lean_ctor_set(x_25, 6, x_3);
lean_ctor_set(x_25, 7, x_21);
lean_ctor_set(x_25, 8, x_22);
lean_ctor_set(x_25, 9, x_23);
lean_ctor_set(x_25, 10, x_24);
x_26 = lean_mk_empty_array_with_capacity(x_7);
x_27 = lean_array_push(x_26, x_25);
x_28 = l_Lean_Server_mkPublishDiagnosticsNotification(x_1, x_27);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_38 = lean_ctor_get(x_28, 1);
lean_inc(x_38);
lean_dec(x_28);
x_39 = l_Lean_Json_toStructured_x3f___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_publishDiagnostics_spec__1(x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; 
lean_dec(x_39);
x_40 = lean_box(0);
x_30 = x_40;
goto block_37;
}
else
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_39);
if (x_41 == 0)
{
x_30 = x_39;
goto block_37;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_39, 0);
lean_inc(x_42);
lean_dec(x_39);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_30 = x_43;
goto block_37;
}
}
block_37:
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Std_Channel_Sync_send___redArg(x_2, x_31, x_4);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
return x_32;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_32);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_setupImports___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_inc(x_3);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_setupImports___lam__2(uint8_t x_1, lean_object* x_2) {
_start:
{
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_setupImports___lam__4(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_setupImports(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_importsLoadedRef;
x_8 = lean_st_ref_take(x_7, x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_11 = x_8;
} else {
 lean_dec_ref(x_8);
 x_11 = lean_box(0);
}
x_12 = lean_box(1);
x_13 = lean_st_ref_set(x_7, x_12, x_10);
x_14 = lean_unbox(x_9);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_16 = x_13;
} else {
 lean_dec_ref(x_13);
 x_16 = lean_box(0);
}
lean_inc(x_3);
lean_inc(x_1);
x_17 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_setupImports___lam__0), 4, 2);
lean_closure_set(x_17, 0, x_1);
lean_closure_set(x_17, 1, x_3);
x_18 = l_Lean_Elab_HeaderSyntax_imports(x_4);
lean_inc(x_18);
lean_inc(x_1);
x_19 = l_Lean_Server_FileWorker_setupFile(x_1, x_18, x_17, x_15);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_213; lean_object* x_214; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_setupImports___lam__1___boxed), 3, 0);
lean_inc(x_9);
x_23 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_setupImports___lam__2___boxed), 2, 1);
lean_closure_set(x_23, 0, x_9);
x_24 = lean_unsigned_to_nat(0u);
x_25 = lean_mk_empty_array_with_capacity(x_24);
lean_inc(x_1);
x_26 = l_Lean_Server_mkPublishDiagnosticsNotification(x_1, x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_213 = lean_ctor_get(x_26, 1);
lean_inc(x_213);
lean_dec(x_26);
x_214 = l_Lean_Json_toStructured_x3f___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_publishDiagnostics_spec__1(x_213);
if (lean_obj_tag(x_214) == 0)
{
lean_object* x_215; 
lean_dec(x_214);
x_215 = lean_box(0);
x_28 = x_215;
goto block_212;
}
else
{
uint8_t x_216; 
x_216 = !lean_is_exclusive(x_214);
if (x_216 == 0)
{
x_28 = x_214;
goto block_212;
}
else
{
lean_object* x_217; lean_object* x_218; 
x_217 = lean_ctor_get(x_214, 0);
lean_inc(x_217);
lean_dec(x_214);
x_218 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_218, 0, x_217);
x_28 = x_218;
goto block_212;
}
}
block_212:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
if (lean_is_scalar(x_16)) {
 x_29 = lean_alloc_ctor(1, 2, 0);
} else {
 x_29 = x_16;
 lean_ctor_set_tag(x_29, 1);
}
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Std_Channel_Sync_send___redArg(x_3, x_29, x_21);
x_31 = lean_ctor_get(x_20, 0);
lean_inc(x_31);
switch (lean_obj_tag(x_31)) {
case 2:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_mk_string_unchecked("Imports are out of date and must be rebuilt; use the \"Restart File\" command in your editor.", 91, 91);
x_34 = l_Lean_Language_diagnosticsOfHeaderError(x_33, x_5, x_32);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; uint64_t x_45; lean_object* x_46; lean_object* x_47; size_t x_48; lean_object* x_49; lean_object* x_50; size_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; 
x_36 = lean_ctor_get(x_34, 0);
x_37 = lean_mk_string_unchecked("Lean", 4, 4);
x_38 = lean_mk_string_unchecked("Server", 6, 6);
x_39 = lean_mk_string_unchecked("FileWorker", 10, 10);
x_40 = lean_mk_string_unchecked("setupImports", 12, 12);
x_41 = l_Lean_Name_mkStr4(x_37, x_38, x_39, x_40);
x_42 = lean_unbox(x_12);
x_43 = l_Lean_Name_toString(x_41, x_42, x_23);
x_44 = lean_box(0);
x_45 = lean_uint64_of_nat(x_24);
x_46 = lean_unsigned_to_nat(2u);
x_47 = lean_unsigned_to_nat(5u);
x_48 = lean_usize_of_nat(x_47);
x_49 = lean_usize_to_nat(x_48);
x_50 = lean_nat_pow(x_46, x_49);
lean_dec(x_49);
x_51 = lean_usize_of_nat(x_50);
lean_dec(x_50);
x_52 = lean_usize_to_nat(x_51);
x_53 = lean_mk_empty_array_with_capacity(x_52);
lean_dec(x_52);
lean_inc(x_53);
x_54 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_55 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
lean_ctor_set(x_55, 2, x_24);
lean_ctor_set(x_55, 3, x_24);
lean_ctor_set_usize(x_55, 4, x_48);
x_56 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set_uint64(x_56, sizeof(void*)*1, x_45);
x_57 = lean_box(0);
x_58 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_58, 0, x_43);
lean_ctor_set(x_58, 1, x_36);
lean_ctor_set(x_58, 2, x_44);
lean_ctor_set(x_58, 3, x_56);
x_59 = lean_unbox(x_12);
lean_ctor_set_uint8(x_58, sizeof(void*)*4, x_59);
if (lean_is_scalar(x_11)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_11;
}
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_57);
x_61 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_34, 0, x_61);
return x_34;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; uint64_t x_72; lean_object* x_73; lean_object* x_74; size_t x_75; lean_object* x_76; lean_object* x_77; size_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_62 = lean_ctor_get(x_34, 0);
x_63 = lean_ctor_get(x_34, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_34);
x_64 = lean_mk_string_unchecked("Lean", 4, 4);
x_65 = lean_mk_string_unchecked("Server", 6, 6);
x_66 = lean_mk_string_unchecked("FileWorker", 10, 10);
x_67 = lean_mk_string_unchecked("setupImports", 12, 12);
x_68 = l_Lean_Name_mkStr4(x_64, x_65, x_66, x_67);
x_69 = lean_unbox(x_12);
x_70 = l_Lean_Name_toString(x_68, x_69, x_23);
x_71 = lean_box(0);
x_72 = lean_uint64_of_nat(x_24);
x_73 = lean_unsigned_to_nat(2u);
x_74 = lean_unsigned_to_nat(5u);
x_75 = lean_usize_of_nat(x_74);
x_76 = lean_usize_to_nat(x_75);
x_77 = lean_nat_pow(x_73, x_76);
lean_dec(x_76);
x_78 = lean_usize_of_nat(x_77);
lean_dec(x_77);
x_79 = lean_usize_to_nat(x_78);
x_80 = lean_mk_empty_array_with_capacity(x_79);
lean_dec(x_79);
lean_inc(x_80);
x_81 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_81, 0, x_80);
x_82 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_80);
lean_ctor_set(x_82, 2, x_24);
lean_ctor_set(x_82, 3, x_24);
lean_ctor_set_usize(x_82, 4, x_75);
x_83 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set_uint64(x_83, sizeof(void*)*1, x_72);
x_84 = lean_box(0);
x_85 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_85, 0, x_70);
lean_ctor_set(x_85, 1, x_62);
lean_ctor_set(x_85, 2, x_71);
lean_ctor_set(x_85, 3, x_83);
x_86 = lean_unbox(x_12);
lean_ctor_set_uint8(x_85, sizeof(void*)*4, x_86);
if (lean_is_scalar(x_11)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_11;
}
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_84);
x_88 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_88, 0, x_87);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_63);
return x_89;
}
}
case 3:
{
lean_object* x_90; uint8_t x_91; 
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_90 = lean_ctor_get(x_30, 1);
lean_inc(x_90);
lean_dec(x_30);
x_91 = !lean_is_exclusive(x_31);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_92 = lean_ctor_get(x_31, 0);
x_93 = l_Lean_Language_diagnosticsOfHeaderError(x_92, x_5, x_90);
x_94 = !lean_is_exclusive(x_93);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; lean_object* x_102; lean_object* x_103; uint64_t x_104; lean_object* x_105; lean_object* x_106; size_t x_107; lean_object* x_108; lean_object* x_109; size_t x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; lean_object* x_118; lean_object* x_119; 
x_95 = lean_ctor_get(x_93, 0);
x_96 = lean_mk_string_unchecked("Lean", 4, 4);
x_97 = lean_mk_string_unchecked("Server", 6, 6);
x_98 = lean_mk_string_unchecked("FileWorker", 10, 10);
x_99 = lean_mk_string_unchecked("setupImports", 12, 12);
x_100 = l_Lean_Name_mkStr4(x_96, x_97, x_98, x_99);
x_101 = lean_unbox(x_12);
x_102 = l_Lean_Name_toString(x_100, x_101, x_23);
x_103 = lean_box(0);
x_104 = lean_uint64_of_nat(x_24);
x_105 = lean_unsigned_to_nat(2u);
x_106 = lean_unsigned_to_nat(5u);
x_107 = lean_usize_of_nat(x_106);
x_108 = lean_usize_to_nat(x_107);
x_109 = lean_nat_pow(x_105, x_108);
lean_dec(x_108);
x_110 = lean_usize_of_nat(x_109);
lean_dec(x_109);
x_111 = lean_usize_to_nat(x_110);
x_112 = lean_mk_empty_array_with_capacity(x_111);
lean_dec(x_111);
lean_inc(x_112);
lean_ctor_set_tag(x_31, 0);
lean_ctor_set(x_31, 0, x_112);
x_113 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_113, 0, x_31);
lean_ctor_set(x_113, 1, x_112);
lean_ctor_set(x_113, 2, x_24);
lean_ctor_set(x_113, 3, x_24);
lean_ctor_set_usize(x_113, 4, x_107);
x_114 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set_uint64(x_114, sizeof(void*)*1, x_104);
x_115 = lean_box(0);
x_116 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_116, 0, x_102);
lean_ctor_set(x_116, 1, x_95);
lean_ctor_set(x_116, 2, x_103);
lean_ctor_set(x_116, 3, x_114);
x_117 = lean_unbox(x_12);
lean_ctor_set_uint8(x_116, sizeof(void*)*4, x_117);
if (lean_is_scalar(x_11)) {
 x_118 = lean_alloc_ctor(0, 2, 0);
} else {
 x_118 = x_11;
}
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_115);
x_119 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_93, 0, x_119);
return x_93;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; lean_object* x_128; lean_object* x_129; uint64_t x_130; lean_object* x_131; lean_object* x_132; size_t x_133; lean_object* x_134; lean_object* x_135; size_t x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_120 = lean_ctor_get(x_93, 0);
x_121 = lean_ctor_get(x_93, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_93);
x_122 = lean_mk_string_unchecked("Lean", 4, 4);
x_123 = lean_mk_string_unchecked("Server", 6, 6);
x_124 = lean_mk_string_unchecked("FileWorker", 10, 10);
x_125 = lean_mk_string_unchecked("setupImports", 12, 12);
x_126 = l_Lean_Name_mkStr4(x_122, x_123, x_124, x_125);
x_127 = lean_unbox(x_12);
x_128 = l_Lean_Name_toString(x_126, x_127, x_23);
x_129 = lean_box(0);
x_130 = lean_uint64_of_nat(x_24);
x_131 = lean_unsigned_to_nat(2u);
x_132 = lean_unsigned_to_nat(5u);
x_133 = lean_usize_of_nat(x_132);
x_134 = lean_usize_to_nat(x_133);
x_135 = lean_nat_pow(x_131, x_134);
lean_dec(x_134);
x_136 = lean_usize_of_nat(x_135);
lean_dec(x_135);
x_137 = lean_usize_to_nat(x_136);
x_138 = lean_mk_empty_array_with_capacity(x_137);
lean_dec(x_137);
lean_inc(x_138);
lean_ctor_set_tag(x_31, 0);
lean_ctor_set(x_31, 0, x_138);
x_139 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_139, 0, x_31);
lean_ctor_set(x_139, 1, x_138);
lean_ctor_set(x_139, 2, x_24);
lean_ctor_set(x_139, 3, x_24);
lean_ctor_set_usize(x_139, 4, x_133);
x_140 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set_uint64(x_140, sizeof(void*)*1, x_130);
x_141 = lean_box(0);
x_142 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_142, 0, x_128);
lean_ctor_set(x_142, 1, x_120);
lean_ctor_set(x_142, 2, x_129);
lean_ctor_set(x_142, 3, x_140);
x_143 = lean_unbox(x_12);
lean_ctor_set_uint8(x_142, sizeof(void*)*4, x_143);
if (lean_is_scalar(x_11)) {
 x_144 = lean_alloc_ctor(0, 2, 0);
} else {
 x_144 = x_11;
}
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set(x_144, 1, x_141);
x_145 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_145, 0, x_144);
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_121);
return x_146;
}
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; lean_object* x_158; lean_object* x_159; uint64_t x_160; lean_object* x_161; lean_object* x_162; size_t x_163; lean_object* x_164; lean_object* x_165; size_t x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; uint8_t x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_147 = lean_ctor_get(x_31, 0);
lean_inc(x_147);
lean_dec(x_31);
x_148 = l_Lean_Language_diagnosticsOfHeaderError(x_147, x_5, x_90);
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_148, 1);
lean_inc(x_150);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 lean_ctor_release(x_148, 1);
 x_151 = x_148;
} else {
 lean_dec_ref(x_148);
 x_151 = lean_box(0);
}
x_152 = lean_mk_string_unchecked("Lean", 4, 4);
x_153 = lean_mk_string_unchecked("Server", 6, 6);
x_154 = lean_mk_string_unchecked("FileWorker", 10, 10);
x_155 = lean_mk_string_unchecked("setupImports", 12, 12);
x_156 = l_Lean_Name_mkStr4(x_152, x_153, x_154, x_155);
x_157 = lean_unbox(x_12);
x_158 = l_Lean_Name_toString(x_156, x_157, x_23);
x_159 = lean_box(0);
x_160 = lean_uint64_of_nat(x_24);
x_161 = lean_unsigned_to_nat(2u);
x_162 = lean_unsigned_to_nat(5u);
x_163 = lean_usize_of_nat(x_162);
x_164 = lean_usize_to_nat(x_163);
x_165 = lean_nat_pow(x_161, x_164);
lean_dec(x_164);
x_166 = lean_usize_of_nat(x_165);
lean_dec(x_165);
x_167 = lean_usize_to_nat(x_166);
x_168 = lean_mk_empty_array_with_capacity(x_167);
lean_dec(x_167);
lean_inc(x_168);
x_169 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_169, 0, x_168);
x_170 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_168);
lean_ctor_set(x_170, 2, x_24);
lean_ctor_set(x_170, 3, x_24);
lean_ctor_set_usize(x_170, 4, x_163);
x_171 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set_uint64(x_171, sizeof(void*)*1, x_160);
x_172 = lean_box(0);
x_173 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_173, 0, x_158);
lean_ctor_set(x_173, 1, x_149);
lean_ctor_set(x_173, 2, x_159);
lean_ctor_set(x_173, 3, x_171);
x_174 = lean_unbox(x_12);
lean_ctor_set_uint8(x_173, sizeof(void*)*4, x_174);
if (lean_is_scalar(x_11)) {
 x_175 = lean_alloc_ctor(0, 2, 0);
} else {
 x_175 = x_11;
}
lean_ctor_set(x_175, 0, x_173);
lean_ctor_set(x_175, 1, x_172);
x_176 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_176, 0, x_175);
if (lean_is_scalar(x_151)) {
 x_177 = lean_alloc_ctor(0, 2, 0);
} else {
 x_177 = x_151;
}
lean_ctor_set(x_177, 0, x_176);
lean_ctor_set(x_177, 1, x_150);
return x_177;
}
}
default: 
{
uint8_t x_178; 
lean_dec(x_31);
lean_dec(x_23);
lean_dec(x_11);
lean_dec(x_5);
x_178 = !lean_is_exclusive(x_30);
if (x_178 == 0)
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; uint8_t x_183; lean_object* x_184; lean_object* x_185; uint8_t x_186; lean_object* x_187; lean_object* x_188; uint32_t x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; uint8_t x_193; lean_object* x_194; 
x_179 = lean_ctor_get(x_30, 0);
lean_dec(x_179);
x_180 = lean_ctor_get(x_20, 1);
lean_inc(x_180);
x_181 = l_List_forIn_x27_loop___at___Lean_KVMap_mergeBy_spec__0___redArg(x_22, x_180, x_2);
x_182 = l_Lean_Elab_async;
x_183 = lean_unbox(x_12);
x_184 = l_Lean_Option_setIfNotSet___at___Lean_Language_Lean_process_processHeader_spec__1(x_181, x_182, x_183);
x_185 = l_Lean_Elab_inServer;
x_186 = lean_unbox(x_12);
x_187 = l_Lean_Option_set___at___Lean_Environment_realizeConst_spec__2(x_184, x_185, x_186);
x_188 = lean_ctor_get(x_1, 1);
lean_inc(x_188);
lean_dec(x_1);
x_189 = lean_uint32_of_nat(x_24);
x_190 = lean_box(0);
x_191 = lean_ctor_get(x_20, 2);
lean_inc(x_191);
lean_dec(x_20);
x_192 = lean_alloc_ctor(0, 5, 5);
lean_ctor_set(x_192, 0, x_188);
lean_ctor_set(x_192, 1, x_18);
lean_ctor_set(x_192, 2, x_187);
lean_ctor_set(x_192, 3, x_190);
lean_ctor_set(x_192, 4, x_191);
x_193 = lean_unbox(x_9);
lean_dec(x_9);
lean_ctor_set_uint8(x_192, sizeof(void*)*5 + 4, x_193);
lean_ctor_set_uint32(x_192, sizeof(void*)*5, x_189);
x_194 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_194, 0, x_192);
lean_ctor_set(x_30, 0, x_194);
return x_30;
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; uint8_t x_199; lean_object* x_200; lean_object* x_201; uint8_t x_202; lean_object* x_203; lean_object* x_204; uint32_t x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; uint8_t x_209; lean_object* x_210; lean_object* x_211; 
x_195 = lean_ctor_get(x_30, 1);
lean_inc(x_195);
lean_dec(x_30);
x_196 = lean_ctor_get(x_20, 1);
lean_inc(x_196);
x_197 = l_List_forIn_x27_loop___at___Lean_KVMap_mergeBy_spec__0___redArg(x_22, x_196, x_2);
x_198 = l_Lean_Elab_async;
x_199 = lean_unbox(x_12);
x_200 = l_Lean_Option_setIfNotSet___at___Lean_Language_Lean_process_processHeader_spec__1(x_197, x_198, x_199);
x_201 = l_Lean_Elab_inServer;
x_202 = lean_unbox(x_12);
x_203 = l_Lean_Option_set___at___Lean_Environment_realizeConst_spec__2(x_200, x_201, x_202);
x_204 = lean_ctor_get(x_1, 1);
lean_inc(x_204);
lean_dec(x_1);
x_205 = lean_uint32_of_nat(x_24);
x_206 = lean_box(0);
x_207 = lean_ctor_get(x_20, 2);
lean_inc(x_207);
lean_dec(x_20);
x_208 = lean_alloc_ctor(0, 5, 5);
lean_ctor_set(x_208, 0, x_204);
lean_ctor_set(x_208, 1, x_18);
lean_ctor_set(x_208, 2, x_203);
lean_ctor_set(x_208, 3, x_206);
lean_ctor_set(x_208, 4, x_207);
x_209 = lean_unbox(x_9);
lean_dec(x_9);
lean_ctor_set_uint8(x_208, sizeof(void*)*5 + 4, x_209);
lean_ctor_set_uint32(x_208, sizeof(void*)*5, x_205);
x_210 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_210, 0, x_208);
x_211 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_211, 0, x_210);
lean_ctor_set(x_211, 1, x_195);
return x_211;
}
}
}
}
}
else
{
uint8_t x_219; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_219 = !lean_is_exclusive(x_19);
if (x_219 == 0)
{
return x_19;
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_220 = lean_ctor_get(x_19, 0);
x_221 = lean_ctor_get(x_19, 1);
lean_inc(x_221);
lean_inc(x_220);
lean_dec(x_19);
x_222 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_222, 0, x_220);
lean_ctor_set(x_222, 1, x_221);
return x_222;
}
}
}
else
{
lean_object* x_223; lean_object* x_224; uint32_t x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; uint8_t x_264; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_223 = lean_ctor_get(x_13, 1);
lean_inc(x_223);
lean_dec(x_13);
x_224 = lean_unsigned_to_nat(200u);
x_225 = lean_uint32_of_nat(x_224);
x_226 = l_IO_sleep(x_225, x_223);
x_227 = lean_ctor_get(x_226, 1);
lean_inc(x_227);
if (lean_is_exclusive(x_226)) {
 lean_ctor_release(x_226, 0);
 lean_ctor_release(x_226, 1);
 x_228 = x_226;
} else {
 lean_dec_ref(x_226);
 x_228 = lean_box(0);
}
x_229 = lean_io_check_canceled(x_227);
x_230 = lean_ctor_get(x_229, 0);
lean_inc(x_230);
x_231 = lean_ctor_get(x_229, 1);
lean_inc(x_231);
if (lean_is_exclusive(x_229)) {
 lean_ctor_release(x_229, 0);
 lean_ctor_release(x_229, 1);
 x_232 = x_229;
} else {
 lean_dec_ref(x_229);
 x_232 = lean_box(0);
}
x_233 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_setupImports___lam__4___boxed), 1, 0);
x_264 = lean_unbox(x_230);
lean_dec(x_230);
if (x_264 == 0)
{
lean_object* x_265; uint8_t x_266; lean_object* x_267; 
x_265 = lean_unsigned_to_nat(2u);
x_266 = lean_uint8_of_nat(x_265);
x_267 = lean_io_exit(x_266, x_231);
if (lean_obj_tag(x_267) == 0)
{
lean_object* x_268; 
x_268 = lean_ctor_get(x_267, 1);
lean_inc(x_268);
lean_dec(x_267);
x_234 = x_268;
goto block_263;
}
else
{
uint8_t x_269; 
lean_dec(x_233);
lean_dec(x_232);
lean_dec(x_228);
lean_dec(x_9);
x_269 = !lean_is_exclusive(x_267);
if (x_269 == 0)
{
return x_267;
}
else
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; 
x_270 = lean_ctor_get(x_267, 0);
x_271 = lean_ctor_get(x_267, 1);
lean_inc(x_271);
lean_inc(x_270);
lean_dec(x_267);
x_272 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_272, 0, x_270);
lean_ctor_set(x_272, 1, x_271);
return x_272;
}
}
}
else
{
x_234 = x_231;
goto block_263;
}
block_263:
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; uint8_t x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; uint64_t x_245; lean_object* x_246; lean_object* x_247; size_t x_248; lean_object* x_249; lean_object* x_250; size_t x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; uint8_t x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; 
x_235 = lean_mk_string_unchecked("Lean", 4, 4);
x_236 = lean_mk_string_unchecked("Server", 6, 6);
x_237 = lean_mk_string_unchecked("FileWorker", 10, 10);
x_238 = lean_mk_string_unchecked("setupImports", 12, 12);
x_239 = l_Lean_Name_mkStr4(x_235, x_236, x_237, x_238);
x_240 = lean_unbox(x_9);
x_241 = l_Lean_Name_toString(x_239, x_240, x_233);
x_242 = l_Lean_Language_Snapshot_Diagnostics_empty;
x_243 = lean_box(0);
x_244 = lean_unsigned_to_nat(0u);
x_245 = lean_uint64_of_nat(x_244);
x_246 = lean_unsigned_to_nat(2u);
x_247 = lean_unsigned_to_nat(5u);
x_248 = lean_usize_of_nat(x_247);
x_249 = lean_usize_to_nat(x_248);
x_250 = lean_nat_pow(x_246, x_249);
lean_dec(x_249);
x_251 = lean_usize_of_nat(x_250);
lean_dec(x_250);
x_252 = lean_usize_to_nat(x_251);
x_253 = lean_mk_empty_array_with_capacity(x_252);
lean_dec(x_252);
lean_inc(x_253);
x_254 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_254, 0, x_253);
x_255 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_255, 0, x_254);
lean_ctor_set(x_255, 1, x_253);
lean_ctor_set(x_255, 2, x_244);
lean_ctor_set(x_255, 3, x_244);
lean_ctor_set_usize(x_255, 4, x_248);
x_256 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_256, 0, x_255);
lean_ctor_set_uint64(x_256, sizeof(void*)*1, x_245);
x_257 = lean_box(0);
x_258 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_258, 0, x_241);
lean_ctor_set(x_258, 1, x_242);
lean_ctor_set(x_258, 2, x_243);
lean_ctor_set(x_258, 3, x_256);
x_259 = lean_unbox(x_9);
lean_dec(x_9);
lean_ctor_set_uint8(x_258, sizeof(void*)*4, x_259);
if (lean_is_scalar(x_228)) {
 x_260 = lean_alloc_ctor(0, 2, 0);
} else {
 x_260 = x_228;
}
lean_ctor_set(x_260, 0, x_258);
lean_ctor_set(x_260, 1, x_257);
x_261 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_261, 0, x_260);
if (lean_is_scalar(x_232)) {
 x_262 = lean_alloc_ctor(0, 2, 0);
} else {
 x_262 = x_232;
}
lean_ctor_set(x_262, 0, x_261);
lean_ctor_set(x_262, 1, x_234);
return x_262;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_setupImports___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_FileWorker_setupImports___lam__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_setupImports___lam__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_Server_FileWorker_setupImports___lam__2(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_setupImports___lam__4___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Server_FileWorker_setupImports___lam__4(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_initializeWorker_mkLspOutputChannel___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_1);
if (x_14 == 0)
{
lean_ctor_set_tag(x_1, 4);
x_2 = x_1;
goto block_13;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_2 = x_16;
goto block_13;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_1);
if (x_17 == 0)
{
lean_ctor_set_tag(x_1, 5);
x_2 = x_1;
goto block_13;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
lean_dec(x_1);
x_19 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_2 = x_19;
goto block_13;
}
}
block_13:
{
lean_object* x_3; 
x_3 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_2193_(x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec(x_3);
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_nat_to_int(x_7);
lean_ctor_set(x_3, 0, x_8);
return x_3;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
lean_dec(x_3);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_nat_to_int(x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_initializeWorker_mkLspOutputChannel___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_19; lean_object* x_32; lean_object* x_35; lean_object* x_43; 
if (lean_obj_tag(x_4) == 1)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_48 = lean_ctor_get(x_4, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_4, 1);
lean_inc(x_49);
x_50 = lean_mk_string_unchecked("textDocument/publishDiagnostics", 31, 31);
x_51 = lean_string_dec_eq(x_48, x_50);
lean_dec(x_50);
if (x_51 == 0)
{
lean_object* x_52; uint8_t x_53; 
x_52 = lean_mk_string_unchecked("$/lean/fileProgress", 19, 19);
x_53 = lean_string_dec_eq(x_48, x_52);
lean_dec(x_52);
if (x_53 == 0)
{
lean_object* x_54; uint8_t x_55; 
x_54 = lean_mk_string_unchecked("$/lean/ileanInfoUpdate", 22, 22);
x_55 = lean_string_dec_eq(x_48, x_54);
lean_dec(x_54);
if (x_55 == 0)
{
lean_object* x_56; uint8_t x_57; 
x_56 = lean_mk_string_unchecked("$/lean/ileanInfoFinal", 21, 21);
x_57 = lean_string_dec_eq(x_48, x_56);
lean_dec(x_56);
lean_dec(x_48);
if (x_57 == 0)
{
lean_dec(x_49);
lean_dec(x_3);
x_6 = x_5;
goto block_18;
}
else
{
if (lean_obj_tag(x_49) == 0)
{
lean_dec(x_3);
x_6 = x_5;
goto block_18;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_49, 0);
lean_inc(x_58);
lean_dec(x_49);
x_59 = lean_apply_1(x_3, x_58);
x_32 = x_59;
goto block_34;
}
}
}
else
{
lean_dec(x_48);
if (lean_obj_tag(x_49) == 0)
{
lean_dec(x_3);
x_6 = x_5;
goto block_18;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_49, 0);
lean_inc(x_60);
lean_dec(x_49);
x_61 = lean_apply_1(x_3, x_60);
x_32 = x_61;
goto block_34;
}
}
}
else
{
lean_dec(x_48);
lean_dec(x_3);
if (lean_obj_tag(x_49) == 0)
{
x_6 = x_5;
goto block_18;
}
else
{
lean_object* x_62; 
x_62 = lean_ctor_get(x_49, 0);
lean_inc(x_62);
lean_dec(x_49);
if (lean_obj_tag(x_62) == 0)
{
uint8_t x_63; 
x_63 = !lean_is_exclusive(x_62);
if (x_63 == 0)
{
lean_ctor_set_tag(x_62, 4);
x_35 = x_62;
goto block_42;
}
else
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_62, 0);
lean_inc(x_64);
lean_dec(x_62);
x_65 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_65, 0, x_64);
x_35 = x_65;
goto block_42;
}
}
else
{
uint8_t x_66; 
x_66 = !lean_is_exclusive(x_62);
if (x_66 == 0)
{
lean_ctor_set_tag(x_62, 5);
x_35 = x_62;
goto block_42;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_62, 0);
lean_inc(x_67);
lean_dec(x_62);
x_68 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_68, 0, x_67);
x_35 = x_68;
goto block_42;
}
}
}
}
}
else
{
lean_dec(x_48);
lean_dec(x_3);
if (lean_obj_tag(x_49) == 0)
{
x_6 = x_5;
goto block_18;
}
else
{
lean_object* x_69; 
x_69 = lean_ctor_get(x_49, 0);
lean_inc(x_69);
lean_dec(x_49);
if (lean_obj_tag(x_69) == 0)
{
uint8_t x_70; 
x_70 = !lean_is_exclusive(x_69);
if (x_70 == 0)
{
lean_ctor_set_tag(x_69, 4);
x_43 = x_69;
goto block_47;
}
else
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_69, 0);
lean_inc(x_71);
lean_dec(x_69);
x_72 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_72, 0, x_71);
x_43 = x_72;
goto block_47;
}
}
else
{
uint8_t x_73; 
x_73 = !lean_is_exclusive(x_69);
if (x_73 == 0)
{
lean_ctor_set_tag(x_69, 5);
x_43 = x_69;
goto block_47;
}
else
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_69, 0);
lean_inc(x_74);
lean_dec(x_69);
x_75 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_75, 0, x_74);
x_43 = x_75;
goto block_47;
}
}
}
}
}
else
{
lean_dec(x_3);
x_6 = x_5;
goto block_18;
}
block_18:
{
lean_object* x_7; 
x_7 = l_IO_FS_Stream_writeLspMessage(x_1, x_4, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
return x_7;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_7);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_7, 0);
lean_dec(x_13);
x_14 = lean_box(0);
lean_ctor_set_tag(x_7, 0);
lean_ctor_set(x_7, 0, x_14);
return x_7;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_7, 1);
lean_inc(x_15);
lean_dec(x_7);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
}
block_31:
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_st_ref_get(x_2, x_5);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
x_24 = lean_int_dec_lt(x_19, x_22);
lean_dec(x_22);
lean_dec(x_19);
if (x_24 == 0)
{
lean_free_object(x_20);
x_6 = x_23;
goto block_18;
}
else
{
lean_object* x_25; 
lean_dec(x_4);
lean_dec(x_1);
x_25 = lean_box(0);
lean_ctor_set(x_20, 0, x_25);
return x_20;
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_20, 0);
x_27 = lean_ctor_get(x_20, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_20);
x_28 = lean_int_dec_lt(x_19, x_26);
lean_dec(x_26);
lean_dec(x_19);
if (x_28 == 0)
{
x_6 = x_27;
goto block_18;
}
else
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_4);
lean_dec(x_1);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
return x_30;
}
}
}
block_34:
{
if (lean_obj_tag(x_32) == 0)
{
x_6 = x_5;
goto block_18;
}
else
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec(x_32);
x_19 = x_33;
goto block_31;
}
}
block_42:
{
lean_object* x_36; 
x_36 = l___private_Lean_Data_Lsp_Extra_0__Lean_Lsp_fromJsonLeanFileProgressParams____x40_Lean_Data_Lsp_Extra___hyg_1125_(x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_dec(x_36);
x_6 = x_5;
goto block_18;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_dec(x_36);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec(x_37);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
if (lean_obj_tag(x_39) == 0)
{
x_6 = x_5;
goto block_18;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec(x_39);
x_41 = lean_nat_to_int(x_40);
x_19 = x_41;
goto block_31;
}
}
}
block_47:
{
lean_object* x_44; 
x_44 = l___private_Lean_Data_Lsp_Diagnostics_0__Lean_Lsp_fromJsonPublishDiagnosticsParams____x40_Lean_Data_Lsp_Diagnostics___hyg_2484_(x_43);
if (lean_obj_tag(x_44) == 0)
{
lean_dec(x_44);
x_6 = x_5;
goto block_18;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_32 = x_46;
goto block_34;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_initializeWorker_mkLspOutputChannel(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_4 = lean_box(0);
x_5 = l_Std_CloseableChannel_new___redArg(x_4, x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_initializeWorker_mkLspOutputChannel___lam__0), 1, 0);
x_9 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_initializeWorker_mkLspOutputChannel___lam__1___boxed), 5, 3);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_2);
lean_closure_set(x_9, 2, x_8);
x_10 = l_Lean_JsonRpc_instInhabitedMessage;
x_11 = lean_unsigned_to_nat(9u);
lean_inc(x_6);
x_12 = l_Std_Channel_forAsync___redArg(x_10, x_9, x_6, x_11, x_7);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
lean_ctor_set(x_12, 0, x_6);
return x_12;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_6);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_initializeWorker_mkLspOutputChannel___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Server_FileWorker_initializeWorker_mkLspOutputChannel___lam__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_initializeWorker_getImportClosure_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 3);
lean_inc(x_2);
lean_dec(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_mk_empty_array_with_capacity(x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_Language_SnapshotTask_get___redArg(x_6);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_mk_empty_array_with_capacity(x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
lean_dec(x_8);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_Lean_Environment_allImportedModuleNames(x_13);
lean_dec(x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Server_FileWorker_initializeWorker_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_6, 1);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_10 = lean_ctor_get(x_6, 0);
x_11 = lean_ctor_get(x_8, 0);
x_12 = lean_ctor_get(x_8, 1);
lean_dec(x_12);
x_13 = lean_box(0);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_array_uset(x_4, x_3, x_13);
lean_inc(x_1);
lean_ctor_set(x_6, 1, x_14);
lean_ctor_set(x_6, 0, x_1);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_6);
x_17 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_17, 0, x_11);
lean_ctor_set(x_17, 1, x_14);
lean_ctor_set(x_17, 2, x_16);
lean_ctor_set(x_8, 1, x_17);
lean_ctor_set(x_8, 0, x_10);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_usize_of_nat(x_18);
x_20 = lean_usize_add(x_3, x_19);
x_21 = lean_array_uset(x_15, x_3, x_8);
x_3 = x_20;
x_4 = x_21;
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; size_t x_32; size_t x_33; lean_object* x_34; 
x_23 = lean_ctor_get(x_6, 0);
x_24 = lean_ctor_get(x_8, 0);
lean_inc(x_24);
lean_dec(x_8);
x_25 = lean_box(0);
x_26 = lean_unsigned_to_nat(0u);
x_27 = lean_array_uset(x_4, x_3, x_25);
lean_inc(x_1);
lean_ctor_set(x_6, 1, x_26);
lean_ctor_set(x_6, 0, x_1);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_6);
x_29 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_29, 0, x_24);
lean_ctor_set(x_29, 1, x_26);
lean_ctor_set(x_29, 2, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_23);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_usize_of_nat(x_31);
x_33 = lean_usize_add(x_3, x_32);
x_34 = lean_array_uset(x_27, x_3, x_30);
x_3 = x_33;
x_4 = x_34;
goto _start;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; size_t x_48; size_t x_49; lean_object* x_50; 
x_36 = lean_ctor_get(x_6, 1);
x_37 = lean_ctor_get(x_6, 0);
lean_inc(x_36);
lean_inc(x_37);
lean_dec(x_6);
x_38 = lean_ctor_get(x_36, 0);
lean_inc(x_38);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_39 = x_36;
} else {
 lean_dec_ref(x_36);
 x_39 = lean_box(0);
}
x_40 = lean_box(0);
x_41 = lean_unsigned_to_nat(0u);
x_42 = lean_array_uset(x_4, x_3, x_40);
lean_inc(x_1);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_1);
lean_ctor_set(x_43, 1, x_41);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_45 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_45, 0, x_38);
lean_ctor_set(x_45, 1, x_41);
lean_ctor_set(x_45, 2, x_44);
if (lean_is_scalar(x_39)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_39;
}
lean_ctor_set(x_46, 0, x_37);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_unsigned_to_nat(1u);
x_48 = lean_usize_of_nat(x_47);
x_49 = lean_usize_add(x_3, x_48);
x_50 = lean_array_uset(x_42, x_3, x_46);
x_3 = x_49;
x_4 = x_50;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_Server_FileWorker_initializeWorker_spec__1_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_2, x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_array_uget(x_1, x_2);
x_8 = l_Lean_Server_documentUriFromModule_x3f(x_7, x_5);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
if (lean_obj_tag(x_9) == 0)
{
x_11 = x_4;
goto block_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_9, 0);
lean_inc(x_17);
lean_dec(x_9);
x_18 = lean_array_push(x_4, x_17);
x_11 = x_18;
goto block_16;
}
block_16:
{
lean_object* x_12; size_t x_13; size_t x_14; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_usize_of_nat(x_12);
x_14 = lean_usize_add(x_2, x_13);
x_2 = x_14;
x_4 = x_11;
x_5 = x_10;
goto _start;
}
}
else
{
uint8_t x_19; 
lean_dec(x_4);
x_19 = !lean_is_exclusive(x_8);
if (x_19 == 0)
{
return x_8;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_8, 0);
x_21 = lean_ctor_get(x_8, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_8);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_4);
lean_ctor_set(x_23, 1, x_5);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___Lean_Server_FileWorker_initializeWorker_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_mk_empty_array_with_capacity(x_5);
x_7 = lean_nat_dec_lt(x_2, x_3);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_get_size(x_1);
x_10 = lean_nat_dec_le(x_3, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_4);
return x_11;
}
else
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_usize_of_nat(x_2);
x_13 = lean_usize_of_nat(x_3);
x_14 = l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_Server_FileWorker_initializeWorker_spec__1_spec__1(x_1, x_12, x_13, x_6, x_4);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___Lean_Server_FileWorker_initializeWorker_spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanImportClosureParams____x40_Lean_Data_Lsp_Internal___hyg_2431_(x_1);
if (lean_obj_tag(x_2) == 5)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; 
lean_ctor_set_tag(x_2, 1);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_2);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_mk_string_unchecked("expected structured object, got '", 33, 33);
x_9 = lean_unsigned_to_nat(80u);
x_10 = l_Lean_Json_pretty(x_2, x_9);
x_11 = lean_string_append(x_8, x_10);
lean_dec(x_10);
x_12 = lean_mk_string_unchecked("'", 1, 1);
x_13 = lean_string_append(x_11, x_12);
lean_dec(x_12);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Server_FileWorker_initializeWorker_spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_RBNode_insert___at___Lean_Json_mkObj_spec__0___redArg(x_4, x_7, x_8);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_usize_of_nat(x_10);
x_12 = lean_usize_add(x_2, x_11);
x_2 = x_12;
x_4 = x_9;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_initializeWorker___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_filterMapM___at___Lean_Server_FileWorker_initializeWorker_spec__1(x_1, x_2, x_3, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_19; lean_object* x_20; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_mkImportClosureNotification(x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_dec(x_9);
x_20 = l_Lean_Json_toStructured_x3f___at___Lean_Server_FileWorker_initializeWorker_spec__3(x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
lean_dec(x_20);
x_21 = lean_box(0);
x_11 = x_21;
goto block_18;
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
x_11 = x_20;
goto block_18;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_11 = x_24;
goto block_18;
}
}
block_18:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Std_Channel_send___redArg(x_4, x_12, x_8);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
return x_13;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
else
{
uint8_t x_25; 
lean_dec(x_4);
x_25 = !lean_is_exclusive(x_6);
if (x_25 == 0)
{
return x_6;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_6, 0);
x_27 = lean_ctor_get(x_6, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_6);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_initializeWorker(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; uint8_t x_96; lean_object* x_135; 
x_135 = lean_ctor_get(x_4, 3);
lean_inc(x_135);
if (lean_obj_tag(x_135) == 0)
{
goto block_134;
}
else
{
lean_object* x_136; lean_object* x_137; 
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
lean_dec(x_135);
x_137 = lean_ctor_get(x_136, 1);
lean_inc(x_137);
lean_dec(x_136);
if (lean_obj_tag(x_137) == 0)
{
goto block_134;
}
else
{
lean_object* x_138; uint8_t x_139; 
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
lean_dec(x_137);
x_139 = lean_unbox(x_138);
lean_dec(x_138);
x_96 = x_139;
goto block_131;
}
}
block_95:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_18 = lean_st_mk_ref(x_17, x_8);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_11);
lean_inc(x_5);
lean_inc(x_1);
x_21 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_setupImports), 6, 3);
lean_closure_set(x_21, 0, x_1);
lean_closure_set(x_21, 1, x_5);
lean_closure_set(x_21, 2, x_11);
x_22 = lean_alloc_closure((void*)(l_Lean_Language_Lean_process), 4, 1);
lean_closure_set(x_22, 0, x_21);
x_23 = l_Lean_Language_mkIncrementalProcessor(lean_box(0), x_22, x_20);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_1);
x_26 = l_Lean_Server_DocumentMeta_mkInputContext(x_1);
lean_inc(x_24);
x_27 = lean_apply_2(x_24, x_26, x_25);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
lean_inc(x_28);
x_30 = l_Lean_Server_FileWorker_initializeWorker_getImportClosure_x3f(x_28);
x_31 = lean_array_get_size(x_30);
x_32 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_initializeWorker___lam__0___boxed), 5, 4);
lean_closure_set(x_32, 0, x_30);
lean_closure_set(x_32, 1, x_9);
lean_closure_set(x_32, 2, x_31);
lean_closure_set(x_32, 3, x_7);
x_33 = l_Lean_Server_ServerTask_IO_asTask(lean_box(0), x_32, x_29);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_st_mk_ref(x_14, x_34);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_37 = lean_ctor_get(x_35, 0);
x_38 = lean_ctor_get(x_35, 1);
x_39 = l_IO_CancelToken_new(x_38);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_41 = lean_ctor_get(x_39, 0);
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_28);
x_43 = l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps(x_28);
x_44 = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(x_44, 0, x_11);
lean_ctor_set(x_44, 1, x_13);
lean_ctor_set(x_44, 2, x_15);
lean_ctor_set(x_44, 3, x_10);
lean_ctor_set(x_44, 4, x_19);
lean_ctor_set(x_44, 5, x_12);
lean_ctor_set(x_44, 6, x_3);
lean_ctor_set(x_44, 7, x_4);
lean_ctor_set(x_44, 8, x_24);
lean_ctor_set(x_44, 9, x_5);
lean_ctor_set_uint8(x_44, sizeof(void*)*10, x_16);
x_45 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_45, 0, x_1);
lean_ctor_set(x_45, 1, x_28);
lean_ctor_set(x_45, 2, x_43);
lean_ctor_set(x_45, 3, x_37);
lean_inc(x_41);
lean_inc(x_45);
lean_inc(x_44);
x_46 = l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots(x_44, x_45, x_41, x_42);
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_48 = lean_ctor_get(x_46, 0);
lean_ctor_set(x_39, 1, x_48);
lean_ctor_set(x_39, 0, x_45);
x_49 = lean_box(0);
x_50 = lean_box(0);
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_52, 0, x_39);
lean_ctor_set(x_52, 1, x_41);
lean_ctor_set(x_52, 2, x_49);
lean_ctor_set(x_52, 3, x_50);
lean_ctor_set(x_52, 4, x_51);
lean_ctor_set(x_35, 1, x_52);
lean_ctor_set(x_35, 0, x_44);
lean_ctor_set(x_46, 0, x_35);
return x_46;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_53 = lean_ctor_get(x_46, 0);
x_54 = lean_ctor_get(x_46, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_46);
lean_ctor_set(x_39, 1, x_53);
lean_ctor_set(x_39, 0, x_45);
x_55 = lean_box(0);
x_56 = lean_box(0);
x_57 = lean_box(0);
x_58 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_58, 0, x_39);
lean_ctor_set(x_58, 1, x_41);
lean_ctor_set(x_58, 2, x_55);
lean_ctor_set(x_58, 3, x_56);
lean_ctor_set(x_58, 4, x_57);
lean_ctor_set(x_35, 1, x_58);
lean_ctor_set(x_35, 0, x_44);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_35);
lean_ctor_set(x_59, 1, x_54);
return x_59;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_60 = lean_ctor_get(x_39, 0);
x_61 = lean_ctor_get(x_39, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_39);
lean_inc(x_28);
x_62 = l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps(x_28);
x_63 = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(x_63, 0, x_11);
lean_ctor_set(x_63, 1, x_13);
lean_ctor_set(x_63, 2, x_15);
lean_ctor_set(x_63, 3, x_10);
lean_ctor_set(x_63, 4, x_19);
lean_ctor_set(x_63, 5, x_12);
lean_ctor_set(x_63, 6, x_3);
lean_ctor_set(x_63, 7, x_4);
lean_ctor_set(x_63, 8, x_24);
lean_ctor_set(x_63, 9, x_5);
lean_ctor_set_uint8(x_63, sizeof(void*)*10, x_16);
x_64 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_64, 0, x_1);
lean_ctor_set(x_64, 1, x_28);
lean_ctor_set(x_64, 2, x_62);
lean_ctor_set(x_64, 3, x_37);
lean_inc(x_60);
lean_inc(x_64);
lean_inc(x_63);
x_65 = l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots(x_63, x_64, x_60, x_61);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_68 = x_65;
} else {
 lean_dec_ref(x_65);
 x_68 = lean_box(0);
}
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_64);
lean_ctor_set(x_69, 1, x_66);
x_70 = lean_box(0);
x_71 = lean_box(0);
x_72 = lean_box(0);
x_73 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_73, 0, x_69);
lean_ctor_set(x_73, 1, x_60);
lean_ctor_set(x_73, 2, x_70);
lean_ctor_set(x_73, 3, x_71);
lean_ctor_set(x_73, 4, x_72);
lean_ctor_set(x_35, 1, x_73);
lean_ctor_set(x_35, 0, x_63);
if (lean_is_scalar(x_68)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_68;
}
lean_ctor_set(x_74, 0, x_35);
lean_ctor_set(x_74, 1, x_67);
return x_74;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_75 = lean_ctor_get(x_35, 0);
x_76 = lean_ctor_get(x_35, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_35);
x_77 = l_IO_CancelToken_new(x_76);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_80 = x_77;
} else {
 lean_dec_ref(x_77);
 x_80 = lean_box(0);
}
lean_inc(x_28);
x_81 = l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps(x_28);
x_82 = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(x_82, 0, x_11);
lean_ctor_set(x_82, 1, x_13);
lean_ctor_set(x_82, 2, x_15);
lean_ctor_set(x_82, 3, x_10);
lean_ctor_set(x_82, 4, x_19);
lean_ctor_set(x_82, 5, x_12);
lean_ctor_set(x_82, 6, x_3);
lean_ctor_set(x_82, 7, x_4);
lean_ctor_set(x_82, 8, x_24);
lean_ctor_set(x_82, 9, x_5);
lean_ctor_set_uint8(x_82, sizeof(void*)*10, x_16);
x_83 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_83, 0, x_1);
lean_ctor_set(x_83, 1, x_28);
lean_ctor_set(x_83, 2, x_81);
lean_ctor_set(x_83, 3, x_75);
lean_inc(x_78);
lean_inc(x_83);
lean_inc(x_82);
x_84 = l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots(x_82, x_83, x_78, x_79);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_87 = x_84;
} else {
 lean_dec_ref(x_84);
 x_87 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_80;
}
lean_ctor_set(x_88, 0, x_83);
lean_ctor_set(x_88, 1, x_85);
x_89 = lean_box(0);
x_90 = lean_box(0);
x_91 = lean_box(0);
x_92 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_92, 0, x_88);
lean_ctor_set(x_92, 1, x_78);
lean_ctor_set(x_92, 2, x_89);
lean_ctor_set(x_92, 3, x_90);
lean_ctor_set(x_92, 4, x_91);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_82);
lean_ctor_set(x_93, 1, x_92);
if (lean_is_scalar(x_87)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_87;
}
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_86);
return x_94;
}
}
block_131:
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; size_t x_122; size_t x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_97 = lean_unsigned_to_nat(0u);
x_98 = lean_nat_to_int(x_97);
lean_inc(x_98);
x_99 = lean_st_mk_ref(x_98, x_6);
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec(x_99);
x_102 = lean_st_mk_ref(x_98, x_101);
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
x_105 = l_Array_empty(lean_box(0));
lean_inc(x_105);
x_106 = lean_st_mk_ref(x_105, x_104);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec(x_106);
x_109 = lean_box(1);
x_110 = lean_st_mk_ref(x_109, x_108);
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
lean_dec(x_110);
lean_inc(x_100);
x_113 = l_Lean_Server_FileWorker_initializeWorker_mkLspOutputChannel(x_2, x_100, x_112);
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
lean_dec(x_113);
x_116 = lean_io_mono_ms_now(x_115);
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
lean_dec(x_116);
x_119 = l_Lean_Server_partialLspRequestHandlerMethods(x_118);
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec(x_119);
x_122 = lean_array_size(x_120);
x_123 = lean_usize_of_nat(x_97);
x_124 = l_Array_mapMUnsafe_map___at___Lean_Server_FileWorker_initializeWorker_spec__0(x_117, x_122, x_123, x_120);
x_125 = lean_box(0);
x_126 = lean_array_get_size(x_124);
x_127 = lean_nat_dec_lt(x_97, x_126);
if (x_127 == 0)
{
lean_dec(x_126);
lean_dec(x_124);
lean_inc(x_114);
x_7 = x_114;
x_8 = x_121;
x_9 = x_97;
x_10 = x_107;
x_11 = x_114;
x_12 = x_111;
x_13 = x_100;
x_14 = x_105;
x_15 = x_103;
x_16 = x_96;
x_17 = x_125;
goto block_95;
}
else
{
uint8_t x_128; 
x_128 = lean_nat_dec_le(x_126, x_126);
if (x_128 == 0)
{
lean_dec(x_126);
lean_dec(x_124);
lean_inc(x_114);
x_7 = x_114;
x_8 = x_121;
x_9 = x_97;
x_10 = x_107;
x_11 = x_114;
x_12 = x_111;
x_13 = x_100;
x_14 = x_105;
x_15 = x_103;
x_16 = x_96;
x_17 = x_125;
goto block_95;
}
else
{
size_t x_129; lean_object* x_130; 
x_129 = lean_usize_of_nat(x_126);
lean_dec(x_126);
x_130 = l_Array_foldlMUnsafe_fold___at___Lean_Server_FileWorker_initializeWorker_spec__4(x_124, x_123, x_129, x_125);
lean_dec(x_124);
lean_inc(x_114);
x_7 = x_114;
x_8 = x_121;
x_9 = x_97;
x_10 = x_107;
x_11 = x_114;
x_12 = x_111;
x_13 = x_100;
x_14 = x_105;
x_15 = x_103;
x_16 = x_96;
x_17 = x_130;
goto block_95;
}
}
}
block_134:
{
lean_object* x_132; uint8_t x_133; 
x_132 = lean_box(0);
x_133 = lean_unbox(x_132);
x_96 = x_133;
goto block_131;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Server_FileWorker_initializeWorker_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at___Lean_Server_FileWorker_initializeWorker_spec__0(x_1, x_5, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_Server_FileWorker_initializeWorker_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_Server_FileWorker_initializeWorker_spec__1_spec__1(x_1, x_6, x_7, x_4, x_5);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___Lean_Server_FileWorker_initializeWorker_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_filterMapM___at___Lean_Server_FileWorker_initializeWorker_spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Server_FileWorker_initializeWorker_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Lean_Server_FileWorker_initializeWorker_spec__4(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_initializeWorker___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Server_FileWorker_initializeWorker___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_sendServerRequest___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_30; 
x_7 = lean_ctor_get(x_3, 2);
lean_inc(x_7);
x_8 = lean_st_ref_take(x_7, x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_to_int(x_11);
x_13 = lean_int_add(x_9, x_12);
lean_dec(x_12);
x_14 = lean_st_ref_set(x_7, x_13, x_10);
lean_dec(x_7);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_Lean_JsonNumber_fromInt(x_9);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
lean_inc(x_17);
x_18 = l_Lean_Server_FileWorker_WorkerContext_initPendingServerRequest___redArg(x_2, x_3, x_17, x_15);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_3, 0);
lean_inc(x_21);
lean_dec(x_3);
x_30 = l_Lean_Json_toStructured_x3f___redArg(x_1, x_5);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; 
lean_dec(x_30);
x_31 = lean_box(0);
x_22 = x_31;
goto block_29;
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_30);
if (x_32 == 0)
{
x_22 = x_30;
goto block_29;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_30, 0);
lean_inc(x_33);
lean_dec(x_30);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_22 = x_34;
goto block_29;
}
}
block_29:
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_23, 0, x_17);
lean_ctor_set(x_23, 1, x_4);
lean_ctor_set(x_23, 2, x_22);
x_24 = l_Std_Channel_Sync_send___redArg(x_21, x_23, x_20);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
lean_ctor_set(x_24, 0, x_19);
return x_24;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_19);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_sendServerRequest(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Server_FileWorker_sendServerRequest___redArg(x_2, x_4, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_sendServerRequest___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Server_FileWorker_sendServerRequest(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___Lean_Server_FileWorker_WorkerContext_initPendingServerRequest___at___Lean_Server_FileWorker_sendServerRequest___at___Lean_Server_FileWorker_sendUntypedServerRequest_spec__0_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 3);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 4);
lean_inc(x_8);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 lean_ctor_release(x_3, 4);
 x_9 = x_3;
} else {
 lean_dec_ref(x_3);
 x_9 = lean_box(0);
}
lean_inc(x_5);
lean_inc(x_1);
x_10 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_ordRequestID____x40_Lean_Data_JsonRpc___hyg_126_(x_1, x_5);
switch (x_10) {
case 0:
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_4);
x_11 = l_Std_DTreeMap_Internal_Impl_insert___at___Lean_Server_FileWorker_WorkerContext_initPendingServerRequest___at___Lean_Server_FileWorker_sendServerRequest___at___Lean_Server_FileWorker_sendUntypedServerRequest_spec__0_spec__0_spec__0___redArg(x_1, x_2, x_7);
x_12 = lean_unsigned_to_nat(1u);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_13 = lean_ctor_get(x_8, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_11, 2);
lean_inc(x_16);
x_17 = lean_ctor_get(x_11, 3);
lean_inc(x_17);
x_18 = lean_ctor_get(x_11, 4);
lean_inc(x_18);
x_19 = lean_unsigned_to_nat(3u);
x_20 = lean_nat_mul(x_19, x_13);
x_21 = lean_nat_dec_lt(x_20, x_14);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
x_22 = lean_nat_add(x_12, x_14);
lean_dec(x_14);
x_23 = lean_nat_add(x_22, x_13);
lean_dec(x_13);
lean_dec(x_22);
if (lean_is_scalar(x_9)) {
 x_24 = lean_alloc_ctor(0, 5, 0);
} else {
 x_24 = x_9;
}
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_5);
lean_ctor_set(x_24, 2, x_6);
lean_ctor_set(x_24, 3, x_11);
lean_ctor_set(x_24, 4, x_8);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 lean_ctor_release(x_11, 2);
 lean_ctor_release(x_11, 3);
 lean_ctor_release(x_11, 4);
 x_25 = x_11;
} else {
 lean_dec_ref(x_11);
 x_25 = lean_box(0);
}
x_26 = lean_ctor_get(x_17, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_18, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_18, 1);
lean_inc(x_28);
x_29 = lean_ctor_get(x_18, 2);
lean_inc(x_29);
x_30 = lean_ctor_get(x_18, 3);
lean_inc(x_30);
x_31 = lean_ctor_get(x_18, 4);
lean_inc(x_31);
x_32 = lean_nat_shiftl(x_26, x_12);
x_33 = lean_nat_dec_lt(x_27, x_32);
lean_dec(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_44; lean_object* x_45; 
lean_dec(x_27);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 lean_ctor_release(x_18, 2);
 lean_ctor_release(x_18, 3);
 lean_ctor_release(x_18, 4);
 x_34 = x_18;
} else {
 lean_dec_ref(x_18);
 x_34 = lean_box(0);
}
x_35 = lean_nat_add(x_12, x_14);
lean_dec(x_14);
x_36 = lean_nat_add(x_35, x_13);
lean_dec(x_35);
x_44 = lean_nat_add(x_12, x_26);
lean_dec(x_26);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_30, 0);
lean_inc(x_52);
x_45 = x_52;
goto block_51;
}
else
{
lean_object* x_53; 
x_53 = lean_unsigned_to_nat(0u);
x_45 = x_53;
goto block_51;
}
block_43:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_nat_add(x_38, x_39);
lean_dec(x_39);
lean_dec(x_38);
if (lean_is_scalar(x_34)) {
 x_41 = lean_alloc_ctor(0, 5, 0);
} else {
 x_41 = x_34;
}
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_5);
lean_ctor_set(x_41, 2, x_6);
lean_ctor_set(x_41, 3, x_31);
lean_ctor_set(x_41, 4, x_8);
if (lean_is_scalar(x_25)) {
 x_42 = lean_alloc_ctor(0, 5, 0);
} else {
 x_42 = x_25;
}
lean_ctor_set(x_42, 0, x_36);
lean_ctor_set(x_42, 1, x_28);
lean_ctor_set(x_42, 2, x_29);
lean_ctor_set(x_42, 3, x_37);
lean_ctor_set(x_42, 4, x_41);
return x_42;
}
block_51:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_nat_add(x_44, x_45);
lean_dec(x_45);
lean_dec(x_44);
if (lean_is_scalar(x_9)) {
 x_47 = lean_alloc_ctor(0, 5, 0);
} else {
 x_47 = x_9;
}
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_15);
lean_ctor_set(x_47, 2, x_16);
lean_ctor_set(x_47, 3, x_17);
lean_ctor_set(x_47, 4, x_30);
x_48 = lean_nat_add(x_12, x_13);
lean_dec(x_13);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_31, 0);
lean_inc(x_49);
x_37 = x_47;
x_38 = x_48;
x_39 = x_49;
goto block_43;
}
else
{
lean_object* x_50; 
x_50 = lean_unsigned_to_nat(0u);
x_37 = x_47;
x_38 = x_48;
x_39 = x_50;
goto block_43;
}
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_9);
x_54 = lean_nat_add(x_12, x_14);
lean_dec(x_14);
x_55 = lean_nat_add(x_54, x_13);
lean_dec(x_54);
x_56 = lean_nat_add(x_12, x_13);
lean_dec(x_13);
x_57 = lean_nat_add(x_56, x_27);
lean_dec(x_27);
lean_dec(x_56);
lean_inc(x_8);
if (lean_is_scalar(x_25)) {
 x_58 = lean_alloc_ctor(0, 5, 0);
} else {
 x_58 = x_25;
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_5);
lean_ctor_set(x_58, 2, x_6);
lean_ctor_set(x_58, 3, x_18);
lean_ctor_set(x_58, 4, x_8);
x_59 = !lean_is_exclusive(x_8);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_60 = lean_ctor_get(x_8, 4);
lean_dec(x_60);
x_61 = lean_ctor_get(x_8, 3);
lean_dec(x_61);
x_62 = lean_ctor_get(x_8, 2);
lean_dec(x_62);
x_63 = lean_ctor_get(x_8, 1);
lean_dec(x_63);
x_64 = lean_ctor_get(x_8, 0);
lean_dec(x_64);
lean_ctor_set(x_8, 4, x_58);
lean_ctor_set(x_8, 3, x_17);
lean_ctor_set(x_8, 2, x_16);
lean_ctor_set(x_8, 1, x_15);
lean_ctor_set(x_8, 0, x_55);
return x_8;
}
else
{
lean_object* x_65; 
lean_dec(x_8);
x_65 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_65, 0, x_55);
lean_ctor_set(x_65, 1, x_15);
lean_ctor_set(x_65, 2, x_16);
lean_ctor_set(x_65, 3, x_17);
lean_ctor_set(x_65, 4, x_58);
return x_65;
}
}
}
}
else
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_11, 3);
lean_inc(x_66);
if (lean_obj_tag(x_66) == 0)
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_11);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_68 = lean_ctor_get(x_11, 4);
x_69 = lean_ctor_get(x_11, 1);
x_70 = lean_ctor_get(x_11, 2);
x_71 = lean_ctor_get(x_11, 3);
lean_dec(x_71);
x_72 = lean_ctor_get(x_11, 0);
lean_dec(x_72);
x_73 = lean_unsigned_to_nat(3u);
lean_inc(x_68);
lean_ctor_set(x_11, 3, x_68);
lean_ctor_set(x_11, 2, x_6);
lean_ctor_set(x_11, 1, x_5);
lean_ctor_set(x_11, 0, x_12);
if (lean_is_scalar(x_9)) {
 x_74 = lean_alloc_ctor(0, 5, 0);
} else {
 x_74 = x_9;
}
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_69);
lean_ctor_set(x_74, 2, x_70);
lean_ctor_set(x_74, 3, x_66);
lean_ctor_set(x_74, 4, x_11);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_75 = lean_ctor_get(x_11, 4);
x_76 = lean_ctor_get(x_11, 1);
x_77 = lean_ctor_get(x_11, 2);
lean_inc(x_75);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_11);
x_78 = lean_unsigned_to_nat(3u);
lean_inc(x_75);
x_79 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_79, 0, x_12);
lean_ctor_set(x_79, 1, x_5);
lean_ctor_set(x_79, 2, x_6);
lean_ctor_set(x_79, 3, x_75);
lean_ctor_set(x_79, 4, x_75);
if (lean_is_scalar(x_9)) {
 x_80 = lean_alloc_ctor(0, 5, 0);
} else {
 x_80 = x_9;
}
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_76);
lean_ctor_set(x_80, 2, x_77);
lean_ctor_set(x_80, 3, x_66);
lean_ctor_set(x_80, 4, x_79);
return x_80;
}
}
else
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_11, 4);
lean_inc(x_81);
if (lean_obj_tag(x_81) == 0)
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_11);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_83 = lean_ctor_get(x_11, 1);
x_84 = lean_ctor_get(x_11, 2);
x_85 = lean_ctor_get(x_11, 4);
lean_dec(x_85);
x_86 = lean_ctor_get(x_11, 3);
lean_dec(x_86);
x_87 = lean_ctor_get(x_11, 0);
lean_dec(x_87);
x_88 = !lean_is_exclusive(x_81);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_89 = lean_ctor_get(x_81, 1);
x_90 = lean_ctor_get(x_81, 2);
x_91 = lean_ctor_get(x_81, 4);
lean_dec(x_91);
x_92 = lean_ctor_get(x_81, 3);
lean_dec(x_92);
x_93 = lean_ctor_get(x_81, 0);
lean_dec(x_93);
x_94 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_81, 4, x_66);
lean_ctor_set(x_81, 3, x_66);
lean_ctor_set(x_81, 2, x_84);
lean_ctor_set(x_81, 1, x_83);
lean_ctor_set(x_81, 0, x_12);
lean_ctor_set(x_11, 4, x_66);
lean_ctor_set(x_11, 2, x_6);
lean_ctor_set(x_11, 1, x_5);
lean_ctor_set(x_11, 0, x_12);
if (lean_is_scalar(x_9)) {
 x_95 = lean_alloc_ctor(0, 5, 0);
} else {
 x_95 = x_9;
}
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_89);
lean_ctor_set(x_95, 2, x_90);
lean_ctor_set(x_95, 3, x_81);
lean_ctor_set(x_95, 4, x_11);
return x_95;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_96 = lean_ctor_get(x_81, 1);
x_97 = lean_ctor_get(x_81, 2);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_81);
x_98 = lean_unsigned_to_nat(3u);
x_99 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_99, 0, x_12);
lean_ctor_set(x_99, 1, x_83);
lean_ctor_set(x_99, 2, x_84);
lean_ctor_set(x_99, 3, x_66);
lean_ctor_set(x_99, 4, x_66);
lean_ctor_set(x_11, 4, x_66);
lean_ctor_set(x_11, 2, x_6);
lean_ctor_set(x_11, 1, x_5);
lean_ctor_set(x_11, 0, x_12);
if (lean_is_scalar(x_9)) {
 x_100 = lean_alloc_ctor(0, 5, 0);
} else {
 x_100 = x_9;
}
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_96);
lean_ctor_set(x_100, 2, x_97);
lean_ctor_set(x_100, 3, x_99);
lean_ctor_set(x_100, 4, x_11);
return x_100;
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_101 = lean_ctor_get(x_11, 1);
x_102 = lean_ctor_get(x_11, 2);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_11);
x_103 = lean_ctor_get(x_81, 1);
lean_inc(x_103);
x_104 = lean_ctor_get(x_81, 2);
lean_inc(x_104);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 lean_ctor_release(x_81, 2);
 lean_ctor_release(x_81, 3);
 lean_ctor_release(x_81, 4);
 x_105 = x_81;
} else {
 lean_dec_ref(x_81);
 x_105 = lean_box(0);
}
x_106 = lean_unsigned_to_nat(3u);
if (lean_is_scalar(x_105)) {
 x_107 = lean_alloc_ctor(0, 5, 0);
} else {
 x_107 = x_105;
}
lean_ctor_set(x_107, 0, x_12);
lean_ctor_set(x_107, 1, x_101);
lean_ctor_set(x_107, 2, x_102);
lean_ctor_set(x_107, 3, x_66);
lean_ctor_set(x_107, 4, x_66);
x_108 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_108, 0, x_12);
lean_ctor_set(x_108, 1, x_5);
lean_ctor_set(x_108, 2, x_6);
lean_ctor_set(x_108, 3, x_66);
lean_ctor_set(x_108, 4, x_66);
if (lean_is_scalar(x_9)) {
 x_109 = lean_alloc_ctor(0, 5, 0);
} else {
 x_109 = x_9;
}
lean_ctor_set(x_109, 0, x_106);
lean_ctor_set(x_109, 1, x_103);
lean_ctor_set(x_109, 2, x_104);
lean_ctor_set(x_109, 3, x_107);
lean_ctor_set(x_109, 4, x_108);
return x_109;
}
}
else
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_unsigned_to_nat(2u);
if (lean_is_scalar(x_9)) {
 x_111 = lean_alloc_ctor(0, 5, 0);
} else {
 x_111 = x_9;
}
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_5);
lean_ctor_set(x_111, 2, x_6);
lean_ctor_set(x_111, 3, x_11);
lean_ctor_set(x_111, 4, x_81);
return x_111;
}
}
}
}
case 1:
{
lean_object* x_112; 
lean_dec(x_6);
lean_dec(x_5);
if (lean_is_scalar(x_9)) {
 x_112 = lean_alloc_ctor(0, 5, 0);
} else {
 x_112 = x_9;
}
lean_ctor_set(x_112, 0, x_4);
lean_ctor_set(x_112, 1, x_1);
lean_ctor_set(x_112, 2, x_2);
lean_ctor_set(x_112, 3, x_7);
lean_ctor_set(x_112, 4, x_8);
return x_112;
}
default: 
{
lean_object* x_113; lean_object* x_114; 
lean_dec(x_4);
x_113 = l_Std_DTreeMap_Internal_Impl_insert___at___Lean_Server_FileWorker_WorkerContext_initPendingServerRequest___at___Lean_Server_FileWorker_sendServerRequest___at___Lean_Server_FileWorker_sendUntypedServerRequest_spec__0_spec__0_spec__0___redArg(x_1, x_2, x_8);
x_114 = lean_unsigned_to_nat(1u);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; 
x_115 = lean_ctor_get(x_7, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_113, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_113, 1);
lean_inc(x_117);
x_118 = lean_ctor_get(x_113, 2);
lean_inc(x_118);
x_119 = lean_ctor_get(x_113, 3);
lean_inc(x_119);
x_120 = lean_ctor_get(x_113, 4);
lean_inc(x_120);
x_121 = lean_unsigned_to_nat(3u);
x_122 = lean_nat_mul(x_121, x_115);
x_123 = lean_nat_dec_lt(x_122, x_116);
lean_dec(x_122);
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
lean_dec(x_120);
lean_dec(x_119);
lean_dec(x_118);
lean_dec(x_117);
x_124 = lean_nat_add(x_114, x_115);
lean_dec(x_115);
x_125 = lean_nat_add(x_124, x_116);
lean_dec(x_116);
lean_dec(x_124);
if (lean_is_scalar(x_9)) {
 x_126 = lean_alloc_ctor(0, 5, 0);
} else {
 x_126 = x_9;
}
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_5);
lean_ctor_set(x_126, 2, x_6);
lean_ctor_set(x_126, 3, x_7);
lean_ctor_set(x_126, 4, x_113);
return x_126;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; 
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 lean_ctor_release(x_113, 2);
 lean_ctor_release(x_113, 3);
 lean_ctor_release(x_113, 4);
 x_127 = x_113;
} else {
 lean_dec_ref(x_113);
 x_127 = lean_box(0);
}
x_128 = lean_ctor_get(x_119, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_119, 1);
lean_inc(x_129);
x_130 = lean_ctor_get(x_119, 2);
lean_inc(x_130);
x_131 = lean_ctor_get(x_119, 3);
lean_inc(x_131);
x_132 = lean_ctor_get(x_119, 4);
lean_inc(x_132);
x_133 = lean_ctor_get(x_120, 0);
lean_inc(x_133);
x_134 = lean_nat_shiftl(x_133, x_114);
x_135 = lean_nat_dec_lt(x_128, x_134);
lean_dec(x_134);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_146; 
lean_dec(x_128);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 lean_ctor_release(x_119, 2);
 lean_ctor_release(x_119, 3);
 lean_ctor_release(x_119, 4);
 x_136 = x_119;
} else {
 lean_dec_ref(x_119);
 x_136 = lean_box(0);
}
x_137 = lean_nat_add(x_114, x_115);
lean_dec(x_115);
x_138 = lean_nat_add(x_137, x_116);
lean_dec(x_116);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_153; 
x_153 = lean_ctor_get(x_131, 0);
lean_inc(x_153);
x_146 = x_153;
goto block_152;
}
else
{
lean_object* x_154; 
x_154 = lean_unsigned_to_nat(0u);
x_146 = x_154;
goto block_152;
}
block_145:
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_142 = lean_nat_add(x_139, x_141);
lean_dec(x_141);
lean_dec(x_139);
if (lean_is_scalar(x_136)) {
 x_143 = lean_alloc_ctor(0, 5, 0);
} else {
 x_143 = x_136;
}
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_117);
lean_ctor_set(x_143, 2, x_118);
lean_ctor_set(x_143, 3, x_132);
lean_ctor_set(x_143, 4, x_120);
if (lean_is_scalar(x_127)) {
 x_144 = lean_alloc_ctor(0, 5, 0);
} else {
 x_144 = x_127;
}
lean_ctor_set(x_144, 0, x_138);
lean_ctor_set(x_144, 1, x_129);
lean_ctor_set(x_144, 2, x_130);
lean_ctor_set(x_144, 3, x_140);
lean_ctor_set(x_144, 4, x_143);
return x_144;
}
block_152:
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_147 = lean_nat_add(x_137, x_146);
lean_dec(x_146);
lean_dec(x_137);
if (lean_is_scalar(x_9)) {
 x_148 = lean_alloc_ctor(0, 5, 0);
} else {
 x_148 = x_9;
}
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_5);
lean_ctor_set(x_148, 2, x_6);
lean_ctor_set(x_148, 3, x_7);
lean_ctor_set(x_148, 4, x_131);
x_149 = lean_nat_add(x_114, x_133);
lean_dec(x_133);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_150; 
x_150 = lean_ctor_get(x_132, 0);
lean_inc(x_150);
x_139 = x_149;
x_140 = x_148;
x_141 = x_150;
goto block_145;
}
else
{
lean_object* x_151; 
x_151 = lean_unsigned_to_nat(0u);
x_139 = x_149;
x_140 = x_148;
x_141 = x_151;
goto block_145;
}
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; 
lean_dec(x_133);
lean_dec(x_132);
lean_dec(x_131);
lean_dec(x_130);
lean_dec(x_129);
lean_dec(x_9);
x_155 = lean_nat_add(x_114, x_115);
lean_dec(x_115);
x_156 = lean_nat_add(x_155, x_116);
lean_dec(x_116);
x_157 = lean_nat_add(x_155, x_128);
lean_dec(x_128);
lean_dec(x_155);
lean_inc(x_7);
if (lean_is_scalar(x_127)) {
 x_158 = lean_alloc_ctor(0, 5, 0);
} else {
 x_158 = x_127;
}
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_5);
lean_ctor_set(x_158, 2, x_6);
lean_ctor_set(x_158, 3, x_7);
lean_ctor_set(x_158, 4, x_119);
x_159 = !lean_is_exclusive(x_7);
if (x_159 == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_160 = lean_ctor_get(x_7, 4);
lean_dec(x_160);
x_161 = lean_ctor_get(x_7, 3);
lean_dec(x_161);
x_162 = lean_ctor_get(x_7, 2);
lean_dec(x_162);
x_163 = lean_ctor_get(x_7, 1);
lean_dec(x_163);
x_164 = lean_ctor_get(x_7, 0);
lean_dec(x_164);
lean_ctor_set(x_7, 4, x_120);
lean_ctor_set(x_7, 3, x_158);
lean_ctor_set(x_7, 2, x_118);
lean_ctor_set(x_7, 1, x_117);
lean_ctor_set(x_7, 0, x_156);
return x_7;
}
else
{
lean_object* x_165; 
lean_dec(x_7);
x_165 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_165, 0, x_156);
lean_ctor_set(x_165, 1, x_117);
lean_ctor_set(x_165, 2, x_118);
lean_ctor_set(x_165, 3, x_158);
lean_ctor_set(x_165, 4, x_120);
return x_165;
}
}
}
}
else
{
lean_object* x_166; 
x_166 = lean_ctor_get(x_113, 3);
lean_inc(x_166);
if (lean_obj_tag(x_166) == 0)
{
uint8_t x_167; 
x_167 = !lean_is_exclusive(x_113);
if (x_167 == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; uint8_t x_171; 
x_168 = lean_ctor_get(x_113, 4);
x_169 = lean_ctor_get(x_113, 3);
lean_dec(x_169);
x_170 = lean_ctor_get(x_113, 0);
lean_dec(x_170);
x_171 = !lean_is_exclusive(x_166);
if (x_171 == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_172 = lean_ctor_get(x_166, 1);
x_173 = lean_ctor_get(x_166, 2);
x_174 = lean_ctor_get(x_166, 4);
lean_dec(x_174);
x_175 = lean_ctor_get(x_166, 3);
lean_dec(x_175);
x_176 = lean_ctor_get(x_166, 0);
lean_dec(x_176);
x_177 = lean_unsigned_to_nat(3u);
lean_inc_n(x_168, 2);
lean_ctor_set(x_166, 4, x_168);
lean_ctor_set(x_166, 3, x_168);
lean_ctor_set(x_166, 2, x_6);
lean_ctor_set(x_166, 1, x_5);
lean_ctor_set(x_166, 0, x_114);
lean_inc(x_168);
lean_ctor_set(x_113, 3, x_168);
lean_ctor_set(x_113, 0, x_114);
if (lean_is_scalar(x_9)) {
 x_178 = lean_alloc_ctor(0, 5, 0);
} else {
 x_178 = x_9;
}
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set(x_178, 1, x_172);
lean_ctor_set(x_178, 2, x_173);
lean_ctor_set(x_178, 3, x_166);
lean_ctor_set(x_178, 4, x_113);
return x_178;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_179 = lean_ctor_get(x_166, 1);
x_180 = lean_ctor_get(x_166, 2);
lean_inc(x_180);
lean_inc(x_179);
lean_dec(x_166);
x_181 = lean_unsigned_to_nat(3u);
lean_inc_n(x_168, 2);
x_182 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_182, 0, x_114);
lean_ctor_set(x_182, 1, x_5);
lean_ctor_set(x_182, 2, x_6);
lean_ctor_set(x_182, 3, x_168);
lean_ctor_set(x_182, 4, x_168);
lean_inc(x_168);
lean_ctor_set(x_113, 3, x_168);
lean_ctor_set(x_113, 0, x_114);
if (lean_is_scalar(x_9)) {
 x_183 = lean_alloc_ctor(0, 5, 0);
} else {
 x_183 = x_9;
}
lean_ctor_set(x_183, 0, x_181);
lean_ctor_set(x_183, 1, x_179);
lean_ctor_set(x_183, 2, x_180);
lean_ctor_set(x_183, 3, x_182);
lean_ctor_set(x_183, 4, x_113);
return x_183;
}
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_184 = lean_ctor_get(x_113, 4);
x_185 = lean_ctor_get(x_113, 1);
x_186 = lean_ctor_get(x_113, 2);
lean_inc(x_184);
lean_inc(x_186);
lean_inc(x_185);
lean_dec(x_113);
x_187 = lean_ctor_get(x_166, 1);
lean_inc(x_187);
x_188 = lean_ctor_get(x_166, 2);
lean_inc(x_188);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 lean_ctor_release(x_166, 1);
 lean_ctor_release(x_166, 2);
 lean_ctor_release(x_166, 3);
 lean_ctor_release(x_166, 4);
 x_189 = x_166;
} else {
 lean_dec_ref(x_166);
 x_189 = lean_box(0);
}
x_190 = lean_unsigned_to_nat(3u);
lean_inc_n(x_184, 2);
if (lean_is_scalar(x_189)) {
 x_191 = lean_alloc_ctor(0, 5, 0);
} else {
 x_191 = x_189;
}
lean_ctor_set(x_191, 0, x_114);
lean_ctor_set(x_191, 1, x_5);
lean_ctor_set(x_191, 2, x_6);
lean_ctor_set(x_191, 3, x_184);
lean_ctor_set(x_191, 4, x_184);
lean_inc(x_184);
x_192 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_192, 0, x_114);
lean_ctor_set(x_192, 1, x_185);
lean_ctor_set(x_192, 2, x_186);
lean_ctor_set(x_192, 3, x_184);
lean_ctor_set(x_192, 4, x_184);
if (lean_is_scalar(x_9)) {
 x_193 = lean_alloc_ctor(0, 5, 0);
} else {
 x_193 = x_9;
}
lean_ctor_set(x_193, 0, x_190);
lean_ctor_set(x_193, 1, x_187);
lean_ctor_set(x_193, 2, x_188);
lean_ctor_set(x_193, 3, x_191);
lean_ctor_set(x_193, 4, x_192);
return x_193;
}
}
else
{
lean_object* x_194; 
x_194 = lean_ctor_get(x_113, 4);
lean_inc(x_194);
if (lean_obj_tag(x_194) == 0)
{
uint8_t x_195; 
x_195 = !lean_is_exclusive(x_113);
if (x_195 == 0)
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_196 = lean_ctor_get(x_113, 1);
x_197 = lean_ctor_get(x_113, 2);
x_198 = lean_ctor_get(x_113, 4);
lean_dec(x_198);
x_199 = lean_ctor_get(x_113, 3);
lean_dec(x_199);
x_200 = lean_ctor_get(x_113, 0);
lean_dec(x_200);
x_201 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_113, 4, x_166);
lean_ctor_set(x_113, 2, x_6);
lean_ctor_set(x_113, 1, x_5);
lean_ctor_set(x_113, 0, x_114);
if (lean_is_scalar(x_9)) {
 x_202 = lean_alloc_ctor(0, 5, 0);
} else {
 x_202 = x_9;
}
lean_ctor_set(x_202, 0, x_201);
lean_ctor_set(x_202, 1, x_196);
lean_ctor_set(x_202, 2, x_197);
lean_ctor_set(x_202, 3, x_113);
lean_ctor_set(x_202, 4, x_194);
return x_202;
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_203 = lean_ctor_get(x_113, 1);
x_204 = lean_ctor_get(x_113, 2);
lean_inc(x_204);
lean_inc(x_203);
lean_dec(x_113);
x_205 = lean_unsigned_to_nat(3u);
x_206 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_206, 0, x_114);
lean_ctor_set(x_206, 1, x_5);
lean_ctor_set(x_206, 2, x_6);
lean_ctor_set(x_206, 3, x_166);
lean_ctor_set(x_206, 4, x_166);
if (lean_is_scalar(x_9)) {
 x_207 = lean_alloc_ctor(0, 5, 0);
} else {
 x_207 = x_9;
}
lean_ctor_set(x_207, 0, x_205);
lean_ctor_set(x_207, 1, x_203);
lean_ctor_set(x_207, 2, x_204);
lean_ctor_set(x_207, 3, x_206);
lean_ctor_set(x_207, 4, x_194);
return x_207;
}
}
else
{
lean_object* x_208; lean_object* x_209; 
x_208 = lean_unsigned_to_nat(2u);
if (lean_is_scalar(x_9)) {
 x_209 = lean_alloc_ctor(0, 5, 0);
} else {
 x_209 = x_9;
}
lean_ctor_set(x_209, 0, x_208);
lean_ctor_set(x_209, 1, x_5);
lean_ctor_set(x_209, 2, x_6);
lean_ctor_set(x_209, 3, x_194);
lean_ctor_set(x_209, 4, x_113);
return x_209;
}
}
}
}
}
}
else
{
lean_object* x_210; lean_object* x_211; 
x_210 = lean_unsigned_to_nat(1u);
x_211 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_211, 0, x_210);
lean_ctor_set(x_211, 1, x_1);
lean_ctor_set(x_211, 2, x_2);
lean_ctor_set(x_211, 3, x_3);
lean_ctor_set(x_211, 4, x_3);
return x_211;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___Lean_Server_FileWorker_WorkerContext_initPendingServerRequest___at___Lean_Server_FileWorker_sendServerRequest___at___Lean_Server_FileWorker_sendUntypedServerRequest_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_DTreeMap_Internal_Impl_insert___at___Lean_Server_FileWorker_WorkerContext_initPendingServerRequest___at___Lean_Server_FileWorker_sendServerRequest___at___Lean_Server_FileWorker_sendUntypedServerRequest_spec__0_spec__0_spec__0___redArg(x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_WorkerContext_initPendingServerRequest___at___Lean_Server_FileWorker_sendServerRequest___at___Lean_Server_FileWorker_sendUntypedServerRequest_spec__0_spec__0___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_WorkerContext_initPendingServerRequest___at___Lean_Server_FileWorker_sendServerRequest___at___Lean_Server_FileWorker_sendUntypedServerRequest_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_4 = lean_io_promise_new(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_1, 5);
x_8 = lean_st_ref_take(x_7, x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_5);
x_11 = l_Std_DTreeMap_Internal_Impl_insert___at___Lean_Server_FileWorker_WorkerContext_initPendingServerRequest___at___Lean_Server_FileWorker_sendServerRequest___at___Lean_Server_FileWorker_sendUntypedServerRequest_spec__0_spec__0_spec__0___redArg(x_2, x_5, x_9);
x_12 = lean_st_ref_set(x_7, x_11, x_10);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
x_15 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_WorkerContext_initPendingServerRequest___at___Lean_Server_FileWorker_sendServerRequest___at___Lean_Server_FileWorker_sendUntypedServerRequest_spec__0_spec__0___redArg___lam__0___boxed), 1, 0);
x_16 = l_IO_Promise_result_x21___redArg(x_5);
lean_dec(x_5);
x_17 = l_Lean_Server_ServerTask_mapCheap___redArg(x_15, x_16);
lean_ctor_set(x_12, 0, x_17);
return x_12;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_dec(x_12);
x_19 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_WorkerContext_initPendingServerRequest___at___Lean_Server_FileWorker_sendServerRequest___at___Lean_Server_FileWorker_sendUntypedServerRequest_spec__0_spec__0___redArg___lam__0___boxed), 1, 0);
x_20 = l_IO_Promise_result_x21___redArg(x_5);
lean_dec(x_5);
x_21 = l_Lean_Server_ServerTask_mapCheap___redArg(x_19, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_18);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_WorkerContext_initPendingServerRequest___at___Lean_Server_FileWorker_sendServerRequest___at___Lean_Server_FileWorker_sendUntypedServerRequest_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_FileWorker_WorkerContext_initPendingServerRequest___at___Lean_Server_FileWorker_sendServerRequest___at___Lean_Server_FileWorker_sendUntypedServerRequest_spec__0_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_sendServerRequest___at___Lean_Server_FileWorker_sendUntypedServerRequest_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_29; 
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
x_7 = lean_st_ref_take(x_6, x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_to_int(x_10);
x_12 = lean_int_add(x_8, x_11);
lean_dec(x_11);
x_13 = lean_st_ref_set(x_6, x_12, x_9);
lean_dec(x_6);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Lean_JsonNumber_fromInt(x_8);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
lean_inc(x_16);
x_17 = l_Lean_Server_FileWorker_WorkerContext_initPendingServerRequest___at___Lean_Server_FileWorker_sendServerRequest___at___Lean_Server_FileWorker_sendUntypedServerRequest_spec__0_spec__0___redArg(x_2, x_16, x_14);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_2, 0);
lean_inc(x_20);
lean_dec(x_2);
x_29 = l_Lean_Json_toStructured_x3f___at___IO_FS_Stream_writeLspRequest___at___Lean_Lsp_Ipc_shutdown_spec__0_spec__0(x_4);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; 
lean_dec(x_29);
x_30 = lean_box(0);
x_21 = x_30;
goto block_28;
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_29);
if (x_31 == 0)
{
x_21 = x_29;
goto block_28;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_29, 0);
lean_inc(x_32);
lean_dec(x_29);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_21 = x_33;
goto block_28;
}
}
block_28:
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_22, 0, x_16);
lean_ctor_set(x_22, 1, x_3);
lean_ctor_set(x_22, 2, x_21);
x_23 = l_Std_Channel_Sync_send___redArg(x_20, x_22, x_19);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
lean_ctor_set(x_23, 0, x_18);
return x_23;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_18);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_sendUntypedServerRequest(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = l_Lean_Server_FileWorker_sendServerRequest___at___Lean_Server_FileWorker_sendUntypedServerRequest_spec__0(x_5, x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_WorkerContext_initPendingServerRequest___at___Lean_Server_FileWorker_sendServerRequest___at___Lean_Server_FileWorker_sendUntypedServerRequest_spec__0_spec__0___redArg___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Server_FileWorker_WorkerContext_initPendingServerRequest___at___Lean_Server_FileWorker_sendServerRequest___at___Lean_Server_FileWorker_sendUntypedServerRequest_spec__0_spec__0___redArg___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_WorkerContext_initPendingServerRequest___at___Lean_Server_FileWorker_sendServerRequest___at___Lean_Server_FileWorker_sendUntypedServerRequest_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_FileWorker_WorkerContext_initPendingServerRequest___at___Lean_Server_FileWorker_sendServerRequest___at___Lean_Server_FileWorker_sendUntypedServerRequest_spec__0_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_WorkerContext_initPendingServerRequest___at___Lean_Server_FileWorker_sendServerRequest___at___Lean_Server_FileWorker_sendUntypedServerRequest_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_FileWorker_WorkerContext_initPendingServerRequest___at___Lean_Server_FileWorker_sendServerRequest___at___Lean_Server_FileWorker_sendUntypedServerRequest_spec__0_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_sendServerRequest___at___Lean_Server_FileWorker_sendUntypedServerRequest_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Server_FileWorker_sendServerRequest___at___Lean_Server_FileWorker_sendUntypedServerRequest_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_updatePendingRequests___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
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
x_9 = lean_ctor_get(x_5, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_5, 3);
lean_inc(x_10);
x_11 = lean_apply_1(x_1, x_10);
x_12 = lean_ctor_get(x_5, 4);
lean_inc(x_12);
lean_dec(x_5);
x_13 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_9);
lean_ctor_set(x_13, 3, x_11);
lean_ctor_set(x_13, 4, x_12);
x_14 = lean_st_ref_set(x_2, x_13, x_6);
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
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_updatePendingRequests(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_FileWorker_updatePendingRequests___redArg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_updatePendingRequests___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_FileWorker_updatePendingRequests___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_updatePendingRequests___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_FileWorker_updatePendingRequests(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_updateDocument(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_IO_CancelToken_set(x_8, x_7);
lean_dec(x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_2, 8);
lean_inc(x_11);
lean_inc(x_1);
x_12 = l_Lean_Server_DocumentMeta_mkInputContext(x_1);
x_13 = lean_apply_2(x_11, x_12, x_10);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Array_empty(lean_box(0));
x_17 = lean_st_mk_ref(x_16, x_15);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_IO_CancelToken_new(x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_14);
x_23 = l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps(x_14);
lean_inc(x_1);
x_24 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_14);
lean_ctor_set(x_24, 2, x_23);
lean_ctor_set(x_24, 3, x_18);
lean_inc(x_21);
lean_inc(x_24);
lean_inc(x_2);
x_25 = l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_reportSnapshots(x_2, x_24, x_21, x_22);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_st_ref_take(x_3, x_27);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_ctor_get(x_28, 1);
lean_ctor_set(x_28, 1, x_26);
lean_ctor_set(x_28, 0, x_24);
x_32 = lean_ctor_get(x_30, 2);
lean_inc(x_32);
x_33 = lean_ctor_get(x_30, 3);
lean_inc(x_33);
x_34 = lean_ctor_get(x_30, 4);
lean_inc(x_34);
lean_dec(x_30);
x_35 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_35, 0, x_28);
lean_ctor_set(x_35, 1, x_21);
lean_ctor_set(x_35, 2, x_32);
lean_ctor_set(x_35, 3, x_33);
lean_ctor_set(x_35, 4, x_34);
x_36 = lean_st_ref_set(x_3, x_35, x_31);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = lean_ctor_get(x_2, 1);
lean_inc(x_38);
lean_dec(x_2);
x_39 = lean_ctor_get(x_1, 2);
lean_inc(x_39);
lean_dec(x_1);
x_40 = lean_nat_to_int(x_39);
x_41 = lean_st_ref_set(x_38, x_40, x_37);
lean_dec(x_38);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
return x_41;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_41, 0);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_41);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_46 = lean_ctor_get(x_28, 0);
x_47 = lean_ctor_get(x_28, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_28);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_24);
lean_ctor_set(x_48, 1, x_26);
x_49 = lean_ctor_get(x_46, 2);
lean_inc(x_49);
x_50 = lean_ctor_get(x_46, 3);
lean_inc(x_50);
x_51 = lean_ctor_get(x_46, 4);
lean_inc(x_51);
lean_dec(x_46);
x_52 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_52, 0, x_48);
lean_ctor_set(x_52, 1, x_21);
lean_ctor_set(x_52, 2, x_49);
lean_ctor_set(x_52, 3, x_50);
lean_ctor_set(x_52, 4, x_51);
x_53 = lean_st_ref_set(x_3, x_52, x_47);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec(x_53);
x_55 = lean_ctor_get(x_2, 1);
lean_inc(x_55);
lean_dec(x_2);
x_56 = lean_ctor_get(x_1, 2);
lean_inc(x_56);
lean_dec(x_1);
x_57 = lean_nat_to_int(x_56);
x_58 = lean_st_ref_set(x_55, x_57, x_54);
lean_dec(x_55);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_61 = x_58;
} else {
 lean_dec_ref(x_58);
 x_61 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_updateDocument___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_FileWorker_updateDocument(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at___Lean_Server_FileWorker_handleDidChange_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_2);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 2);
x_8 = lean_ctor_get(x_1, 3);
x_9 = l_Lean_RBNode_forIn_visit___at___Lean_Server_FileWorker_handleDidChange_spec__0___redArg(x_6, x_2, x_3);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_7, 1);
x_12 = l_Lean_Server_RequestCancellationToken_cancelByEdit(x_11, x_10);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_box(0);
x_1 = x_8;
x_2 = x_14;
x_3 = x_13;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at___Lean_Server_FileWorker_handleDidChange_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_RBNode_forIn_visit___at___Lean_Server_FileWorker_handleDidChange_spec__0___redArg(x_1, x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleDidChange(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_70; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_st_ref_get(x_3, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Server_RequestCancellationToken_new(x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_9, 0);
lean_inc(x_16);
lean_dec(x_9);
x_70 = lean_ctor_get(x_14, 1);
lean_inc(x_70);
lean_dec(x_14);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; 
x_71 = lean_unsigned_to_nat(0u);
x_17 = x_71;
goto block_69;
}
else
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_70, 0);
lean_inc(x_72);
lean_dec(x_70);
x_17 = x_72;
goto block_69;
}
block_69:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_6, 4);
lean_inc(x_18);
x_19 = lean_ctor_get(x_2, 6);
lean_inc(x_19);
x_20 = lean_ctor_get(x_2, 7);
lean_inc(x_20);
lean_inc(x_2);
x_21 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_sendUntypedServerRequest), 4, 1);
lean_closure_set(x_21, 0, x_2);
lean_inc(x_16);
x_22 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_22, 0, x_18);
lean_ctor_set(x_22, 1, x_16);
lean_ctor_set(x_22, 2, x_19);
lean_ctor_set(x_22, 3, x_20);
lean_ctor_set(x_22, 4, x_12);
lean_ctor_set(x_22, 5, x_21);
x_23 = lean_alloc_closure((void*)(l_Lean_Server_handleOnDidChange), 3, 1);
lean_closure_set(x_23, 0, x_1);
x_24 = l_Lean_Server_RequestM_runInIO(lean_box(0), x_23, x_22, x_13);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_29; 
x_26 = lean_ctor_get(x_24, 1);
x_27 = lean_ctor_get(x_24, 0);
lean_dec(x_27);
x_28 = l_Array_isEmpty___redArg(x_15);
x_29 = l_instDecidableNot___redArg(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_2);
x_30 = lean_box(0);
lean_ctor_set(x_24, 0, x_30);
return x_24;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
lean_free_object(x_24);
x_31 = lean_ctor_get(x_16, 0);
lean_inc(x_31);
lean_dec(x_16);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_ctor_get(x_32, 3);
lean_inc(x_33);
x_34 = l_Lean_Server_foldDocumentChanges(x_15, x_33);
lean_dec(x_15);
x_35 = lean_ctor_get(x_32, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_32, 1);
lean_inc(x_36);
x_37 = lean_ctor_get_uint8(x_32, sizeof(void*)*4);
lean_dec(x_32);
x_38 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_36);
lean_ctor_set(x_38, 2, x_17);
lean_ctor_set(x_38, 3, x_34);
lean_ctor_set_uint8(x_38, sizeof(void*)*4, x_37);
x_39 = l_Lean_Server_FileWorker_updateDocument(x_38, x_2, x_3, x_26);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
x_41 = lean_ctor_get(x_6, 3);
lean_inc(x_41);
lean_dec(x_6);
x_42 = lean_box(0);
x_43 = l_Lean_RBNode_forIn_visit___at___Lean_Server_FileWorker_handleDidChange_spec__0___redArg(x_41, x_42, x_40);
lean_dec(x_41);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_43, 0);
lean_dec(x_45);
lean_ctor_set(x_43, 0, x_42);
return x_43;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_dec(x_43);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_42);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
lean_object* x_48; uint8_t x_49; uint8_t x_50; 
x_48 = lean_ctor_get(x_24, 1);
lean_inc(x_48);
lean_dec(x_24);
x_49 = l_Array_isEmpty___redArg(x_15);
x_50 = l_instDecidableNot___redArg(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_2);
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_48);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_53 = lean_ctor_get(x_16, 0);
lean_inc(x_53);
lean_dec(x_16);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
lean_dec(x_53);
x_55 = lean_ctor_get(x_54, 3);
lean_inc(x_55);
x_56 = l_Lean_Server_foldDocumentChanges(x_15, x_55);
lean_dec(x_15);
x_57 = lean_ctor_get(x_54, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_54, 1);
lean_inc(x_58);
x_59 = lean_ctor_get_uint8(x_54, sizeof(void*)*4);
lean_dec(x_54);
x_60 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_58);
lean_ctor_set(x_60, 2, x_17);
lean_ctor_set(x_60, 3, x_56);
lean_ctor_set_uint8(x_60, sizeof(void*)*4, x_59);
x_61 = l_Lean_Server_FileWorker_updateDocument(x_60, x_2, x_3, x_48);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
lean_dec(x_61);
x_63 = lean_ctor_get(x_6, 3);
lean_inc(x_63);
lean_dec(x_6);
x_64 = lean_box(0);
x_65 = l_Lean_RBNode_forIn_visit___at___Lean_Server_FileWorker_handleDidChange_spec__0___redArg(x_63, x_64, x_62);
lean_dec(x_63);
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_67 = x_65;
} else {
 lean_dec_ref(x_65);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_64);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
}
}
else
{
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_2);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at___Lean_Server_FileWorker_handleDidChange_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_forIn_visit___at___Lean_Server_FileWorker_handleDidChange_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at___Lean_Server_FileWorker_handleDidChange_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_RBNode_forIn_visit___at___Lean_Server_FileWorker_handleDidChange_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleDidChange___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_FileWorker_handleDidChange(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at___Lean_Server_FileWorker_handleCancelRequest_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
lean_dec(x_2);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
lean_dec(x_1);
lean_inc(x_2);
x_8 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_ordRequestID____x40_Lean_Data_JsonRpc___hyg_126_(x_2, x_5);
switch (x_8) {
case 0:
{
lean_dec(x_7);
lean_dec(x_6);
x_1 = x_4;
goto _start;
}
case 1:
{
lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_6);
return x_10;
}
default: 
{
lean_dec(x_6);
lean_dec(x_4);
x_1 = x_7;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at___Lean_Server_FileWorker_handleCancelRequest_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_find___at___Lean_Server_FileWorker_handleCancelRequest_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_Server_FileWorker_handleCancelRequest_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_ctor_get(x_2, 3);
lean_inc(x_5);
lean_inc(x_1);
x_8 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_ordRequestID____x40_Lean_Data_JsonRpc___hyg_126_(x_1, x_5);
switch (x_8) {
case 0:
{
uint8_t x_9; 
x_9 = l_Lean_RBNode_isBlack___redArg(x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_box(0);
x_11 = l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_Server_FileWorker_handleCancelRequest_spec__1_spec__1___redArg(x_1, x_4);
lean_ctor_set(x_2, 0, x_11);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_12);
return x_2;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_free_object(x_2);
x_13 = l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_Server_FileWorker_handleCancelRequest_spec__1_spec__1___redArg(x_1, x_4);
x_14 = l_Lean_RBNode_balLeft___redArg(x_13, x_5, x_6, x_7);
return x_14;
}
}
case 1:
{
lean_object* x_15; 
lean_free_object(x_2);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_15 = l_Lean_RBNode_appendTrees___redArg(x_4, x_7);
return x_15;
}
default: 
{
uint8_t x_16; 
x_16 = l_Lean_RBNode_isBlack___redArg(x_7);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_box(0);
x_18 = l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_Server_FileWorker_handleCancelRequest_spec__1_spec__1___redArg(x_1, x_7);
lean_ctor_set(x_2, 3, x_18);
x_19 = lean_unbox(x_17);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_19);
return x_2;
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_free_object(x_2);
x_20 = l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_Server_FileWorker_handleCancelRequest_spec__1_spec__1___redArg(x_1, x_7);
x_21 = l_Lean_RBNode_balRight(lean_box(0), lean_box(0), x_4, x_5, x_6, x_20);
return x_21;
}
}
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_22 = lean_ctor_get(x_2, 0);
x_23 = lean_ctor_get(x_2, 1);
x_24 = lean_ctor_get(x_2, 2);
x_25 = lean_ctor_get(x_2, 3);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_2);
lean_inc(x_23);
lean_inc(x_1);
x_26 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_ordRequestID____x40_Lean_Data_JsonRpc___hyg_126_(x_1, x_23);
switch (x_26) {
case 0:
{
uint8_t x_27; 
x_27 = l_Lean_RBNode_isBlack___redArg(x_22);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_box(0);
x_29 = l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_Server_FileWorker_handleCancelRequest_spec__1_spec__1___redArg(x_1, x_22);
x_30 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_23);
lean_ctor_set(x_30, 2, x_24);
lean_ctor_set(x_30, 3, x_25);
x_31 = lean_unbox(x_28);
lean_ctor_set_uint8(x_30, sizeof(void*)*4, x_31);
return x_30;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_Server_FileWorker_handleCancelRequest_spec__1_spec__1___redArg(x_1, x_22);
x_33 = l_Lean_RBNode_balLeft___redArg(x_32, x_23, x_24, x_25);
return x_33;
}
}
case 1:
{
lean_object* x_34; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_1);
x_34 = l_Lean_RBNode_appendTrees___redArg(x_22, x_25);
return x_34;
}
default: 
{
uint8_t x_35; 
x_35 = l_Lean_RBNode_isBlack___redArg(x_25);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_36 = lean_box(0);
x_37 = l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_Server_FileWorker_handleCancelRequest_spec__1_spec__1___redArg(x_1, x_25);
x_38 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_38, 0, x_22);
lean_ctor_set(x_38, 1, x_23);
lean_ctor_set(x_38, 2, x_24);
lean_ctor_set(x_38, 3, x_37);
x_39 = lean_unbox(x_36);
lean_ctor_set_uint8(x_38, sizeof(void*)*4, x_39);
return x_38;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_Server_FileWorker_handleCancelRequest_spec__1_spec__1___redArg(x_1, x_25);
x_41 = l_Lean_RBNode_balRight(lean_box(0), lean_box(0), x_22, x_23, x_24, x_40);
return x_41;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_Server_FileWorker_handleCancelRequest_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_Server_FileWorker_handleCancelRequest_spec__1_spec__1___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___at___Lean_Server_FileWorker_handleCancelRequest_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_Server_FileWorker_handleCancelRequest_spec__1_spec__1___redArg(x_1, x_2);
x_4 = l_Lean_RBNode_setBlack___redArg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___at___Lean_Server_FileWorker_handleCancelRequest_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_erase___at___Lean_Server_FileWorker_handleCancelRequest_spec__1___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleCancelRequest___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_ctor_get(x_6, 3);
lean_inc(x_8);
lean_inc(x_1);
lean_inc(x_8);
x_9 = l_Lean_RBNode_find___at___Lean_Server_FileWorker_handleCancelRequest_spec__0___redArg(x_8, x_1);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_10 = lean_box(0);
lean_ctor_set(x_4, 0, x_10);
return x_4;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
lean_free_object(x_4);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_Server_RequestCancellationToken_cancelByCancelRequest(x_12, x_7);
lean_dec(x_12);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get(x_6, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_6, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_6, 2);
lean_inc(x_17);
x_18 = l_Lean_RBNode_erase___at___Lean_Server_FileWorker_handleCancelRequest_spec__1___redArg(x_1, x_8);
x_19 = lean_ctor_get(x_6, 4);
lean_inc(x_19);
lean_dec(x_6);
x_20 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_20, 1, x_16);
lean_ctor_set(x_20, 2, x_17);
lean_ctor_set(x_20, 3, x_18);
lean_ctor_set(x_20, 4, x_19);
x_21 = lean_st_ref_set(x_2, x_20, x_14);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
return x_21;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_21);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_4, 0);
x_27 = lean_ctor_get(x_4, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_4);
x_28 = lean_ctor_get(x_26, 3);
lean_inc(x_28);
lean_inc(x_1);
lean_inc(x_28);
x_29 = l_Lean_RBNode_find___at___Lean_Server_FileWorker_handleCancelRequest_spec__0___redArg(x_28, x_1);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_1);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_27);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_32 = lean_ctor_get(x_29, 0);
lean_inc(x_32);
lean_dec(x_29);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = l_Lean_Server_RequestCancellationToken_cancelByCancelRequest(x_33, x_27);
lean_dec(x_33);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_ctor_get(x_26, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_26, 1);
lean_inc(x_37);
x_38 = lean_ctor_get(x_26, 2);
lean_inc(x_38);
x_39 = l_Lean_RBNode_erase___at___Lean_Server_FileWorker_handleCancelRequest_spec__1___redArg(x_1, x_28);
x_40 = lean_ctor_get(x_26, 4);
lean_inc(x_40);
lean_dec(x_26);
x_41 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_41, 0, x_36);
lean_ctor_set(x_41, 1, x_37);
lean_ctor_set(x_41, 2, x_38);
lean_ctor_set(x_41, 3, x_39);
lean_ctor_set(x_41, 4, x_40);
x_42 = lean_st_ref_set(x_2, x_41, x_35);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_45 = x_42;
} else {
 lean_dec_ref(x_42);
 x_45 = lean_box(0);
}
if (lean_is_scalar(x_45)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_45;
}
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleCancelRequest(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_FileWorker_handleCancelRequest___redArg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleCancelRequest___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_FileWorker_handleCancelRequest___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleCancelRequest___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_FileWorker_handleCancelRequest(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Server_FileWorker_handleStaleDependency_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_2, x_3);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_12 = lean_mk_string_unchecked("Imports are out of date and should be rebuilt; use the \"Restart File\" command in your editor.", 93, 93);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_array_uget(x_1, x_2);
x_15 = lean_ctor_get(x_14, 6);
lean_inc(x_15);
x_16 = l_Lean_Widget_TaggedText_stripTags___redArg(x_15);
x_17 = l_Lean_Widget_TaggedText_stripTags___redArg(x_13);
x_18 = lean_string_dec_eq(x_16, x_17);
lean_dec(x_17);
lean_dec(x_16);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_array_push(x_4, x_14);
x_5 = x_19;
goto block_10;
}
else
{
lean_dec(x_14);
x_5 = x_4;
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
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleStaleDependency___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 3);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_mk_string_unchecked("Imports are out of date and should be rebuilt; use the \"Restart File\" command in your editor.", 93, 93);
x_13 = lean_unsigned_to_nat(0u);
lean_ctor_set(x_4, 1, x_13);
lean_ctor_set(x_4, 0, x_13);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
x_17 = lean_string_utf8_byte_size(x_16);
lean_dec(x_16);
x_18 = l_Lean_FileMap_utf8PosToLspPos(x_11, x_17);
lean_dec(x_17);
lean_inc(x_4);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_4);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_box(2);
x_21 = lean_ctor_get(x_1, 3);
lean_inc(x_21);
x_22 = lean_st_ref_take(x_21, x_7);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_12);
lean_ctor_set(x_22, 1, x_15);
lean_ctor_set(x_22, 0, x_4);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_19);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_20);
x_38 = lean_box(0);
x_39 = lean_box(0);
x_40 = lean_box(0);
x_41 = lean_box(0);
x_42 = lean_box(0);
x_43 = lean_box(0);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_45, 0, x_22);
lean_ctor_set(x_45, 1, x_36);
lean_ctor_set(x_45, 2, x_37);
lean_ctor_set(x_45, 3, x_38);
lean_ctor_set(x_45, 4, x_39);
lean_ctor_set(x_45, 5, x_40);
lean_ctor_set(x_45, 6, x_35);
lean_ctor_set(x_45, 7, x_41);
lean_ctor_set(x_45, 8, x_42);
lean_ctor_set(x_45, 9, x_43);
lean_ctor_set(x_45, 10, x_44);
x_46 = lean_array_get_size(x_24);
x_47 = lean_mk_empty_array_with_capacity(x_13);
x_48 = lean_nat_dec_lt(x_13, x_46);
if (x_48 == 0)
{
lean_object* x_49; 
lean_dec(x_46);
lean_dec(x_24);
x_49 = lean_array_push(x_47, x_45);
x_26 = x_49;
goto block_34;
}
else
{
uint8_t x_50; 
x_50 = lean_nat_dec_le(x_46, x_46);
if (x_50 == 0)
{
lean_object* x_51; 
lean_dec(x_46);
lean_dec(x_24);
x_51 = lean_array_push(x_47, x_45);
x_26 = x_51;
goto block_34;
}
else
{
size_t x_52; size_t x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_usize_of_nat(x_13);
x_53 = lean_usize_of_nat(x_46);
lean_dec(x_46);
x_54 = l_Array_foldlMUnsafe_fold___at___Lean_Server_FileWorker_handleStaleDependency_spec__0(x_24, x_52, x_53, x_47);
lean_dec(x_24);
x_55 = lean_array_push(x_54, x_45);
x_26 = x_55;
goto block_34;
}
}
block_34:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_st_ref_set(x_21, x_26, x_25);
lean_dec(x_21);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_publishDiagnostics(x_1, x_9, x_28);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
return x_29;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_29);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_56 = lean_ctor_get(x_22, 0);
x_57 = lean_ctor_get(x_22, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_22);
x_67 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_67, 0, x_12);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_4);
lean_ctor_set(x_68, 1, x_15);
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_19);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_20);
x_71 = lean_box(0);
x_72 = lean_box(0);
x_73 = lean_box(0);
x_74 = lean_box(0);
x_75 = lean_box(0);
x_76 = lean_box(0);
x_77 = lean_box(0);
x_78 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_78, 0, x_68);
lean_ctor_set(x_78, 1, x_69);
lean_ctor_set(x_78, 2, x_70);
lean_ctor_set(x_78, 3, x_71);
lean_ctor_set(x_78, 4, x_72);
lean_ctor_set(x_78, 5, x_73);
lean_ctor_set(x_78, 6, x_67);
lean_ctor_set(x_78, 7, x_74);
lean_ctor_set(x_78, 8, x_75);
lean_ctor_set(x_78, 9, x_76);
lean_ctor_set(x_78, 10, x_77);
x_79 = lean_array_get_size(x_56);
x_80 = lean_mk_empty_array_with_capacity(x_13);
x_81 = lean_nat_dec_lt(x_13, x_79);
if (x_81 == 0)
{
lean_object* x_82; 
lean_dec(x_79);
lean_dec(x_56);
x_82 = lean_array_push(x_80, x_78);
x_58 = x_82;
goto block_66;
}
else
{
uint8_t x_83; 
x_83 = lean_nat_dec_le(x_79, x_79);
if (x_83 == 0)
{
lean_object* x_84; 
lean_dec(x_79);
lean_dec(x_56);
x_84 = lean_array_push(x_80, x_78);
x_58 = x_84;
goto block_66;
}
else
{
size_t x_85; size_t x_86; lean_object* x_87; lean_object* x_88; 
x_85 = lean_usize_of_nat(x_13);
x_86 = lean_usize_of_nat(x_79);
lean_dec(x_79);
x_87 = l_Array_foldlMUnsafe_fold___at___Lean_Server_FileWorker_handleStaleDependency_spec__0(x_56, x_85, x_86, x_80);
lean_dec(x_56);
x_88 = lean_array_push(x_87, x_78);
x_58 = x_88;
goto block_66;
}
}
block_66:
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_59 = lean_st_ref_set(x_21, x_58, x_57);
lean_dec(x_21);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
lean_dec(x_59);
x_61 = l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_publishDiagnostics(x_1, x_9, x_60);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_64 = x_61;
} else {
 lean_dec_ref(x_61);
 x_64 = lean_box(0);
}
if (lean_is_scalar(x_64)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_64;
}
lean_ctor_set(x_65, 0, x_62);
lean_ctor_set(x_65, 1, x_63);
return x_65;
}
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; 
x_89 = lean_ctor_get(x_4, 0);
x_90 = lean_ctor_get(x_4, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_4);
x_91 = lean_ctor_get(x_89, 0);
lean_inc(x_91);
lean_dec(x_89);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
lean_dec(x_91);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_93, 3);
lean_inc(x_94);
lean_dec(x_93);
x_95 = lean_mk_string_unchecked("Imports are out of date and should be rebuilt; use the \"Restart File\" command in your editor.", 93, 93);
x_96 = lean_unsigned_to_nat(0u);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_96);
x_98 = lean_unsigned_to_nat(1u);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_96);
x_100 = lean_ctor_get(x_94, 0);
lean_inc(x_100);
x_101 = lean_string_utf8_byte_size(x_100);
lean_dec(x_100);
x_102 = l_Lean_FileMap_utf8PosToLspPos(x_94, x_101);
lean_dec(x_101);
lean_inc(x_97);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_97);
lean_ctor_set(x_103, 1, x_102);
x_104 = lean_box(2);
x_105 = lean_ctor_get(x_1, 3);
lean_inc(x_105);
x_106 = lean_st_ref_take(x_105, x_90);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_109 = x_106;
} else {
 lean_dec_ref(x_106);
 x_109 = lean_box(0);
}
x_119 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_119, 0, x_95);
if (lean_is_scalar(x_109)) {
 x_120 = lean_alloc_ctor(0, 2, 0);
} else {
 x_120 = x_109;
}
lean_ctor_set(x_120, 0, x_97);
lean_ctor_set(x_120, 1, x_99);
x_121 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_121, 0, x_103);
x_122 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_122, 0, x_104);
x_123 = lean_box(0);
x_124 = lean_box(0);
x_125 = lean_box(0);
x_126 = lean_box(0);
x_127 = lean_box(0);
x_128 = lean_box(0);
x_129 = lean_box(0);
x_130 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_130, 0, x_120);
lean_ctor_set(x_130, 1, x_121);
lean_ctor_set(x_130, 2, x_122);
lean_ctor_set(x_130, 3, x_123);
lean_ctor_set(x_130, 4, x_124);
lean_ctor_set(x_130, 5, x_125);
lean_ctor_set(x_130, 6, x_119);
lean_ctor_set(x_130, 7, x_126);
lean_ctor_set(x_130, 8, x_127);
lean_ctor_set(x_130, 9, x_128);
lean_ctor_set(x_130, 10, x_129);
x_131 = lean_array_get_size(x_107);
x_132 = lean_mk_empty_array_with_capacity(x_96);
x_133 = lean_nat_dec_lt(x_96, x_131);
if (x_133 == 0)
{
lean_object* x_134; 
lean_dec(x_131);
lean_dec(x_107);
x_134 = lean_array_push(x_132, x_130);
x_110 = x_134;
goto block_118;
}
else
{
uint8_t x_135; 
x_135 = lean_nat_dec_le(x_131, x_131);
if (x_135 == 0)
{
lean_object* x_136; 
lean_dec(x_131);
lean_dec(x_107);
x_136 = lean_array_push(x_132, x_130);
x_110 = x_136;
goto block_118;
}
else
{
size_t x_137; size_t x_138; lean_object* x_139; lean_object* x_140; 
x_137 = lean_usize_of_nat(x_96);
x_138 = lean_usize_of_nat(x_131);
lean_dec(x_131);
x_139 = l_Array_foldlMUnsafe_fold___at___Lean_Server_FileWorker_handleStaleDependency_spec__0(x_107, x_137, x_138, x_132);
lean_dec(x_107);
x_140 = lean_array_push(x_139, x_130);
x_110 = x_140;
goto block_118;
}
}
block_118:
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_111 = lean_st_ref_set(x_105, x_110, x_108);
lean_dec(x_105);
x_112 = lean_ctor_get(x_111, 1);
lean_inc(x_112);
lean_dec(x_111);
x_113 = l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_publishDiagnostics(x_1, x_92, x_112);
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_116 = x_113;
} else {
 lean_dec_ref(x_113);
 x_116 = lean_box(0);
}
if (lean_is_scalar(x_116)) {
 x_117 = lean_alloc_ctor(0, 2, 0);
} else {
 x_117 = x_116;
}
lean_ctor_set(x_117, 0, x_114);
lean_ctor_set(x_117, 1, x_115);
return x_117;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleStaleDependency(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_FileWorker_handleStaleDependency___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Server_FileWorker_handleStaleDependency_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Lean_Server_FileWorker_handleStaleDependency_spec__0(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleStaleDependency___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_FileWorker_handleStaleDependency___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleStaleDependency___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_FileWorker_handleStaleDependency(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleRpcRelease_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_3, x_2);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
lean_object* x_8; size_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; 
lean_dec(x_4);
x_8 = lean_array_uget(x_1, x_3);
x_9 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_10 = l_Lean_Server_rpcReleaseRef(x_9, x_5);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_box(0);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_usize_of_nat(x_13);
x_15 = lean_usize_add(x_3, x_14);
x_3 = x_15;
x_4 = x_12;
x_5 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleRpcRelease___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_ctor_get(x_6, 4);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_10 = l_Lean_RBNode_find___at___Lean_Server_wrapRpcProcedure___at___Lean_Server_registerBuiltinRpcProcedure___at___Lean_Widget_initFn____x40_Lean_Server_FileWorker_WidgetRequests___hyg_394__spec__0_spec__0_spec__0___redArg(x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_box(0);
lean_ctor_set(x_4, 0, x_11);
return x_4;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; lean_object* x_24; size_t x_25; lean_object* x_26; uint8_t x_27; 
lean_free_object(x_4);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_io_mono_ms_now(x_7);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_st_ref_take(x_12, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_1, 1);
x_20 = lean_box(0);
x_21 = l_Lean_Server_FileWorker_RpcSession_keptAlive(x_14, x_17);
lean_dec(x_17);
lean_dec(x_14);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_array_size(x_19);
x_24 = lean_unsigned_to_nat(0u);
x_25 = lean_usize_of_nat(x_24);
x_26 = l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleRpcRelease_spec__0(x_19, x_23, x_25, x_20, x_22);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_28 = lean_ctor_get(x_26, 1);
x_29 = lean_ctor_get(x_26, 0);
lean_dec(x_29);
x_30 = lean_ctor_get(x_21, 1);
lean_inc(x_30);
lean_dec(x_21);
lean_ctor_set(x_26, 1, x_30);
lean_ctor_set(x_26, 0, x_28);
x_31 = lean_st_ref_set(x_12, x_26, x_18);
lean_dec(x_12);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
return x_31;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_31);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_36 = lean_ctor_get(x_26, 1);
lean_inc(x_36);
lean_dec(x_26);
x_37 = lean_ctor_get(x_21, 1);
lean_inc(x_37);
lean_dec(x_21);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_st_ref_set(x_12, x_38, x_18);
lean_dec(x_12);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_42 = x_39;
} else {
 lean_dec_ref(x_39);
 x_42 = lean_box(0);
}
if (lean_is_scalar(x_42)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_42;
}
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint64_t x_47; lean_object* x_48; 
x_44 = lean_ctor_get(x_4, 0);
x_45 = lean_ctor_get(x_4, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_4);
x_46 = lean_ctor_get(x_44, 4);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_48 = l_Lean_RBNode_find___at___Lean_Server_wrapRpcProcedure___at___Lean_Server_registerBuiltinRpcProcedure___at___Lean_Widget_initFn____x40_Lean_Server_FileWorker_WidgetRequests___hyg_394__spec__0_spec__0_spec__0___redArg(x_46, x_47);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_45);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; size_t x_62; lean_object* x_63; size_t x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_51 = lean_ctor_get(x_48, 0);
lean_inc(x_51);
lean_dec(x_48);
x_52 = lean_io_mono_ms_now(x_45);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_st_ref_take(x_51, x_54);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = lean_ctor_get(x_1, 1);
x_59 = lean_box(0);
x_60 = l_Lean_Server_FileWorker_RpcSession_keptAlive(x_53, x_56);
lean_dec(x_56);
lean_dec(x_53);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_array_size(x_58);
x_63 = lean_unsigned_to_nat(0u);
x_64 = lean_usize_of_nat(x_63);
x_65 = l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleRpcRelease_spec__0(x_58, x_62, x_64, x_59, x_61);
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_67 = x_65;
} else {
 lean_dec_ref(x_65);
 x_67 = lean_box(0);
}
x_68 = lean_ctor_get(x_60, 1);
lean_inc(x_68);
lean_dec(x_60);
if (lean_is_scalar(x_67)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_67;
}
lean_ctor_set(x_69, 0, x_66);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_st_ref_set(x_51, x_69, x_57);
lean_dec(x_51);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_73 = x_70;
} else {
 lean_dec_ref(x_70);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_71);
lean_ctor_set(x_74, 1, x_72);
return x_74;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleRpcRelease(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_FileWorker_handleRpcRelease___redArg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleRpcRelease_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_handleRpcRelease_spec__0(x_1, x_6, x_7, x_4, x_5);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleRpcRelease___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_FileWorker_handleRpcRelease___redArg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleRpcRelease___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_FileWorker_handleRpcRelease(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleRpcKeepAlive___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_ctor_get(x_6, 4);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
x_10 = l_Lean_RBNode_find___at___Lean_Server_wrapRpcProcedure___at___Lean_Server_registerBuiltinRpcProcedure___at___Lean_Widget_initFn____x40_Lean_Server_FileWorker_WidgetRequests___hyg_394__spec__0_spec__0_spec__0___redArg(x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_box(0);
lean_ctor_set(x_4, 0, x_11);
return x_4;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_free_object(x_4);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_io_mono_ms_now(x_7);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_st_ref_take(x_12, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Server_FileWorker_RpcSession_keptAlive(x_14, x_17);
lean_dec(x_17);
lean_dec(x_14);
x_20 = lean_st_ref_set(x_12, x_19, x_18);
lean_dec(x_12);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
return x_20;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint64_t x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_4, 0);
x_26 = lean_ctor_get(x_4, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_4);
x_27 = lean_ctor_get(x_25, 4);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
x_29 = l_Lean_RBNode_find___at___Lean_Server_wrapRpcProcedure___at___Lean_Server_registerBuiltinRpcProcedure___at___Lean_Widget_initFn____x40_Lean_Server_FileWorker_WidgetRequests___hyg_394__spec__0_spec__0_spec__0___redArg(x_27, x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_26);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_32 = lean_ctor_get(x_29, 0);
lean_inc(x_32);
lean_dec(x_29);
x_33 = lean_io_mono_ms_now(x_26);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_st_ref_take(x_32, x_35);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l_Lean_Server_FileWorker_RpcSession_keptAlive(x_34, x_37);
lean_dec(x_37);
lean_dec(x_34);
x_40 = lean_st_ref_set(x_32, x_39, x_38);
lean_dec(x_32);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_43 = x_40;
} else {
 lean_dec_ref(x_40);
 x_43 = lean_box(0);
}
if (lean_is_scalar(x_43)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_43;
}
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleRpcKeepAlive(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_FileWorker_handleRpcKeepAlive___redArg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleRpcKeepAlive___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_FileWorker_handleRpcKeepAlive___redArg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleRpcKeepAlive___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_FileWorker_handleRpcKeepAlive(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_Server_FileWorker_handleRpcConnect_spec__0_spec__0___redArg___lam__0(uint64_t x_1, uint64_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_uint64_dec_lt(x_1, x_2);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = lean_uint64_dec_eq(x_1, x_2);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_box(2);
x_6 = lean_unbox(x_5);
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_box(1);
x_8 = lean_unbox(x_7);
return x_8;
}
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_box(0);
x_10 = lean_unbox(x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_Server_FileWorker_handleRpcConnect_spec__0_spec__0___redArg(lean_object* x_1, uint64_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_box(0);
x_5 = lean_box_uint64(x_2);
x_6 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_1);
x_7 = lean_unbox(x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*4, x_7);
return x_6;
}
else
{
uint8_t x_8; 
x_8 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint64_t x_14; uint8_t x_15; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
x_12 = lean_ctor_get(x_1, 2);
x_13 = lean_ctor_get(x_1, 3);
x_14 = lean_unbox_uint64(x_11);
x_15 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_Server_FileWorker_handleRpcConnect_spec__0_spec__0___redArg___lam__0(x_2, x_14);
switch (x_15) {
case 0:
{
lean_object* x_16; 
x_16 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_Server_FileWorker_handleRpcConnect_spec__0_spec__0___redArg(x_10, x_2, x_3);
lean_ctor_set(x_1, 0, x_16);
return x_1;
}
case 1:
{
lean_object* x_17; 
lean_dec(x_12);
lean_dec(x_11);
x_17 = lean_box_uint64(x_2);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_17);
return x_1;
}
default: 
{
lean_object* x_18; 
x_18 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_Server_FileWorker_handleRpcConnect_spec__0_spec__0___redArg(x_13, x_2, x_3);
lean_ctor_set(x_1, 3, x_18);
return x_1;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint64_t x_23; uint8_t x_24; 
x_19 = lean_ctor_get(x_1, 0);
x_20 = lean_ctor_get(x_1, 1);
x_21 = lean_ctor_get(x_1, 2);
x_22 = lean_ctor_get(x_1, 3);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_1);
x_23 = lean_unbox_uint64(x_20);
x_24 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_Server_FileWorker_handleRpcConnect_spec__0_spec__0___redArg___lam__0(x_2, x_23);
switch (x_24) {
case 0:
{
lean_object* x_25; lean_object* x_26; 
x_25 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_Server_FileWorker_handleRpcConnect_spec__0_spec__0___redArg(x_19, x_2, x_3);
x_26 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_20);
lean_ctor_set(x_26, 2, x_21);
lean_ctor_set(x_26, 3, x_22);
lean_ctor_set_uint8(x_26, sizeof(void*)*4, x_8);
return x_26;
}
case 1:
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_21);
lean_dec(x_20);
x_27 = lean_box_uint64(x_2);
x_28 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_28, 0, x_19);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set(x_28, 2, x_3);
lean_ctor_set(x_28, 3, x_22);
lean_ctor_set_uint8(x_28, sizeof(void*)*4, x_8);
return x_28;
}
default: 
{
lean_object* x_29; lean_object* x_30; 
x_29 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_Server_FileWorker_handleRpcConnect_spec__0_spec__0___redArg(x_22, x_2, x_3);
x_30 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_30, 0, x_19);
lean_ctor_set(x_30, 1, x_20);
lean_ctor_set(x_30, 2, x_21);
lean_ctor_set(x_30, 3, x_29);
lean_ctor_set_uint8(x_30, sizeof(void*)*4, x_8);
return x_30;
}
}
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint64_t x_36; uint8_t x_37; 
x_31 = lean_ctor_get(x_1, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_1, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_1, 2);
lean_inc(x_33);
x_34 = lean_ctor_get(x_1, 3);
lean_inc(x_34);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 x_35 = x_1;
} else {
 lean_dec_ref(x_1);
 x_35 = lean_box(0);
}
x_36 = lean_unbox_uint64(x_32);
x_37 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_Server_FileWorker_handleRpcConnect_spec__0_spec__0___redArg___lam__0(x_2, x_36);
switch (x_37) {
case 0:
{
lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint64_t x_45; lean_object* x_46; lean_object* x_47; uint64_t x_48; lean_object* x_49; lean_object* x_50; uint64_t x_51; lean_object* x_52; lean_object* x_53; 
x_38 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_Server_FileWorker_handleRpcConnect_spec__0_spec__0___redArg(x_31, x_2, x_3);
x_39 = lean_ctor_get_uint8(x_38, sizeof(void*)*4);
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
x_42 = lean_ctor_get(x_38, 2);
lean_inc(x_42);
x_43 = lean_ctor_get(x_38, 3);
lean_inc(x_43);
if (x_39 == 0)
{
if (lean_obj_tag(x_40) == 0)
{
if (lean_obj_tag(x_43) == 0)
{
uint8_t x_61; 
lean_dec(x_35);
x_61 = !lean_is_exclusive(x_38);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_62 = lean_ctor_get(x_38, 3);
lean_dec(x_62);
x_63 = lean_ctor_get(x_38, 2);
lean_dec(x_63);
x_64 = lean_ctor_get(x_38, 1);
lean_dec(x_64);
x_65 = lean_ctor_get(x_38, 0);
lean_dec(x_65);
lean_ctor_set(x_38, 0, x_43);
x_66 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_66, 0, x_38);
lean_ctor_set(x_66, 1, x_32);
lean_ctor_set(x_66, 2, x_33);
lean_ctor_set(x_66, 3, x_34);
lean_ctor_set_uint8(x_66, sizeof(void*)*4, x_8);
return x_66;
}
else
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_38);
x_67 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_67, 0, x_43);
lean_ctor_set(x_67, 1, x_41);
lean_ctor_set(x_67, 2, x_42);
lean_ctor_set(x_67, 3, x_43);
lean_ctor_set_uint8(x_67, sizeof(void*)*4, x_39);
x_68 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_32);
lean_ctor_set(x_68, 2, x_33);
lean_ctor_set(x_68, 3, x_34);
lean_ctor_set_uint8(x_68, sizeof(void*)*4, x_8);
return x_68;
}
}
else
{
uint8_t x_69; 
x_69 = lean_ctor_get_uint8(x_43, sizeof(void*)*4);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint64_t x_74; uint64_t x_75; uint64_t x_76; 
lean_dec(x_38);
x_70 = lean_ctor_get(x_43, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_43, 1);
lean_inc(x_71);
x_72 = lean_ctor_get(x_43, 2);
lean_inc(x_72);
x_73 = lean_ctor_get(x_43, 3);
lean_inc(x_73);
lean_dec(x_43);
x_74 = lean_unbox_uint64(x_41);
lean_dec(x_41);
x_75 = lean_unbox_uint64(x_71);
lean_dec(x_71);
x_76 = lean_unbox_uint64(x_32);
lean_dec(x_32);
x_44 = x_40;
x_45 = x_74;
x_46 = x_42;
x_47 = x_70;
x_48 = x_75;
x_49 = x_72;
x_50 = x_73;
x_51 = x_76;
x_52 = x_33;
x_53 = x_34;
goto block_60;
}
else
{
uint8_t x_77; 
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_35);
x_77 = !lean_is_exclusive(x_43);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_78 = lean_ctor_get(x_43, 3);
lean_dec(x_78);
x_79 = lean_ctor_get(x_43, 2);
lean_dec(x_79);
x_80 = lean_ctor_get(x_43, 1);
lean_dec(x_80);
x_81 = lean_ctor_get(x_43, 0);
lean_dec(x_81);
lean_ctor_set(x_43, 3, x_34);
lean_ctor_set(x_43, 2, x_33);
lean_ctor_set(x_43, 1, x_32);
lean_ctor_set(x_43, 0, x_38);
lean_ctor_set_uint8(x_43, sizeof(void*)*4, x_8);
return x_43;
}
else
{
lean_object* x_82; 
lean_dec(x_43);
x_82 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_82, 0, x_38);
lean_ctor_set(x_82, 1, x_32);
lean_ctor_set(x_82, 2, x_33);
lean_ctor_set(x_82, 3, x_34);
lean_ctor_set_uint8(x_82, sizeof(void*)*4, x_8);
return x_82;
}
}
}
}
else
{
uint8_t x_83; 
x_83 = lean_ctor_get_uint8(x_40, sizeof(void*)*4);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint64_t x_88; uint64_t x_89; uint64_t x_90; 
lean_dec(x_38);
x_84 = lean_ctor_get(x_40, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_40, 1);
lean_inc(x_85);
x_86 = lean_ctor_get(x_40, 2);
lean_inc(x_86);
x_87 = lean_ctor_get(x_40, 3);
lean_inc(x_87);
lean_dec(x_40);
x_88 = lean_unbox_uint64(x_85);
lean_dec(x_85);
x_89 = lean_unbox_uint64(x_41);
lean_dec(x_41);
x_90 = lean_unbox_uint64(x_32);
lean_dec(x_32);
x_44 = x_84;
x_45 = x_88;
x_46 = x_86;
x_47 = x_87;
x_48 = x_89;
x_49 = x_42;
x_50 = x_43;
x_51 = x_90;
x_52 = x_33;
x_53 = x_34;
goto block_60;
}
else
{
if (lean_obj_tag(x_43) == 0)
{
uint8_t x_91; 
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_35);
x_91 = !lean_is_exclusive(x_40);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_92 = lean_ctor_get(x_40, 3);
lean_dec(x_92);
x_93 = lean_ctor_get(x_40, 2);
lean_dec(x_93);
x_94 = lean_ctor_get(x_40, 1);
lean_dec(x_94);
x_95 = lean_ctor_get(x_40, 0);
lean_dec(x_95);
lean_ctor_set(x_40, 3, x_34);
lean_ctor_set(x_40, 2, x_33);
lean_ctor_set(x_40, 1, x_32);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set_uint8(x_40, sizeof(void*)*4, x_8);
return x_40;
}
else
{
lean_object* x_96; 
lean_dec(x_40);
x_96 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_96, 0, x_38);
lean_ctor_set(x_96, 1, x_32);
lean_ctor_set(x_96, 2, x_33);
lean_ctor_set(x_96, 3, x_34);
lean_ctor_set_uint8(x_96, sizeof(void*)*4, x_8);
return x_96;
}
}
else
{
uint8_t x_97; 
x_97 = !lean_is_exclusive(x_38);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; 
x_98 = lean_ctor_get(x_38, 3);
lean_dec(x_98);
x_99 = lean_ctor_get(x_38, 2);
lean_dec(x_99);
x_100 = lean_ctor_get(x_38, 1);
lean_dec(x_100);
x_101 = lean_ctor_get(x_38, 0);
lean_dec(x_101);
x_102 = lean_ctor_get_uint8(x_43, sizeof(void*)*4);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint64_t x_107; uint64_t x_108; uint64_t x_109; 
lean_free_object(x_38);
x_103 = lean_ctor_get(x_43, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_43, 1);
lean_inc(x_104);
x_105 = lean_ctor_get(x_43, 2);
lean_inc(x_105);
x_106 = lean_ctor_get(x_43, 3);
lean_inc(x_106);
lean_dec(x_43);
x_107 = lean_unbox_uint64(x_41);
lean_dec(x_41);
x_108 = lean_unbox_uint64(x_104);
lean_dec(x_104);
x_109 = lean_unbox_uint64(x_32);
lean_dec(x_32);
x_44 = x_40;
x_45 = x_107;
x_46 = x_42;
x_47 = x_103;
x_48 = x_108;
x_49 = x_105;
x_50 = x_106;
x_51 = x_109;
x_52 = x_33;
x_53 = x_34;
goto block_60;
}
else
{
uint8_t x_110; 
lean_dec(x_35);
x_110 = !lean_is_exclusive(x_40);
if (x_110 == 0)
{
lean_object* x_111; 
lean_ctor_set_uint8(x_40, sizeof(void*)*4, x_102);
x_111 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_111, 0, x_38);
lean_ctor_set(x_111, 1, x_32);
lean_ctor_set(x_111, 2, x_33);
lean_ctor_set(x_111, 3, x_34);
lean_ctor_set_uint8(x_111, sizeof(void*)*4, x_8);
return x_111;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_112 = lean_ctor_get(x_40, 0);
x_113 = lean_ctor_get(x_40, 1);
x_114 = lean_ctor_get(x_40, 2);
x_115 = lean_ctor_get(x_40, 3);
lean_inc(x_115);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_40);
x_116 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_116, 0, x_112);
lean_ctor_set(x_116, 1, x_113);
lean_ctor_set(x_116, 2, x_114);
lean_ctor_set(x_116, 3, x_115);
lean_ctor_set_uint8(x_116, sizeof(void*)*4, x_102);
lean_ctor_set(x_38, 0, x_116);
x_117 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_117, 0, x_38);
lean_ctor_set(x_117, 1, x_32);
lean_ctor_set(x_117, 2, x_33);
lean_ctor_set(x_117, 3, x_34);
lean_ctor_set_uint8(x_117, sizeof(void*)*4, x_8);
return x_117;
}
}
}
else
{
uint8_t x_118; 
lean_dec(x_38);
x_118 = lean_ctor_get_uint8(x_43, sizeof(void*)*4);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint64_t x_123; uint64_t x_124; uint64_t x_125; 
x_119 = lean_ctor_get(x_43, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_43, 1);
lean_inc(x_120);
x_121 = lean_ctor_get(x_43, 2);
lean_inc(x_121);
x_122 = lean_ctor_get(x_43, 3);
lean_inc(x_122);
lean_dec(x_43);
x_123 = lean_unbox_uint64(x_41);
lean_dec(x_41);
x_124 = lean_unbox_uint64(x_120);
lean_dec(x_120);
x_125 = lean_unbox_uint64(x_32);
lean_dec(x_32);
x_44 = x_40;
x_45 = x_123;
x_46 = x_42;
x_47 = x_119;
x_48 = x_124;
x_49 = x_121;
x_50 = x_122;
x_51 = x_125;
x_52 = x_33;
x_53 = x_34;
goto block_60;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
lean_dec(x_35);
x_126 = lean_ctor_get(x_40, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_40, 1);
lean_inc(x_127);
x_128 = lean_ctor_get(x_40, 2);
lean_inc(x_128);
x_129 = lean_ctor_get(x_40, 3);
lean_inc(x_129);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 lean_ctor_release(x_40, 2);
 lean_ctor_release(x_40, 3);
 x_130 = x_40;
} else {
 lean_dec_ref(x_40);
 x_130 = lean_box(0);
}
if (lean_is_scalar(x_130)) {
 x_131 = lean_alloc_ctor(1, 4, 1);
} else {
 x_131 = x_130;
}
lean_ctor_set(x_131, 0, x_126);
lean_ctor_set(x_131, 1, x_127);
lean_ctor_set(x_131, 2, x_128);
lean_ctor_set(x_131, 3, x_129);
lean_ctor_set_uint8(x_131, sizeof(void*)*4, x_118);
x_132 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_41);
lean_ctor_set(x_132, 2, x_42);
lean_ctor_set(x_132, 3, x_43);
lean_ctor_set_uint8(x_132, sizeof(void*)*4, x_39);
x_133 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_32);
lean_ctor_set(x_133, 2, x_33);
lean_ctor_set(x_133, 3, x_34);
lean_ctor_set_uint8(x_133, sizeof(void*)*4, x_8);
return x_133;
}
}
}
}
}
}
else
{
lean_object* x_134; 
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_35);
x_134 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_134, 0, x_38);
lean_ctor_set(x_134, 1, x_32);
lean_ctor_set(x_134, 2, x_33);
lean_ctor_set(x_134, 3, x_34);
lean_ctor_set_uint8(x_134, sizeof(void*)*4, x_8);
return x_134;
}
block_60:
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_54 = lean_box_uint64(x_45);
if (lean_is_scalar(x_35)) {
 x_55 = lean_alloc_ctor(1, 4, 1);
} else {
 x_55 = x_35;
}
lean_ctor_set(x_55, 0, x_44);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set(x_55, 2, x_46);
lean_ctor_set(x_55, 3, x_47);
lean_ctor_set_uint8(x_55, sizeof(void*)*4, x_8);
x_56 = lean_box_uint64(x_51);
x_57 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_57, 0, x_50);
lean_ctor_set(x_57, 1, x_56);
lean_ctor_set(x_57, 2, x_52);
lean_ctor_set(x_57, 3, x_53);
lean_ctor_set_uint8(x_57, sizeof(void*)*4, x_8);
x_58 = lean_box_uint64(x_48);
x_59 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_59, 0, x_55);
lean_ctor_set(x_59, 1, x_58);
lean_ctor_set(x_59, 2, x_49);
lean_ctor_set(x_59, 3, x_57);
lean_ctor_set_uint8(x_59, sizeof(void*)*4, x_39);
return x_59;
}
}
case 1:
{
lean_object* x_135; lean_object* x_136; 
lean_dec(x_33);
lean_dec(x_32);
x_135 = lean_box_uint64(x_2);
if (lean_is_scalar(x_35)) {
 x_136 = lean_alloc_ctor(1, 4, 1);
} else {
 x_136 = x_35;
}
lean_ctor_set(x_136, 0, x_31);
lean_ctor_set(x_136, 1, x_135);
lean_ctor_set(x_136, 2, x_3);
lean_ctor_set(x_136, 3, x_34);
lean_ctor_set_uint8(x_136, sizeof(void*)*4, x_8);
return x_136;
}
default: 
{
lean_object* x_137; uint8_t x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; uint64_t x_144; lean_object* x_145; lean_object* x_146; uint64_t x_147; lean_object* x_148; lean_object* x_149; uint64_t x_150; lean_object* x_151; lean_object* x_152; 
x_137 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_Server_FileWorker_handleRpcConnect_spec__0_spec__0___redArg(x_34, x_2, x_3);
x_138 = lean_ctor_get_uint8(x_137, sizeof(void*)*4);
x_139 = lean_ctor_get(x_137, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_137, 1);
lean_inc(x_140);
x_141 = lean_ctor_get(x_137, 2);
lean_inc(x_141);
x_142 = lean_ctor_get(x_137, 3);
lean_inc(x_142);
if (x_138 == 0)
{
if (lean_obj_tag(x_139) == 0)
{
if (lean_obj_tag(x_142) == 0)
{
uint8_t x_160; 
lean_dec(x_35);
x_160 = !lean_is_exclusive(x_137);
if (x_160 == 0)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_161 = lean_ctor_get(x_137, 3);
lean_dec(x_161);
x_162 = lean_ctor_get(x_137, 2);
lean_dec(x_162);
x_163 = lean_ctor_get(x_137, 1);
lean_dec(x_163);
x_164 = lean_ctor_get(x_137, 0);
lean_dec(x_164);
lean_ctor_set(x_137, 0, x_142);
x_165 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_165, 0, x_31);
lean_ctor_set(x_165, 1, x_32);
lean_ctor_set(x_165, 2, x_33);
lean_ctor_set(x_165, 3, x_137);
lean_ctor_set_uint8(x_165, sizeof(void*)*4, x_8);
return x_165;
}
else
{
lean_object* x_166; lean_object* x_167; 
lean_dec(x_137);
x_166 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_166, 0, x_142);
lean_ctor_set(x_166, 1, x_140);
lean_ctor_set(x_166, 2, x_141);
lean_ctor_set(x_166, 3, x_142);
lean_ctor_set_uint8(x_166, sizeof(void*)*4, x_138);
x_167 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_167, 0, x_31);
lean_ctor_set(x_167, 1, x_32);
lean_ctor_set(x_167, 2, x_33);
lean_ctor_set(x_167, 3, x_166);
lean_ctor_set_uint8(x_167, sizeof(void*)*4, x_8);
return x_167;
}
}
else
{
uint8_t x_168; 
x_168 = lean_ctor_get_uint8(x_142, sizeof(void*)*4);
if (x_168 == 0)
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; uint64_t x_173; uint64_t x_174; uint64_t x_175; 
lean_dec(x_137);
x_169 = lean_ctor_get(x_142, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_142, 1);
lean_inc(x_170);
x_171 = lean_ctor_get(x_142, 2);
lean_inc(x_171);
x_172 = lean_ctor_get(x_142, 3);
lean_inc(x_172);
lean_dec(x_142);
x_173 = lean_unbox_uint64(x_32);
lean_dec(x_32);
x_174 = lean_unbox_uint64(x_140);
lean_dec(x_140);
x_175 = lean_unbox_uint64(x_170);
lean_dec(x_170);
x_143 = x_31;
x_144 = x_173;
x_145 = x_33;
x_146 = x_139;
x_147 = x_174;
x_148 = x_141;
x_149 = x_169;
x_150 = x_175;
x_151 = x_171;
x_152 = x_172;
goto block_159;
}
else
{
uint8_t x_176; 
lean_dec(x_141);
lean_dec(x_140);
lean_dec(x_35);
x_176 = !lean_is_exclusive(x_142);
if (x_176 == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_177 = lean_ctor_get(x_142, 3);
lean_dec(x_177);
x_178 = lean_ctor_get(x_142, 2);
lean_dec(x_178);
x_179 = lean_ctor_get(x_142, 1);
lean_dec(x_179);
x_180 = lean_ctor_get(x_142, 0);
lean_dec(x_180);
lean_ctor_set(x_142, 3, x_137);
lean_ctor_set(x_142, 2, x_33);
lean_ctor_set(x_142, 1, x_32);
lean_ctor_set(x_142, 0, x_31);
lean_ctor_set_uint8(x_142, sizeof(void*)*4, x_8);
return x_142;
}
else
{
lean_object* x_181; 
lean_dec(x_142);
x_181 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_181, 0, x_31);
lean_ctor_set(x_181, 1, x_32);
lean_ctor_set(x_181, 2, x_33);
lean_ctor_set(x_181, 3, x_137);
lean_ctor_set_uint8(x_181, sizeof(void*)*4, x_8);
return x_181;
}
}
}
}
else
{
uint8_t x_182; 
x_182 = lean_ctor_get_uint8(x_139, sizeof(void*)*4);
if (x_182 == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; uint64_t x_187; uint64_t x_188; uint64_t x_189; 
lean_dec(x_137);
x_183 = lean_ctor_get(x_139, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_139, 1);
lean_inc(x_184);
x_185 = lean_ctor_get(x_139, 2);
lean_inc(x_185);
x_186 = lean_ctor_get(x_139, 3);
lean_inc(x_186);
lean_dec(x_139);
x_187 = lean_unbox_uint64(x_32);
lean_dec(x_32);
x_188 = lean_unbox_uint64(x_184);
lean_dec(x_184);
x_189 = lean_unbox_uint64(x_140);
lean_dec(x_140);
x_143 = x_31;
x_144 = x_187;
x_145 = x_33;
x_146 = x_183;
x_147 = x_188;
x_148 = x_185;
x_149 = x_186;
x_150 = x_189;
x_151 = x_141;
x_152 = x_142;
goto block_159;
}
else
{
if (lean_obj_tag(x_142) == 0)
{
uint8_t x_190; 
lean_dec(x_141);
lean_dec(x_140);
lean_dec(x_35);
x_190 = !lean_is_exclusive(x_139);
if (x_190 == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_191 = lean_ctor_get(x_139, 3);
lean_dec(x_191);
x_192 = lean_ctor_get(x_139, 2);
lean_dec(x_192);
x_193 = lean_ctor_get(x_139, 1);
lean_dec(x_193);
x_194 = lean_ctor_get(x_139, 0);
lean_dec(x_194);
lean_ctor_set(x_139, 3, x_137);
lean_ctor_set(x_139, 2, x_33);
lean_ctor_set(x_139, 1, x_32);
lean_ctor_set(x_139, 0, x_31);
lean_ctor_set_uint8(x_139, sizeof(void*)*4, x_8);
return x_139;
}
else
{
lean_object* x_195; 
lean_dec(x_139);
x_195 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_195, 0, x_31);
lean_ctor_set(x_195, 1, x_32);
lean_ctor_set(x_195, 2, x_33);
lean_ctor_set(x_195, 3, x_137);
lean_ctor_set_uint8(x_195, sizeof(void*)*4, x_8);
return x_195;
}
}
else
{
uint8_t x_196; 
x_196 = !lean_is_exclusive(x_137);
if (x_196 == 0)
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; uint8_t x_201; 
x_197 = lean_ctor_get(x_137, 3);
lean_dec(x_197);
x_198 = lean_ctor_get(x_137, 2);
lean_dec(x_198);
x_199 = lean_ctor_get(x_137, 1);
lean_dec(x_199);
x_200 = lean_ctor_get(x_137, 0);
lean_dec(x_200);
x_201 = lean_ctor_get_uint8(x_142, sizeof(void*)*4);
if (x_201 == 0)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; uint64_t x_206; uint64_t x_207; uint64_t x_208; 
lean_free_object(x_137);
x_202 = lean_ctor_get(x_142, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_142, 1);
lean_inc(x_203);
x_204 = lean_ctor_get(x_142, 2);
lean_inc(x_204);
x_205 = lean_ctor_get(x_142, 3);
lean_inc(x_205);
lean_dec(x_142);
x_206 = lean_unbox_uint64(x_32);
lean_dec(x_32);
x_207 = lean_unbox_uint64(x_140);
lean_dec(x_140);
x_208 = lean_unbox_uint64(x_203);
lean_dec(x_203);
x_143 = x_31;
x_144 = x_206;
x_145 = x_33;
x_146 = x_139;
x_147 = x_207;
x_148 = x_141;
x_149 = x_202;
x_150 = x_208;
x_151 = x_204;
x_152 = x_205;
goto block_159;
}
else
{
uint8_t x_209; 
lean_dec(x_35);
x_209 = !lean_is_exclusive(x_139);
if (x_209 == 0)
{
lean_object* x_210; 
lean_ctor_set_uint8(x_139, sizeof(void*)*4, x_201);
x_210 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_210, 0, x_31);
lean_ctor_set(x_210, 1, x_32);
lean_ctor_set(x_210, 2, x_33);
lean_ctor_set(x_210, 3, x_137);
lean_ctor_set_uint8(x_210, sizeof(void*)*4, x_8);
return x_210;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_211 = lean_ctor_get(x_139, 0);
x_212 = lean_ctor_get(x_139, 1);
x_213 = lean_ctor_get(x_139, 2);
x_214 = lean_ctor_get(x_139, 3);
lean_inc(x_214);
lean_inc(x_213);
lean_inc(x_212);
lean_inc(x_211);
lean_dec(x_139);
x_215 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_215, 0, x_211);
lean_ctor_set(x_215, 1, x_212);
lean_ctor_set(x_215, 2, x_213);
lean_ctor_set(x_215, 3, x_214);
lean_ctor_set_uint8(x_215, sizeof(void*)*4, x_201);
lean_ctor_set(x_137, 0, x_215);
x_216 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_216, 0, x_31);
lean_ctor_set(x_216, 1, x_32);
lean_ctor_set(x_216, 2, x_33);
lean_ctor_set(x_216, 3, x_137);
lean_ctor_set_uint8(x_216, sizeof(void*)*4, x_8);
return x_216;
}
}
}
else
{
uint8_t x_217; 
lean_dec(x_137);
x_217 = lean_ctor_get_uint8(x_142, sizeof(void*)*4);
if (x_217 == 0)
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; uint64_t x_222; uint64_t x_223; uint64_t x_224; 
x_218 = lean_ctor_get(x_142, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_142, 1);
lean_inc(x_219);
x_220 = lean_ctor_get(x_142, 2);
lean_inc(x_220);
x_221 = lean_ctor_get(x_142, 3);
lean_inc(x_221);
lean_dec(x_142);
x_222 = lean_unbox_uint64(x_32);
lean_dec(x_32);
x_223 = lean_unbox_uint64(x_140);
lean_dec(x_140);
x_224 = lean_unbox_uint64(x_219);
lean_dec(x_219);
x_143 = x_31;
x_144 = x_222;
x_145 = x_33;
x_146 = x_139;
x_147 = x_223;
x_148 = x_141;
x_149 = x_218;
x_150 = x_224;
x_151 = x_220;
x_152 = x_221;
goto block_159;
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
lean_dec(x_35);
x_225 = lean_ctor_get(x_139, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_139, 1);
lean_inc(x_226);
x_227 = lean_ctor_get(x_139, 2);
lean_inc(x_227);
x_228 = lean_ctor_get(x_139, 3);
lean_inc(x_228);
if (lean_is_exclusive(x_139)) {
 lean_ctor_release(x_139, 0);
 lean_ctor_release(x_139, 1);
 lean_ctor_release(x_139, 2);
 lean_ctor_release(x_139, 3);
 x_229 = x_139;
} else {
 lean_dec_ref(x_139);
 x_229 = lean_box(0);
}
if (lean_is_scalar(x_229)) {
 x_230 = lean_alloc_ctor(1, 4, 1);
} else {
 x_230 = x_229;
}
lean_ctor_set(x_230, 0, x_225);
lean_ctor_set(x_230, 1, x_226);
lean_ctor_set(x_230, 2, x_227);
lean_ctor_set(x_230, 3, x_228);
lean_ctor_set_uint8(x_230, sizeof(void*)*4, x_217);
x_231 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_231, 0, x_230);
lean_ctor_set(x_231, 1, x_140);
lean_ctor_set(x_231, 2, x_141);
lean_ctor_set(x_231, 3, x_142);
lean_ctor_set_uint8(x_231, sizeof(void*)*4, x_138);
x_232 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_232, 0, x_31);
lean_ctor_set(x_232, 1, x_32);
lean_ctor_set(x_232, 2, x_33);
lean_ctor_set(x_232, 3, x_231);
lean_ctor_set_uint8(x_232, sizeof(void*)*4, x_8);
return x_232;
}
}
}
}
}
}
else
{
lean_object* x_233; 
lean_dec(x_142);
lean_dec(x_141);
lean_dec(x_140);
lean_dec(x_139);
lean_dec(x_35);
x_233 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_233, 0, x_31);
lean_ctor_set(x_233, 1, x_32);
lean_ctor_set(x_233, 2, x_33);
lean_ctor_set(x_233, 3, x_137);
lean_ctor_set_uint8(x_233, sizeof(void*)*4, x_8);
return x_233;
}
block_159:
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_153 = lean_box_uint64(x_144);
if (lean_is_scalar(x_35)) {
 x_154 = lean_alloc_ctor(1, 4, 1);
} else {
 x_154 = x_35;
}
lean_ctor_set(x_154, 0, x_143);
lean_ctor_set(x_154, 1, x_153);
lean_ctor_set(x_154, 2, x_145);
lean_ctor_set(x_154, 3, x_146);
lean_ctor_set_uint8(x_154, sizeof(void*)*4, x_8);
x_155 = lean_box_uint64(x_150);
x_156 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_156, 0, x_149);
lean_ctor_set(x_156, 1, x_155);
lean_ctor_set(x_156, 2, x_151);
lean_ctor_set(x_156, 3, x_152);
lean_ctor_set_uint8(x_156, sizeof(void*)*4, x_8);
x_157 = lean_box_uint64(x_147);
x_158 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_158, 0, x_154);
lean_ctor_set(x_158, 1, x_157);
lean_ctor_set(x_158, 2, x_148);
lean_ctor_set(x_158, 3, x_156);
lean_ctor_set_uint8(x_158, sizeof(void*)*4, x_138);
return x_158;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_Server_FileWorker_handleRpcConnect_spec__0_spec__0(lean_object* x_1, lean_object* x_2, uint64_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_Server_FileWorker_handleRpcConnect_spec__0_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at___Lean_Server_FileWorker_handleRpcConnect_spec__0___redArg(lean_object* x_1, uint64_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_RBNode_isRed___redArg(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_Server_FileWorker_handleRpcConnect_spec__0_spec__0___redArg(x_1, x_2, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_Server_FileWorker_handleRpcConnect_spec__0_spec__0___redArg(x_1, x_2, x_3);
x_7 = l_Lean_RBNode_setBlack___redArg(x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at___Lean_Server_FileWorker_handleRpcConnect_spec__0(lean_object* x_1, lean_object* x_2, uint64_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_insert___at___Lean_Server_FileWorker_handleRpcConnect_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleRpcConnect___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_FileWorker_RpcSession_new(x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint64_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
x_8 = lean_st_mk_ref(x_7, x_5);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_st_ref_take(x_1, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 4);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_12, 2);
lean_inc(x_17);
x_18 = lean_ctor_get(x_12, 3);
lean_inc(x_18);
lean_dec(x_12);
x_19 = lean_unbox_uint64(x_6);
x_20 = l_Lean_RBNode_insert___at___Lean_Server_FileWorker_handleRpcConnect_spec__0___redArg(x_14, x_19, x_9);
x_21 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_21, 0, x_15);
lean_ctor_set(x_21, 1, x_16);
lean_ctor_set(x_21, 2, x_17);
lean_ctor_set(x_21, 3, x_18);
lean_ctor_set(x_21, 4, x_20);
x_22 = lean_st_ref_set(x_1, x_21, x_13);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
lean_ctor_set(x_22, 0, x_6);
return x_22;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_6);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_3);
if (x_27 == 0)
{
return x_3;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_3, 0);
x_29 = lean_ctor_get(x_3, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_3);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleRpcConnect(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_FileWorker_handleRpcConnect___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_Server_FileWorker_handleRpcConnect_spec__0_spec__0___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_Server_FileWorker_handleRpcConnect_spec__0_spec__0___redArg___lam__0(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_Server_FileWorker_handleRpcConnect_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_Server_FileWorker_handleRpcConnect_spec__0_spec__0___redArg(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_Server_FileWorker_handleRpcConnect_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint64_t x_5; lean_object* x_6; 
x_5 = lean_unbox_uint64(x_3);
lean_dec(x_3);
x_6 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_Server_FileWorker_handleRpcConnect_spec__0_spec__0(x_1, x_2, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at___Lean_Server_FileWorker_handleRpcConnect_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = l_Lean_RBNode_insert___at___Lean_Server_FileWorker_handleRpcConnect_spec__0___redArg(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at___Lean_Server_FileWorker_handleRpcConnect_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint64_t x_5; lean_object* x_6; 
x_5 = lean_unbox_uint64(x_3);
lean_dec(x_3);
x_6 = l_Lean_RBNode_insert___at___Lean_Server_FileWorker_handleRpcConnect_spec__0(x_1, x_2, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleRpcConnect___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_FileWorker_handleRpcConnect___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleRpcConnect___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_FileWorker_handleRpcConnect(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_parseParams___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
x_4 = lean_apply_1(x_1, x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_mk_string_unchecked("Got param with wrong structure: ", 32, 32);
x_7 = l_Lean_Json_compress(x_2);
x_8 = lean_string_append(x_6, x_7);
lean_dec(x_7);
x_9 = lean_mk_string_unchecked("\n", 1, 1);
x_10 = lean_string_append(x_8, x_9);
lean_dec(x_9);
x_11 = lean_string_append(x_10, x_5);
lean_dec(x_5);
x_12 = l_IO_throwServerError(lean_box(0), x_11, x_3);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_2);
x_13 = lean_ctor_get(x_4, 0);
lean_inc(x_13);
lean_dec(x_4);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_3);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_parseParams(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Server_FileWorker_parseParams___redArg(x_2, x_3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_parseParams___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Server_FileWorker_parseParams(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleNotification(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_20; uint8_t x_21; 
x_20 = lean_mk_string_unchecked("textDocument/didChange", 22, 22);
x_21 = lean_string_dec_eq(x_1, x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_mk_string_unchecked("$/cancelRequest", 15, 15);
x_23 = lean_string_dec_eq(x_1, x_22);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_mk_string_unchecked("$/lean/staleDependency", 22, 22);
x_25 = lean_string_dec_eq(x_1, x_24);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_mk_string_unchecked("$/lean/rpc/release", 18, 18);
x_27 = lean_string_dec_eq(x_1, x_26);
lean_dec(x_26);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_mk_string_unchecked("$/lean/rpc/keepAlive", 20, 20);
x_29 = lean_string_dec_eq(x_1, x_28);
lean_dec(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_30 = lean_mk_string_unchecked("Got unsupported notification method: ", 37, 37);
x_31 = lean_string_append(x_30, x_1);
x_32 = l_IO_throwServerError(lean_box(0), x_31, x_5);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Extra_0__Lean_Lsp_fromJsonRpcKeepAliveParams____x40_Lean_Data_Lsp_Extra___hyg_2827_), 1, 0);
x_34 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_handleRpcKeepAlive___boxed), 4, 0);
x_6 = x_33;
x_7 = x_34;
x_8 = x_3;
x_9 = x_4;
x_10 = x_5;
goto block_19;
}
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = l_Lean_Lsp_instFromJsonRpcReleaseParams;
x_36 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_handleRpcRelease___boxed), 4, 0);
x_6 = x_35;
x_7 = x_36;
x_8 = x_3;
x_9 = x_4;
x_10 = x_5;
goto block_19;
}
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanStaleDependencyParams____x40_Lean_Data_Lsp_Internal___hyg_2481_), 1, 0);
x_38 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_handleStaleDependency___boxed), 4, 0);
x_6 = x_37;
x_7 = x_38;
x_8 = x_3;
x_9 = x_4;
x_10 = x_5;
goto block_19;
}
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = l_Lean_Lsp_instFromJsonCancelParams;
x_40 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_handleCancelRequest___boxed), 4, 0);
x_6 = x_39;
x_7 = x_40;
x_8 = x_3;
x_9 = x_4;
x_10 = x_5;
goto block_19;
}
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams;
x_42 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_handleDidChange___boxed), 4, 0);
x_6 = x_41;
x_7 = x_42;
x_8 = x_3;
x_9 = x_4;
x_10 = x_5;
goto block_19;
}
block_19:
{
lean_object* x_11; 
x_11 = l_Lean_Server_FileWorker_parseParams___redArg(x_6, x_2, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_apply_4(x_7, x_12, x_8, x_9, x_13);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_11, 0);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_11);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleNotification___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Server_FileWorker_handleNotification(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_Server_FileWorker_queueRequest_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_1);
x_6 = lean_unbox(x_4);
lean_ctor_set_uint8(x_5, sizeof(void*)*4, x_6);
return x_5;
}
else
{
uint8_t x_7; 
x_7 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_ctor_get(x_1, 2);
x_12 = lean_ctor_get(x_1, 3);
lean_inc(x_10);
lean_inc(x_2);
x_13 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_ordRequestID____x40_Lean_Data_JsonRpc___hyg_126_(x_2, x_10);
switch (x_13) {
case 0:
{
lean_object* x_14; 
x_14 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_Server_FileWorker_queueRequest_spec__0_spec__0___redArg(x_9, x_2, x_3);
lean_ctor_set(x_1, 0, x_14);
return x_1;
}
case 1:
{
lean_dec(x_11);
lean_dec(x_10);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
return x_1;
}
default: 
{
lean_object* x_15; 
x_15 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_Server_FileWorker_queueRequest_spec__0_spec__0___redArg(x_12, x_2, x_3);
lean_ctor_set(x_1, 3, x_15);
return x_1;
}
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_1, 0);
x_17 = lean_ctor_get(x_1, 1);
x_18 = lean_ctor_get(x_1, 2);
x_19 = lean_ctor_get(x_1, 3);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_1);
lean_inc(x_17);
lean_inc(x_2);
x_20 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_ordRequestID____x40_Lean_Data_JsonRpc___hyg_126_(x_2, x_17);
switch (x_20) {
case 0:
{
lean_object* x_21; lean_object* x_22; 
x_21 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_Server_FileWorker_queueRequest_spec__0_spec__0___redArg(x_16, x_2, x_3);
x_22 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_17);
lean_ctor_set(x_22, 2, x_18);
lean_ctor_set(x_22, 3, x_19);
lean_ctor_set_uint8(x_22, sizeof(void*)*4, x_7);
return x_22;
}
case 1:
{
lean_object* x_23; 
lean_dec(x_18);
lean_dec(x_17);
x_23 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_23, 0, x_16);
lean_ctor_set(x_23, 1, x_2);
lean_ctor_set(x_23, 2, x_3);
lean_ctor_set(x_23, 3, x_19);
lean_ctor_set_uint8(x_23, sizeof(void*)*4, x_7);
return x_23;
}
default: 
{
lean_object* x_24; lean_object* x_25; 
x_24 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_Server_FileWorker_queueRequest_spec__0_spec__0___redArg(x_19, x_2, x_3);
x_25 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_25, 0, x_16);
lean_ctor_set(x_25, 1, x_17);
lean_ctor_set(x_25, 2, x_18);
lean_ctor_set(x_25, 3, x_24);
lean_ctor_set_uint8(x_25, sizeof(void*)*4, x_7);
return x_25;
}
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_26 = lean_ctor_get(x_1, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_1, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_1, 2);
lean_inc(x_28);
x_29 = lean_ctor_get(x_1, 3);
lean_inc(x_29);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 x_30 = x_1;
} else {
 lean_dec_ref(x_1);
 x_30 = lean_box(0);
}
lean_inc(x_27);
lean_inc(x_2);
x_31 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_ordRequestID____x40_Lean_Data_JsonRpc___hyg_126_(x_2, x_27);
switch (x_31) {
case 0:
{
lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_32 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_Server_FileWorker_queueRequest_spec__0_spec__0___redArg(x_26, x_2, x_3);
x_33 = lean_ctor_get_uint8(x_32, sizeof(void*)*4);
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_32, 2);
lean_inc(x_36);
x_37 = lean_ctor_get(x_32, 3);
lean_inc(x_37);
if (x_33 == 0)
{
if (lean_obj_tag(x_34) == 0)
{
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_52; 
lean_dec(x_30);
x_52 = !lean_is_exclusive(x_32);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_53 = lean_ctor_get(x_32, 3);
lean_dec(x_53);
x_54 = lean_ctor_get(x_32, 2);
lean_dec(x_54);
x_55 = lean_ctor_get(x_32, 1);
lean_dec(x_55);
x_56 = lean_ctor_get(x_32, 0);
lean_dec(x_56);
lean_ctor_set(x_32, 0, x_37);
x_57 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_57, 0, x_32);
lean_ctor_set(x_57, 1, x_27);
lean_ctor_set(x_57, 2, x_28);
lean_ctor_set(x_57, 3, x_29);
lean_ctor_set_uint8(x_57, sizeof(void*)*4, x_7);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_32);
x_58 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_58, 0, x_37);
lean_ctor_set(x_58, 1, x_35);
lean_ctor_set(x_58, 2, x_36);
lean_ctor_set(x_58, 3, x_37);
lean_ctor_set_uint8(x_58, sizeof(void*)*4, x_33);
x_59 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_27);
lean_ctor_set(x_59, 2, x_28);
lean_ctor_set(x_59, 3, x_29);
lean_ctor_set_uint8(x_59, sizeof(void*)*4, x_7);
return x_59;
}
}
else
{
uint8_t x_60; 
x_60 = lean_ctor_get_uint8(x_37, sizeof(void*)*4);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_32);
x_61 = lean_ctor_get(x_37, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_37, 1);
lean_inc(x_62);
x_63 = lean_ctor_get(x_37, 2);
lean_inc(x_63);
x_64 = lean_ctor_get(x_37, 3);
lean_inc(x_64);
lean_dec(x_37);
x_38 = x_34;
x_39 = x_35;
x_40 = x_36;
x_41 = x_61;
x_42 = x_62;
x_43 = x_63;
x_44 = x_64;
x_45 = x_27;
x_46 = x_28;
x_47 = x_29;
goto block_51;
}
else
{
uint8_t x_65; 
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_30);
x_65 = !lean_is_exclusive(x_37);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_37, 3);
lean_dec(x_66);
x_67 = lean_ctor_get(x_37, 2);
lean_dec(x_67);
x_68 = lean_ctor_get(x_37, 1);
lean_dec(x_68);
x_69 = lean_ctor_get(x_37, 0);
lean_dec(x_69);
lean_ctor_set(x_37, 3, x_29);
lean_ctor_set(x_37, 2, x_28);
lean_ctor_set(x_37, 1, x_27);
lean_ctor_set(x_37, 0, x_32);
lean_ctor_set_uint8(x_37, sizeof(void*)*4, x_7);
return x_37;
}
else
{
lean_object* x_70; 
lean_dec(x_37);
x_70 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_70, 0, x_32);
lean_ctor_set(x_70, 1, x_27);
lean_ctor_set(x_70, 2, x_28);
lean_ctor_set(x_70, 3, x_29);
lean_ctor_set_uint8(x_70, sizeof(void*)*4, x_7);
return x_70;
}
}
}
}
else
{
uint8_t x_71; 
x_71 = lean_ctor_get_uint8(x_34, sizeof(void*)*4);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_32);
x_72 = lean_ctor_get(x_34, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_34, 1);
lean_inc(x_73);
x_74 = lean_ctor_get(x_34, 2);
lean_inc(x_74);
x_75 = lean_ctor_get(x_34, 3);
lean_inc(x_75);
lean_dec(x_34);
x_38 = x_72;
x_39 = x_73;
x_40 = x_74;
x_41 = x_75;
x_42 = x_35;
x_43 = x_36;
x_44 = x_37;
x_45 = x_27;
x_46 = x_28;
x_47 = x_29;
goto block_51;
}
else
{
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_76; 
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_30);
x_76 = !lean_is_exclusive(x_34);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_77 = lean_ctor_get(x_34, 3);
lean_dec(x_77);
x_78 = lean_ctor_get(x_34, 2);
lean_dec(x_78);
x_79 = lean_ctor_get(x_34, 1);
lean_dec(x_79);
x_80 = lean_ctor_get(x_34, 0);
lean_dec(x_80);
lean_ctor_set(x_34, 3, x_29);
lean_ctor_set(x_34, 2, x_28);
lean_ctor_set(x_34, 1, x_27);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set_uint8(x_34, sizeof(void*)*4, x_7);
return x_34;
}
else
{
lean_object* x_81; 
lean_dec(x_34);
x_81 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_81, 0, x_32);
lean_ctor_set(x_81, 1, x_27);
lean_ctor_set(x_81, 2, x_28);
lean_ctor_set(x_81, 3, x_29);
lean_ctor_set_uint8(x_81, sizeof(void*)*4, x_7);
return x_81;
}
}
else
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_32);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_83 = lean_ctor_get(x_32, 3);
lean_dec(x_83);
x_84 = lean_ctor_get(x_32, 2);
lean_dec(x_84);
x_85 = lean_ctor_get(x_32, 1);
lean_dec(x_85);
x_86 = lean_ctor_get(x_32, 0);
lean_dec(x_86);
x_87 = lean_ctor_get_uint8(x_37, sizeof(void*)*4);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_free_object(x_32);
x_88 = lean_ctor_get(x_37, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_37, 1);
lean_inc(x_89);
x_90 = lean_ctor_get(x_37, 2);
lean_inc(x_90);
x_91 = lean_ctor_get(x_37, 3);
lean_inc(x_91);
lean_dec(x_37);
x_38 = x_34;
x_39 = x_35;
x_40 = x_36;
x_41 = x_88;
x_42 = x_89;
x_43 = x_90;
x_44 = x_91;
x_45 = x_27;
x_46 = x_28;
x_47 = x_29;
goto block_51;
}
else
{
uint8_t x_92; 
lean_dec(x_30);
x_92 = !lean_is_exclusive(x_34);
if (x_92 == 0)
{
lean_object* x_93; 
lean_ctor_set_uint8(x_34, sizeof(void*)*4, x_87);
x_93 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_93, 0, x_32);
lean_ctor_set(x_93, 1, x_27);
lean_ctor_set(x_93, 2, x_28);
lean_ctor_set(x_93, 3, x_29);
lean_ctor_set_uint8(x_93, sizeof(void*)*4, x_7);
return x_93;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_94 = lean_ctor_get(x_34, 0);
x_95 = lean_ctor_get(x_34, 1);
x_96 = lean_ctor_get(x_34, 2);
x_97 = lean_ctor_get(x_34, 3);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_34);
x_98 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_98, 0, x_94);
lean_ctor_set(x_98, 1, x_95);
lean_ctor_set(x_98, 2, x_96);
lean_ctor_set(x_98, 3, x_97);
lean_ctor_set_uint8(x_98, sizeof(void*)*4, x_87);
lean_ctor_set(x_32, 0, x_98);
x_99 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_99, 0, x_32);
lean_ctor_set(x_99, 1, x_27);
lean_ctor_set(x_99, 2, x_28);
lean_ctor_set(x_99, 3, x_29);
lean_ctor_set_uint8(x_99, sizeof(void*)*4, x_7);
return x_99;
}
}
}
else
{
uint8_t x_100; 
lean_dec(x_32);
x_100 = lean_ctor_get_uint8(x_37, sizeof(void*)*4);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_101 = lean_ctor_get(x_37, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_37, 1);
lean_inc(x_102);
x_103 = lean_ctor_get(x_37, 2);
lean_inc(x_103);
x_104 = lean_ctor_get(x_37, 3);
lean_inc(x_104);
lean_dec(x_37);
x_38 = x_34;
x_39 = x_35;
x_40 = x_36;
x_41 = x_101;
x_42 = x_102;
x_43 = x_103;
x_44 = x_104;
x_45 = x_27;
x_46 = x_28;
x_47 = x_29;
goto block_51;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_30);
x_105 = lean_ctor_get(x_34, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_34, 1);
lean_inc(x_106);
x_107 = lean_ctor_get(x_34, 2);
lean_inc(x_107);
x_108 = lean_ctor_get(x_34, 3);
lean_inc(x_108);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 lean_ctor_release(x_34, 2);
 lean_ctor_release(x_34, 3);
 x_109 = x_34;
} else {
 lean_dec_ref(x_34);
 x_109 = lean_box(0);
}
if (lean_is_scalar(x_109)) {
 x_110 = lean_alloc_ctor(1, 4, 1);
} else {
 x_110 = x_109;
}
lean_ctor_set(x_110, 0, x_105);
lean_ctor_set(x_110, 1, x_106);
lean_ctor_set(x_110, 2, x_107);
lean_ctor_set(x_110, 3, x_108);
lean_ctor_set_uint8(x_110, sizeof(void*)*4, x_100);
x_111 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_35);
lean_ctor_set(x_111, 2, x_36);
lean_ctor_set(x_111, 3, x_37);
lean_ctor_set_uint8(x_111, sizeof(void*)*4, x_33);
x_112 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_27);
lean_ctor_set(x_112, 2, x_28);
lean_ctor_set(x_112, 3, x_29);
lean_ctor_set_uint8(x_112, sizeof(void*)*4, x_7);
return x_112;
}
}
}
}
}
}
else
{
lean_object* x_113; 
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_30);
x_113 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_113, 0, x_32);
lean_ctor_set(x_113, 1, x_27);
lean_ctor_set(x_113, 2, x_28);
lean_ctor_set(x_113, 3, x_29);
lean_ctor_set_uint8(x_113, sizeof(void*)*4, x_7);
return x_113;
}
block_51:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
if (lean_is_scalar(x_30)) {
 x_48 = lean_alloc_ctor(1, 4, 1);
} else {
 x_48 = x_30;
}
lean_ctor_set(x_48, 0, x_38);
lean_ctor_set(x_48, 1, x_39);
lean_ctor_set(x_48, 2, x_40);
lean_ctor_set(x_48, 3, x_41);
lean_ctor_set_uint8(x_48, sizeof(void*)*4, x_7);
x_49 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_49, 0, x_44);
lean_ctor_set(x_49, 1, x_45);
lean_ctor_set(x_49, 2, x_46);
lean_ctor_set(x_49, 3, x_47);
lean_ctor_set_uint8(x_49, sizeof(void*)*4, x_7);
x_50 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_42);
lean_ctor_set(x_50, 2, x_43);
lean_ctor_set(x_50, 3, x_49);
lean_ctor_set_uint8(x_50, sizeof(void*)*4, x_33);
return x_50;
}
}
case 1:
{
lean_object* x_114; 
lean_dec(x_28);
lean_dec(x_27);
if (lean_is_scalar(x_30)) {
 x_114 = lean_alloc_ctor(1, 4, 1);
} else {
 x_114 = x_30;
}
lean_ctor_set(x_114, 0, x_26);
lean_ctor_set(x_114, 1, x_2);
lean_ctor_set(x_114, 2, x_3);
lean_ctor_set(x_114, 3, x_29);
lean_ctor_set_uint8(x_114, sizeof(void*)*4, x_7);
return x_114;
}
default: 
{
lean_object* x_115; uint8_t x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_115 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_Server_FileWorker_queueRequest_spec__0_spec__0___redArg(x_29, x_2, x_3);
x_116 = lean_ctor_get_uint8(x_115, sizeof(void*)*4);
x_117 = lean_ctor_get(x_115, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_115, 1);
lean_inc(x_118);
x_119 = lean_ctor_get(x_115, 2);
lean_inc(x_119);
x_120 = lean_ctor_get(x_115, 3);
lean_inc(x_120);
if (x_116 == 0)
{
if (lean_obj_tag(x_117) == 0)
{
if (lean_obj_tag(x_120) == 0)
{
uint8_t x_135; 
lean_dec(x_30);
x_135 = !lean_is_exclusive(x_115);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_136 = lean_ctor_get(x_115, 3);
lean_dec(x_136);
x_137 = lean_ctor_get(x_115, 2);
lean_dec(x_137);
x_138 = lean_ctor_get(x_115, 1);
lean_dec(x_138);
x_139 = lean_ctor_get(x_115, 0);
lean_dec(x_139);
lean_ctor_set(x_115, 0, x_120);
x_140 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_140, 0, x_26);
lean_ctor_set(x_140, 1, x_27);
lean_ctor_set(x_140, 2, x_28);
lean_ctor_set(x_140, 3, x_115);
lean_ctor_set_uint8(x_140, sizeof(void*)*4, x_7);
return x_140;
}
else
{
lean_object* x_141; lean_object* x_142; 
lean_dec(x_115);
x_141 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_141, 0, x_120);
lean_ctor_set(x_141, 1, x_118);
lean_ctor_set(x_141, 2, x_119);
lean_ctor_set(x_141, 3, x_120);
lean_ctor_set_uint8(x_141, sizeof(void*)*4, x_116);
x_142 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_142, 0, x_26);
lean_ctor_set(x_142, 1, x_27);
lean_ctor_set(x_142, 2, x_28);
lean_ctor_set(x_142, 3, x_141);
lean_ctor_set_uint8(x_142, sizeof(void*)*4, x_7);
return x_142;
}
}
else
{
uint8_t x_143; 
x_143 = lean_ctor_get_uint8(x_120, sizeof(void*)*4);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_dec(x_115);
x_144 = lean_ctor_get(x_120, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_120, 1);
lean_inc(x_145);
x_146 = lean_ctor_get(x_120, 2);
lean_inc(x_146);
x_147 = lean_ctor_get(x_120, 3);
lean_inc(x_147);
lean_dec(x_120);
x_121 = x_26;
x_122 = x_27;
x_123 = x_28;
x_124 = x_117;
x_125 = x_118;
x_126 = x_119;
x_127 = x_144;
x_128 = x_145;
x_129 = x_146;
x_130 = x_147;
goto block_134;
}
else
{
uint8_t x_148; 
lean_dec(x_119);
lean_dec(x_118);
lean_dec(x_30);
x_148 = !lean_is_exclusive(x_120);
if (x_148 == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_149 = lean_ctor_get(x_120, 3);
lean_dec(x_149);
x_150 = lean_ctor_get(x_120, 2);
lean_dec(x_150);
x_151 = lean_ctor_get(x_120, 1);
lean_dec(x_151);
x_152 = lean_ctor_get(x_120, 0);
lean_dec(x_152);
lean_ctor_set(x_120, 3, x_115);
lean_ctor_set(x_120, 2, x_28);
lean_ctor_set(x_120, 1, x_27);
lean_ctor_set(x_120, 0, x_26);
lean_ctor_set_uint8(x_120, sizeof(void*)*4, x_7);
return x_120;
}
else
{
lean_object* x_153; 
lean_dec(x_120);
x_153 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_153, 0, x_26);
lean_ctor_set(x_153, 1, x_27);
lean_ctor_set(x_153, 2, x_28);
lean_ctor_set(x_153, 3, x_115);
lean_ctor_set_uint8(x_153, sizeof(void*)*4, x_7);
return x_153;
}
}
}
}
else
{
uint8_t x_154; 
x_154 = lean_ctor_get_uint8(x_117, sizeof(void*)*4);
if (x_154 == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
lean_dec(x_115);
x_155 = lean_ctor_get(x_117, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_117, 1);
lean_inc(x_156);
x_157 = lean_ctor_get(x_117, 2);
lean_inc(x_157);
x_158 = lean_ctor_get(x_117, 3);
lean_inc(x_158);
lean_dec(x_117);
x_121 = x_26;
x_122 = x_27;
x_123 = x_28;
x_124 = x_155;
x_125 = x_156;
x_126 = x_157;
x_127 = x_158;
x_128 = x_118;
x_129 = x_119;
x_130 = x_120;
goto block_134;
}
else
{
if (lean_obj_tag(x_120) == 0)
{
uint8_t x_159; 
lean_dec(x_119);
lean_dec(x_118);
lean_dec(x_30);
x_159 = !lean_is_exclusive(x_117);
if (x_159 == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_160 = lean_ctor_get(x_117, 3);
lean_dec(x_160);
x_161 = lean_ctor_get(x_117, 2);
lean_dec(x_161);
x_162 = lean_ctor_get(x_117, 1);
lean_dec(x_162);
x_163 = lean_ctor_get(x_117, 0);
lean_dec(x_163);
lean_ctor_set(x_117, 3, x_115);
lean_ctor_set(x_117, 2, x_28);
lean_ctor_set(x_117, 1, x_27);
lean_ctor_set(x_117, 0, x_26);
lean_ctor_set_uint8(x_117, sizeof(void*)*4, x_7);
return x_117;
}
else
{
lean_object* x_164; 
lean_dec(x_117);
x_164 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_164, 0, x_26);
lean_ctor_set(x_164, 1, x_27);
lean_ctor_set(x_164, 2, x_28);
lean_ctor_set(x_164, 3, x_115);
lean_ctor_set_uint8(x_164, sizeof(void*)*4, x_7);
return x_164;
}
}
else
{
uint8_t x_165; 
x_165 = !lean_is_exclusive(x_115);
if (x_165 == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; 
x_166 = lean_ctor_get(x_115, 3);
lean_dec(x_166);
x_167 = lean_ctor_get(x_115, 2);
lean_dec(x_167);
x_168 = lean_ctor_get(x_115, 1);
lean_dec(x_168);
x_169 = lean_ctor_get(x_115, 0);
lean_dec(x_169);
x_170 = lean_ctor_get_uint8(x_120, sizeof(void*)*4);
if (x_170 == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
lean_free_object(x_115);
x_171 = lean_ctor_get(x_120, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_120, 1);
lean_inc(x_172);
x_173 = lean_ctor_get(x_120, 2);
lean_inc(x_173);
x_174 = lean_ctor_get(x_120, 3);
lean_inc(x_174);
lean_dec(x_120);
x_121 = x_26;
x_122 = x_27;
x_123 = x_28;
x_124 = x_117;
x_125 = x_118;
x_126 = x_119;
x_127 = x_171;
x_128 = x_172;
x_129 = x_173;
x_130 = x_174;
goto block_134;
}
else
{
uint8_t x_175; 
lean_dec(x_30);
x_175 = !lean_is_exclusive(x_117);
if (x_175 == 0)
{
lean_object* x_176; 
lean_ctor_set_uint8(x_117, sizeof(void*)*4, x_170);
x_176 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_176, 0, x_26);
lean_ctor_set(x_176, 1, x_27);
lean_ctor_set(x_176, 2, x_28);
lean_ctor_set(x_176, 3, x_115);
lean_ctor_set_uint8(x_176, sizeof(void*)*4, x_7);
return x_176;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_177 = lean_ctor_get(x_117, 0);
x_178 = lean_ctor_get(x_117, 1);
x_179 = lean_ctor_get(x_117, 2);
x_180 = lean_ctor_get(x_117, 3);
lean_inc(x_180);
lean_inc(x_179);
lean_inc(x_178);
lean_inc(x_177);
lean_dec(x_117);
x_181 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_181, 0, x_177);
lean_ctor_set(x_181, 1, x_178);
lean_ctor_set(x_181, 2, x_179);
lean_ctor_set(x_181, 3, x_180);
lean_ctor_set_uint8(x_181, sizeof(void*)*4, x_170);
lean_ctor_set(x_115, 0, x_181);
x_182 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_182, 0, x_26);
lean_ctor_set(x_182, 1, x_27);
lean_ctor_set(x_182, 2, x_28);
lean_ctor_set(x_182, 3, x_115);
lean_ctor_set_uint8(x_182, sizeof(void*)*4, x_7);
return x_182;
}
}
}
else
{
uint8_t x_183; 
lean_dec(x_115);
x_183 = lean_ctor_get_uint8(x_120, sizeof(void*)*4);
if (x_183 == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_184 = lean_ctor_get(x_120, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_120, 1);
lean_inc(x_185);
x_186 = lean_ctor_get(x_120, 2);
lean_inc(x_186);
x_187 = lean_ctor_get(x_120, 3);
lean_inc(x_187);
lean_dec(x_120);
x_121 = x_26;
x_122 = x_27;
x_123 = x_28;
x_124 = x_117;
x_125 = x_118;
x_126 = x_119;
x_127 = x_184;
x_128 = x_185;
x_129 = x_186;
x_130 = x_187;
goto block_134;
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
lean_dec(x_30);
x_188 = lean_ctor_get(x_117, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_117, 1);
lean_inc(x_189);
x_190 = lean_ctor_get(x_117, 2);
lean_inc(x_190);
x_191 = lean_ctor_get(x_117, 3);
lean_inc(x_191);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 lean_ctor_release(x_117, 2);
 lean_ctor_release(x_117, 3);
 x_192 = x_117;
} else {
 lean_dec_ref(x_117);
 x_192 = lean_box(0);
}
if (lean_is_scalar(x_192)) {
 x_193 = lean_alloc_ctor(1, 4, 1);
} else {
 x_193 = x_192;
}
lean_ctor_set(x_193, 0, x_188);
lean_ctor_set(x_193, 1, x_189);
lean_ctor_set(x_193, 2, x_190);
lean_ctor_set(x_193, 3, x_191);
lean_ctor_set_uint8(x_193, sizeof(void*)*4, x_183);
x_194 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_194, 1, x_118);
lean_ctor_set(x_194, 2, x_119);
lean_ctor_set(x_194, 3, x_120);
lean_ctor_set_uint8(x_194, sizeof(void*)*4, x_116);
x_195 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_195, 0, x_26);
lean_ctor_set(x_195, 1, x_27);
lean_ctor_set(x_195, 2, x_28);
lean_ctor_set(x_195, 3, x_194);
lean_ctor_set_uint8(x_195, sizeof(void*)*4, x_7);
return x_195;
}
}
}
}
}
}
else
{
lean_object* x_196; 
lean_dec(x_120);
lean_dec(x_119);
lean_dec(x_118);
lean_dec(x_117);
lean_dec(x_30);
x_196 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_196, 0, x_26);
lean_ctor_set(x_196, 1, x_27);
lean_ctor_set(x_196, 2, x_28);
lean_ctor_set(x_196, 3, x_115);
lean_ctor_set_uint8(x_196, sizeof(void*)*4, x_7);
return x_196;
}
block_134:
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
if (lean_is_scalar(x_30)) {
 x_131 = lean_alloc_ctor(1, 4, 1);
} else {
 x_131 = x_30;
}
lean_ctor_set(x_131, 0, x_121);
lean_ctor_set(x_131, 1, x_122);
lean_ctor_set(x_131, 2, x_123);
lean_ctor_set(x_131, 3, x_124);
lean_ctor_set_uint8(x_131, sizeof(void*)*4, x_7);
x_132 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_132, 0, x_127);
lean_ctor_set(x_132, 1, x_128);
lean_ctor_set(x_132, 2, x_129);
lean_ctor_set(x_132, 3, x_130);
lean_ctor_set_uint8(x_132, sizeof(void*)*4, x_7);
x_133 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_125);
lean_ctor_set(x_133, 2, x_126);
lean_ctor_set(x_133, 3, x_132);
lean_ctor_set_uint8(x_133, sizeof(void*)*4, x_116);
return x_133;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_Server_FileWorker_queueRequest_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_Server_FileWorker_queueRequest_spec__0_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at___Lean_Server_FileWorker_queueRequest_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_RBNode_isRed___redArg(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_Server_FileWorker_queueRequest_spec__0_spec__0___redArg(x_1, x_2, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_Server_FileWorker_queueRequest_spec__0_spec__0___redArg(x_1, x_2, x_3);
x_7 = l_Lean_RBNode_setBlack___redArg(x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at___Lean_Server_FileWorker_queueRequest_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_insert___at___Lean_Server_FileWorker_queueRequest_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_queueRequest___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_insert___at___Lean_Server_FileWorker_queueRequest_spec__0___redArg(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_queueRequest___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_queueRequest___redArg___lam__0), 3, 2);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
x_6 = l_Lean_Server_FileWorker_updatePendingRequests___redArg(x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_queueRequest(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Server_FileWorker_queueRequest___redArg(x_1, x_2, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_queueRequest___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_FileWorker_queueRequest___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_queueRequest___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Server_FileWorker_queueRequest(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleImportCompletionRequest___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_ImportCompletion_collectAvailableImports(x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_io_mono_ms_now(x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_ctor_get(x_14, 2);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_ImportCompletion_find(x_2, x_15, x_3, x_8);
x_17 = lean_ctor_get(x_4, 0);
lean_inc(x_17);
lean_dec(x_4);
x_18 = l___private_Lean_Data_Lsp_LanguageFeatures_0__Lean_Lsp_toJsonCompletionList____x40_Lean_Data_Lsp_LanguageFeatures___hyg_2889_(x_16);
lean_ctor_set_tag(x_10, 2);
lean_ctor_set(x_10, 1, x_18);
lean_ctor_set(x_10, 0, x_5);
x_19 = l_Std_Channel_Sync_send___redArg(x_17, x_10, x_13);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_8);
lean_ctor_set(x_22, 1, x_12);
lean_ctor_set(x_19, 0, x_22);
return x_19;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_dec(x_19);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_8);
lean_ctor_set(x_24, 1, x_12);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_26 = lean_ctor_get(x_10, 0);
x_27 = lean_ctor_get(x_10, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_10);
x_28 = lean_ctor_get(x_1, 1);
lean_inc(x_28);
lean_dec(x_1);
x_29 = lean_ctor_get(x_28, 2);
lean_inc(x_29);
lean_dec(x_28);
x_30 = l_ImportCompletion_find(x_2, x_29, x_3, x_8);
x_31 = lean_ctor_get(x_4, 0);
lean_inc(x_31);
lean_dec(x_4);
x_32 = l___private_Lean_Data_Lsp_LanguageFeatures_0__Lean_Lsp_toJsonCompletionList____x40_Lean_Data_Lsp_LanguageFeatures___hyg_2889_(x_30);
x_33 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_33, 0, x_5);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_Std_Channel_Sync_send___redArg(x_31, x_33, x_27);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_36 = x_34;
} else {
 lean_dec_ref(x_34);
 x_36 = lean_box(0);
}
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_8);
lean_ctor_set(x_37, 1, x_26);
if (lean_is_scalar(x_36)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_36;
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_35);
return x_38;
}
}
else
{
uint8_t x_39; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_7);
if (x_39 == 0)
{
return x_7;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_7, 0);
x_41 = lean_ctor_get(x_7, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_7);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleImportCompletionRequest___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_IO_ofExcept___at___IO_Process_output_spec__0___redArg(x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_13 = x_9;
} else {
 lean_dec_ref(x_9);
 x_13 = lean_box(0);
}
x_14 = lean_io_mono_ms_now(x_10);
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
x_34 = lean_unsigned_to_nat(10000u);
x_35 = lean_nat_sub(x_15, x_12);
lean_dec(x_12);
x_36 = lean_nat_dec_le(x_34, x_35);
lean_dec(x_35);
if (x_36 == 0)
{
x_18 = x_11;
x_19 = x_16;
goto block_33;
}
else
{
lean_object* x_37; 
lean_dec(x_11);
x_37 = l_ImportCompletion_collectAvailableImports(x_16);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_18 = x_38;
x_19 = x_39;
goto block_33;
}
else
{
uint8_t x_40; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_37);
if (x_40 == 0)
{
return x_37;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_37, 0);
x_42 = lean_ctor_get(x_37, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_37);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
block_33:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
lean_dec(x_1);
x_21 = lean_ctor_get(x_20, 2);
lean_inc(x_21);
lean_dec(x_20);
x_22 = l_ImportCompletion_find(x_2, x_21, x_3, x_18);
x_23 = lean_ctor_get(x_4, 0);
lean_inc(x_23);
lean_dec(x_4);
x_24 = l___private_Lean_Data_Lsp_LanguageFeatures_0__Lean_Lsp_toJsonCompletionList____x40_Lean_Data_Lsp_LanguageFeatures___hyg_2889_(x_22);
if (lean_is_scalar(x_17)) {
 x_25 = lean_alloc_ctor(2, 2, 0);
} else {
 x_25 = x_17;
 lean_ctor_set_tag(x_25, 2);
}
lean_ctor_set(x_25, 0, x_5);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Std_Channel_Sync_send___redArg(x_23, x_25, x_19);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
if (lean_is_scalar(x_13)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_13;
}
lean_ctor_set(x_29, 0, x_18);
lean_ctor_set(x_29, 1, x_15);
lean_ctor_set(x_26, 0, x_29);
return x_26;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_26, 1);
lean_inc(x_30);
lean_dec(x_26);
if (lean_is_scalar(x_13)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_13;
}
lean_ctor_set(x_31, 0, x_18);
lean_ctor_set(x_31, 1, x_15);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
}
else
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleImportCompletionRequest(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_st_ref_get(x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_7, 2);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_12, 3);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_handleImportCompletionRequest___lam__0___boxed), 6, 5);
lean_closure_set(x_14, 0, x_11);
lean_closure_set(x_14, 1, x_13);
lean_closure_set(x_14, 2, x_2);
lean_closure_set(x_14, 3, x_3);
lean_closure_set(x_14, 4, x_1);
x_15 = l_Lean_Server_ServerTask_IO_asTask(lean_box(0), x_14, x_9);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
return x_15;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_15);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_20 = lean_ctor_get(x_6, 1);
lean_inc(x_20);
lean_dec(x_6);
x_21 = lean_ctor_get(x_7, 0);
lean_inc(x_21);
lean_dec(x_7);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_23, 3);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_ctor_get(x_8, 0);
lean_inc(x_25);
lean_dec(x_8);
x_26 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_handleImportCompletionRequest___lam__1___boxed), 7, 5);
lean_closure_set(x_26, 0, x_22);
lean_closure_set(x_26, 1, x_24);
lean_closure_set(x_26, 2, x_2);
lean_closure_set(x_26, 3, x_3);
lean_closure_set(x_26, 4, x_1);
x_27 = l_Lean_Server_ServerTask_IO_mapTaskCostly(lean_box(0), lean_box(0), x_26, x_25, x_20);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
return x_27;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_27);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleImportCompletionRequest___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Server_FileWorker_handleImportCompletionRequest___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleImportCompletionRequest___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Server_FileWorker_handleImportCompletionRequest___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleImportCompletionRequest___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Server_FileWorker_handleImportCompletionRequest(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_parseParams___at___Lean_Server_FileWorker_handleStatefulPreRequestSpecialCases_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc(x_1);
x_3 = l___private_Lean_Data_Lsp_LanguageFeatures_0__Lean_Lsp_fromJsonCompletionParams____x40_Lean_Data_Lsp_LanguageFeatures___hyg_2953_(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_mk_string_unchecked("Got param with wrong structure: ", 32, 32);
x_6 = l_Lean_Json_compress(x_1);
x_7 = lean_string_append(x_5, x_6);
lean_dec(x_6);
x_8 = lean_mk_string_unchecked("\n", 1, 1);
x_9 = lean_string_append(x_7, x_8);
lean_dec(x_8);
x_10 = lean_string_append(x_9, x_4);
lean_dec(x_4);
x_11 = l_IO_throwServerError(lean_box(0), x_10, x_2);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_1);
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_2);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_parseParams___at___Lean_Server_FileWorker_handleStatefulPreRequestSpecialCases_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_FileWorker_parseParams___at___Lean_Server_FileWorker_handleStatefulPreRequestSpecialCases_spec__0___redArg(x_1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_parseParams___at___Lean_Server_FileWorker_handleStatefulPreRequestSpecialCases_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc(x_1);
x_3 = l___private_Lean_Data_Lsp_Extra_0__Lean_Lsp_fromJsonRpcConnectParams____x40_Lean_Data_Lsp_Extra___hyg_1992_(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_mk_string_unchecked("Got param with wrong structure: ", 32, 32);
x_6 = l_Lean_Json_compress(x_1);
x_7 = lean_string_append(x_5, x_6);
lean_dec(x_6);
x_8 = lean_mk_string_unchecked("\n", 1, 1);
x_9 = lean_string_append(x_7, x_8);
lean_dec(x_8);
x_10 = lean_string_append(x_9, x_4);
lean_dec(x_4);
x_11 = l_IO_throwServerError(lean_box(0), x_10, x_2);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_1);
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_2);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_parseParams___at___Lean_Server_FileWorker_handleStatefulPreRequestSpecialCases_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_FileWorker_parseParams___at___Lean_Server_FileWorker_handleStatefulPreRequestSpecialCases_spec__1___redArg(x_1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleStatefulPreRequestSpecialCases(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_23; uint8_t x_24; 
x_23 = lean_st_ref_get(x_5, x_6);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_23, 1);
x_27 = lean_mk_string_unchecked("$/lean/rpc/connect", 18, 18);
x_28 = lean_string_dec_eq(x_2, x_27);
lean_dec(x_27);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_mk_string_unchecked("textDocument/completion", 23, 23);
x_30 = lean_string_dec_eq(x_2, x_29);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; 
lean_dec(x_25);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_31 = lean_box(x_30);
lean_ctor_set(x_23, 0, x_31);
return x_23;
}
else
{
lean_object* x_32; 
lean_free_object(x_23);
x_32 = l_Lean_Server_FileWorker_parseParams___at___Lean_Server_FileWorker_handleStatefulPreRequestSpecialCases_spec__0___redArg(x_3, x_26);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = lean_ctor_get(x_32, 1);
x_36 = lean_ctor_get(x_25, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_38, 3);
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_41 = lean_ctor_get(x_40, 2);
lean_inc(x_41);
lean_dec(x_40);
lean_inc(x_34);
x_42 = l_ImportCompletion_isImportCompletionRequest(x_39, x_41, x_34);
lean_dec(x_41);
lean_dec(x_39);
if (x_42 == 0)
{
lean_object* x_43; 
lean_dec(x_36);
lean_dec(x_34);
lean_dec(x_25);
lean_dec(x_4);
lean_dec(x_1);
x_43 = lean_box(x_42);
lean_ctor_set(x_32, 0, x_43);
return x_32;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
lean_free_object(x_32);
x_44 = l_Lean_Server_FileWorker_handleImportCompletionRequest(x_1, x_34, x_4, x_5, x_35);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_ctor_get(x_25, 1);
lean_inc(x_47);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_45);
x_49 = lean_ctor_get(x_25, 3);
lean_inc(x_49);
x_50 = lean_ctor_get(x_25, 4);
lean_inc(x_50);
lean_dec(x_25);
x_51 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_51, 0, x_36);
lean_ctor_set(x_51, 1, x_47);
lean_ctor_set(x_51, 2, x_48);
lean_ctor_set(x_51, 3, x_49);
lean_ctor_set(x_51, 4, x_50);
x_52 = lean_st_ref_set(x_5, x_51, x_46);
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_52, 0);
lean_dec(x_54);
x_55 = lean_box(x_42);
lean_ctor_set(x_52, 0, x_55);
return x_52;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_52, 1);
lean_inc(x_56);
lean_dec(x_52);
x_57 = lean_box(x_42);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_56);
return x_58;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_59 = lean_ctor_get(x_32, 0);
x_60 = lean_ctor_get(x_32, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_32);
x_61 = lean_ctor_get(x_25, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_63, 3);
lean_inc(x_64);
lean_dec(x_63);
x_65 = lean_ctor_get(x_62, 1);
lean_inc(x_65);
lean_dec(x_62);
x_66 = lean_ctor_get(x_65, 2);
lean_inc(x_66);
lean_dec(x_65);
lean_inc(x_59);
x_67 = l_ImportCompletion_isImportCompletionRequest(x_64, x_66, x_59);
lean_dec(x_66);
lean_dec(x_64);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; 
lean_dec(x_61);
lean_dec(x_59);
lean_dec(x_25);
lean_dec(x_4);
lean_dec(x_1);
x_68 = lean_box(x_67);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_60);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_70 = l_Lean_Server_FileWorker_handleImportCompletionRequest(x_1, x_59, x_4, x_5, x_60);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = lean_ctor_get(x_25, 1);
lean_inc(x_73);
x_74 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_74, 0, x_71);
x_75 = lean_ctor_get(x_25, 3);
lean_inc(x_75);
x_76 = lean_ctor_get(x_25, 4);
lean_inc(x_76);
lean_dec(x_25);
x_77 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_77, 0, x_61);
lean_ctor_set(x_77, 1, x_73);
lean_ctor_set(x_77, 2, x_74);
lean_ctor_set(x_77, 3, x_75);
lean_ctor_set(x_77, 4, x_76);
x_78 = lean_st_ref_set(x_5, x_77, x_72);
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_80 = x_78;
} else {
 lean_dec_ref(x_78);
 x_80 = lean_box(0);
}
x_81 = lean_box(x_67);
if (lean_is_scalar(x_80)) {
 x_82 = lean_alloc_ctor(0, 2, 0);
} else {
 x_82 = x_80;
}
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_79);
return x_82;
}
}
}
else
{
lean_object* x_83; lean_object* x_84; 
lean_dec(x_25);
x_83 = lean_ctor_get(x_32, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_32, 1);
lean_inc(x_84);
lean_dec(x_32);
x_7 = x_83;
x_8 = x_84;
goto block_22;
}
}
}
else
{
lean_object* x_85; 
lean_free_object(x_23);
lean_dec(x_25);
x_85 = l_Lean_Server_FileWorker_parseParams___at___Lean_Server_FileWorker_handleStatefulPreRequestSpecialCases_spec__1___redArg(x_3, x_26);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
lean_dec(x_85);
x_87 = l_Lean_Server_FileWorker_handleRpcConnect___redArg(x_5, x_86);
if (lean_obj_tag(x_87) == 0)
{
uint8_t x_88; 
x_88 = !lean_is_exclusive(x_87);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; uint64_t x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_89 = lean_ctor_get(x_87, 0);
x_90 = lean_ctor_get(x_87, 1);
x_91 = lean_ctor_get(x_4, 0);
lean_inc(x_91);
lean_dec(x_4);
x_92 = lean_unbox_uint64(x_89);
lean_dec(x_89);
x_93 = l___private_Lean_Data_Lsp_Extra_0__Lean_Lsp_toJsonRpcConnected____x40_Lean_Data_Lsp_Extra___hyg_2176_(x_92);
lean_ctor_set_tag(x_87, 2);
lean_ctor_set(x_87, 1, x_93);
lean_ctor_set(x_87, 0, x_1);
x_94 = l_Std_Channel_Sync_send___redArg(x_91, x_87, x_90);
x_95 = !lean_is_exclusive(x_94);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_94, 0);
lean_dec(x_96);
x_97 = lean_box(x_28);
lean_ctor_set(x_94, 0, x_97);
return x_94;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_94, 1);
lean_inc(x_98);
lean_dec(x_94);
x_99 = lean_box(x_28);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_98);
return x_100;
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; uint64_t x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_101 = lean_ctor_get(x_87, 0);
x_102 = lean_ctor_get(x_87, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_87);
x_103 = lean_ctor_get(x_4, 0);
lean_inc(x_103);
lean_dec(x_4);
x_104 = lean_unbox_uint64(x_101);
lean_dec(x_101);
x_105 = l___private_Lean_Data_Lsp_Extra_0__Lean_Lsp_toJsonRpcConnected____x40_Lean_Data_Lsp_Extra___hyg_2176_(x_104);
x_106 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_106, 0, x_1);
lean_ctor_set(x_106, 1, x_105);
x_107 = l_Std_Channel_Sync_send___redArg(x_103, x_106, x_102);
x_108 = lean_ctor_get(x_107, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_109 = x_107;
} else {
 lean_dec_ref(x_107);
 x_109 = lean_box(0);
}
x_110 = lean_box(x_28);
if (lean_is_scalar(x_109)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_109;
}
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_108);
return x_111;
}
}
else
{
lean_object* x_112; lean_object* x_113; 
x_112 = lean_ctor_get(x_87, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_87, 1);
lean_inc(x_113);
lean_dec(x_87);
x_7 = x_112;
x_8 = x_113;
goto block_22;
}
}
else
{
lean_object* x_114; lean_object* x_115; 
x_114 = lean_ctor_get(x_85, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_85, 1);
lean_inc(x_115);
lean_dec(x_85);
x_7 = x_114;
x_8 = x_115;
goto block_22;
}
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; 
x_116 = lean_ctor_get(x_23, 0);
x_117 = lean_ctor_get(x_23, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_23);
x_118 = lean_mk_string_unchecked("$/lean/rpc/connect", 18, 18);
x_119 = lean_string_dec_eq(x_2, x_118);
lean_dec(x_118);
if (x_119 == 0)
{
lean_object* x_120; uint8_t x_121; 
x_120 = lean_mk_string_unchecked("textDocument/completion", 23, 23);
x_121 = lean_string_dec_eq(x_2, x_120);
lean_dec(x_120);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; 
lean_dec(x_116);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_122 = lean_box(x_121);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_117);
return x_123;
}
else
{
lean_object* x_124; 
x_124 = l_Lean_Server_FileWorker_parseParams___at___Lean_Server_FileWorker_handleStatefulPreRequestSpecialCases_spec__0___redArg(x_3, x_117);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; uint8_t x_134; 
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_124, 1);
lean_inc(x_126);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_127 = x_124;
} else {
 lean_dec_ref(x_124);
 x_127 = lean_box(0);
}
x_128 = lean_ctor_get(x_116, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_130, 3);
lean_inc(x_131);
lean_dec(x_130);
x_132 = lean_ctor_get(x_129, 1);
lean_inc(x_132);
lean_dec(x_129);
x_133 = lean_ctor_get(x_132, 2);
lean_inc(x_133);
lean_dec(x_132);
lean_inc(x_125);
x_134 = l_ImportCompletion_isImportCompletionRequest(x_131, x_133, x_125);
lean_dec(x_133);
lean_dec(x_131);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; 
lean_dec(x_128);
lean_dec(x_125);
lean_dec(x_116);
lean_dec(x_4);
lean_dec(x_1);
x_135 = lean_box(x_134);
if (lean_is_scalar(x_127)) {
 x_136 = lean_alloc_ctor(0, 2, 0);
} else {
 x_136 = x_127;
}
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_126);
return x_136;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
lean_dec(x_127);
x_137 = l_Lean_Server_FileWorker_handleImportCompletionRequest(x_1, x_125, x_4, x_5, x_126);
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_137, 1);
lean_inc(x_139);
lean_dec(x_137);
x_140 = lean_ctor_get(x_116, 1);
lean_inc(x_140);
x_141 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_141, 0, x_138);
x_142 = lean_ctor_get(x_116, 3);
lean_inc(x_142);
x_143 = lean_ctor_get(x_116, 4);
lean_inc(x_143);
lean_dec(x_116);
x_144 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_144, 0, x_128);
lean_ctor_set(x_144, 1, x_140);
lean_ctor_set(x_144, 2, x_141);
lean_ctor_set(x_144, 3, x_142);
lean_ctor_set(x_144, 4, x_143);
x_145 = lean_st_ref_set(x_5, x_144, x_139);
x_146 = lean_ctor_get(x_145, 1);
lean_inc(x_146);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 x_147 = x_145;
} else {
 lean_dec_ref(x_145);
 x_147 = lean_box(0);
}
x_148 = lean_box(x_134);
if (lean_is_scalar(x_147)) {
 x_149 = lean_alloc_ctor(0, 2, 0);
} else {
 x_149 = x_147;
}
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_146);
return x_149;
}
}
else
{
lean_object* x_150; lean_object* x_151; 
lean_dec(x_116);
x_150 = lean_ctor_get(x_124, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_124, 1);
lean_inc(x_151);
lean_dec(x_124);
x_7 = x_150;
x_8 = x_151;
goto block_22;
}
}
}
else
{
lean_object* x_152; 
lean_dec(x_116);
x_152 = l_Lean_Server_FileWorker_parseParams___at___Lean_Server_FileWorker_handleStatefulPreRequestSpecialCases_spec__1___redArg(x_3, x_117);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; lean_object* x_154; 
x_153 = lean_ctor_get(x_152, 1);
lean_inc(x_153);
lean_dec(x_152);
x_154 = l_Lean_Server_FileWorker_handleRpcConnect___redArg(x_5, x_153);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint64_t x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_154, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 x_157 = x_154;
} else {
 lean_dec_ref(x_154);
 x_157 = lean_box(0);
}
x_158 = lean_ctor_get(x_4, 0);
lean_inc(x_158);
lean_dec(x_4);
x_159 = lean_unbox_uint64(x_155);
lean_dec(x_155);
x_160 = l___private_Lean_Data_Lsp_Extra_0__Lean_Lsp_toJsonRpcConnected____x40_Lean_Data_Lsp_Extra___hyg_2176_(x_159);
if (lean_is_scalar(x_157)) {
 x_161 = lean_alloc_ctor(2, 2, 0);
} else {
 x_161 = x_157;
 lean_ctor_set_tag(x_161, 2);
}
lean_ctor_set(x_161, 0, x_1);
lean_ctor_set(x_161, 1, x_160);
x_162 = l_Std_Channel_Sync_send___redArg(x_158, x_161, x_156);
x_163 = lean_ctor_get(x_162, 1);
lean_inc(x_163);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 lean_ctor_release(x_162, 1);
 x_164 = x_162;
} else {
 lean_dec_ref(x_162);
 x_164 = lean_box(0);
}
x_165 = lean_box(x_119);
if (lean_is_scalar(x_164)) {
 x_166 = lean_alloc_ctor(0, 2, 0);
} else {
 x_166 = x_164;
}
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_166, 1, x_163);
return x_166;
}
else
{
lean_object* x_167; lean_object* x_168; 
x_167 = lean_ctor_get(x_154, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_154, 1);
lean_inc(x_168);
lean_dec(x_154);
x_7 = x_167;
x_8 = x_168;
goto block_22;
}
}
else
{
lean_object* x_169; lean_object* x_170; 
x_169 = lean_ctor_get(x_152, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_152, 1);
lean_inc(x_170);
lean_dec(x_152);
x_7 = x_169;
x_8 = x_170;
goto block_22;
}
}
}
block_22:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
lean_dec(x_4);
x_10 = lean_box(4);
x_11 = lean_io_error_to_string(x_7);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_11);
lean_ctor_set(x_13, 2, x_12);
x_14 = lean_unbox(x_10);
lean_ctor_set_uint8(x_13, sizeof(void*)*3, x_14);
x_15 = l_Std_Channel_Sync_send___redArg(x_9, x_13, x_8);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
x_18 = lean_box(1);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_box(1);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_parseParams___at___Lean_Server_FileWorker_handleStatefulPreRequestSpecialCases_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_FileWorker_parseParams___at___Lean_Server_FileWorker_handleStatefulPreRequestSpecialCases_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_parseParams___at___Lean_Server_FileWorker_handleStatefulPreRequestSpecialCases_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_FileWorker_parseParams___at___Lean_Server_FileWorker_handleStatefulPreRequestSpecialCases_spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleStatefulPreRequestSpecialCases___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Server_FileWorker_handleStatefulPreRequestSpecialCases(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Server_FileWorker_handleGetInteractiveDiagnosticsRequest_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_12; 
x_12 = lean_usize_dec_eq(x_3, x_4);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; uint8_t x_15; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_13 = lean_array_uget(x_2, x_3);
x_18 = l_Lean_Lsp_DiagnosticWith_fullRange(lean_box(0), x_13);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
x_32 = lean_ctor_get(x_18, 1);
lean_inc(x_32);
lean_dec(x_18);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
x_34 = lean_unsigned_to_nat(0u);
x_35 = lean_nat_dec_eq(x_33, x_34);
lean_dec(x_33);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_32, 0);
lean_inc(x_36);
lean_dec(x_32);
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_nat_add(x_36, x_37);
lean_dec(x_36);
x_21 = x_38;
goto block_31;
}
else
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_32, 0);
lean_inc(x_39);
lean_dec(x_32);
x_21 = x_39;
goto block_31;
}
block_17:
{
if (x_14 == 0)
{
lean_dec(x_13);
x_6 = x_5;
goto block_11;
}
else
{
if (x_15 == 0)
{
lean_dec(x_13);
x_6 = x_5;
goto block_11;
}
else
{
lean_object* x_16; 
x_16 = lean_array_push(x_5, x_13);
x_6 = x_16;
goto block_11;
}
}
}
block_31:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_22; 
lean_dec(x_21);
lean_dec(x_20);
x_22 = lean_array_push(x_5, x_13);
x_6 = x_22;
goto block_11;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; 
x_23 = lean_ctor_get(x_1, 0);
x_24 = lean_ctor_get(x_23, 0);
x_25 = lean_ctor_get(x_23, 1);
x_26 = lean_nat_dec_lt(x_24, x_21);
lean_dec(x_21);
x_27 = lean_nat_dec_le(x_20, x_24);
x_28 = lean_nat_dec_le(x_24, x_20);
if (x_28 == 0)
{
lean_dec(x_20);
x_14 = x_27;
x_15 = x_26;
goto block_17;
}
else
{
uint8_t x_29; 
x_29 = lean_nat_dec_lt(x_20, x_25);
lean_dec(x_20);
if (x_29 == 0)
{
x_14 = x_27;
x_15 = x_26;
goto block_17;
}
else
{
lean_object* x_30; 
x_30 = lean_array_push(x_5, x_13);
x_6 = x_30;
goto block_11;
}
}
}
}
}
else
{
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
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleGetInteractiveDiagnosticsRequest(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_5 = l_Lean_Server_RequestM_readDoc___at___Lean_Server_RequestM_withWaitFindSnapAtPos_spec__0(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_1, 3);
x_9 = lean_st_ref_get(x_8, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_6, 0);
lean_inc(x_12);
lean_dec(x_6);
x_13 = lean_ctor_get(x_12, 3);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_st_ref_get(x_13, x_11);
lean_dec(x_13);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = l_Array_append(lean_box(0), x_10, x_16);
lean_dec(x_16);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_array_get_size(x_17);
x_20 = lean_mk_empty_array_with_capacity(x_18);
x_21 = lean_nat_dec_lt(x_18, x_19);
if (x_21 == 0)
{
lean_dec(x_19);
lean_dec(x_17);
lean_ctor_set(x_14, 0, x_20);
return x_14;
}
else
{
uint8_t x_22; 
x_22 = lean_nat_dec_le(x_19, x_19);
if (x_22 == 0)
{
lean_dec(x_19);
lean_dec(x_17);
lean_ctor_set(x_14, 0, x_20);
return x_14;
}
else
{
size_t x_23; size_t x_24; lean_object* x_25; 
x_23 = lean_usize_of_nat(x_18);
x_24 = lean_usize_of_nat(x_19);
lean_dec(x_19);
x_25 = l_Array_foldlMUnsafe_fold___at___Lean_Server_FileWorker_handleGetInteractiveDiagnosticsRequest_spec__0(x_2, x_17, x_23, x_24, x_20);
lean_dec(x_17);
lean_ctor_set(x_14, 0, x_25);
return x_14;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_26 = lean_ctor_get(x_14, 0);
x_27 = lean_ctor_get(x_14, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_14);
x_28 = l_Array_append(lean_box(0), x_10, x_26);
lean_dec(x_26);
x_29 = lean_unsigned_to_nat(0u);
x_30 = lean_array_get_size(x_28);
x_31 = lean_mk_empty_array_with_capacity(x_29);
x_32 = lean_nat_dec_lt(x_29, x_30);
if (x_32 == 0)
{
lean_object* x_33; 
lean_dec(x_30);
lean_dec(x_28);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_27);
return x_33;
}
else
{
uint8_t x_34; 
x_34 = lean_nat_dec_le(x_30, x_30);
if (x_34 == 0)
{
lean_object* x_35; 
lean_dec(x_30);
lean_dec(x_28);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_31);
lean_ctor_set(x_35, 1, x_27);
return x_35;
}
else
{
size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_usize_of_nat(x_29);
x_37 = lean_usize_of_nat(x_30);
lean_dec(x_30);
x_38 = l_Array_foldlMUnsafe_fold___at___Lean_Server_FileWorker_handleGetInteractiveDiagnosticsRequest_spec__0(x_2, x_28, x_36, x_37, x_31);
lean_dec(x_28);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_27);
return x_39;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Server_FileWorker_handleGetInteractiveDiagnosticsRequest_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at___Lean_Server_FileWorker_handleGetInteractiveDiagnosticsRequest_spec__0(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleGetInteractiveDiagnosticsRequest___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_FileWorker_handleGetInteractiveDiagnosticsRequest(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams___at___Lean_Server_RequestM_parseRequestParams___at___Lean_Server_FileWorker_handlePreRequestSpecialCases_x3f_spec__0_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
lean_inc(x_1);
x_2 = l___private_Lean_Server_FileWorker_WidgetRequests_0__Lean_Widget_fromJsonGetInteractiveDiagnosticsParams____x40_Lean_Server_FileWorker_WidgetRequests___hyg_1658_(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_box(3);
x_6 = lean_mk_string_unchecked("Cannot parse request params: ", 29, 29);
x_7 = l_Lean_Json_compress(x_1);
x_8 = lean_string_append(x_6, x_7);
lean_dec(x_7);
x_9 = lean_mk_string_unchecked("\n", 1, 1);
x_10 = lean_string_append(x_8, x_9);
lean_dec(x_9);
x_11 = lean_string_append(x_10, x_4);
lean_dec(x_4);
x_12 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_unbox(x_5);
lean_ctor_set_uint8(x_12, sizeof(void*)*1, x_13);
lean_ctor_set(x_2, 0, x_12);
return x_2;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
lean_dec(x_2);
x_15 = lean_box(3);
x_16 = lean_mk_string_unchecked("Cannot parse request params: ", 29, 29);
x_17 = l_Lean_Json_compress(x_1);
x_18 = lean_string_append(x_16, x_17);
lean_dec(x_17);
x_19 = lean_mk_string_unchecked("\n", 1, 1);
x_20 = lean_string_append(x_18, x_19);
lean_dec(x_19);
x_21 = lean_string_append(x_20, x_14);
lean_dec(x_14);
x_22 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_unbox(x_15);
lean_ctor_set_uint8(x_22, sizeof(void*)*1, x_23);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_22);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_2);
if (x_25 == 0)
{
return x_2;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_2, 0);
lean_inc(x_26);
lean_dec(x_2);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___Lean_Server_FileWorker_handlePreRequestSpecialCases_x3f_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Server_parseRequestParams___at___Lean_Server_RequestM_parseRequestParams___at___Lean_Server_FileWorker_handlePreRequestSpecialCases_x3f_spec__0_spec__0(x_1);
x_4 = l_EIO_ofExcept(lean_box(0), lean_box(0), x_3, x_2);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___Lean_Server_FileWorker_handlePreRequestSpecialCases_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_RequestM_parseRequestParams___at___Lean_Server_FileWorker_handlePreRequestSpecialCases_x3f_spec__0___redArg(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Widget_instRpcEncodableDiagnosticWith_enc____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853____at___Lean_Server_FileWorker_handlePreRequestSpecialCases_x3f_spec__2_spec__2(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_7 = lean_array_uget(x_3, x_2);
x_8 = lean_box(0);
x_9 = lean_array_uset(x_3, x_2, x_8);
x_10 = l___private_Lean_Data_Lsp_Diagnostics_0__Lean_Lsp_toJsonDiagnosticRelatedInformation____x40_Lean_Data_Lsp_Diagnostics___hyg_1088_(x_7);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_usize_of_nat(x_11);
x_13 = lean_usize_add(x_2, x_12);
x_14 = lean_array_uset(x_9, x_2, x_10);
x_2 = x_13;
x_3 = x_14;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Widget_instRpcEncodableDiagnosticWith_enc____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853____at___Lean_Server_FileWorker_handlePreRequestSpecialCases_x3f_spec__2_spec__3(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_18; 
x_7 = lean_array_uget(x_3, x_2);
x_8 = lean_box(0);
x_9 = lean_array_uset(x_3, x_2, x_8);
x_18 = lean_unbox(x_7);
lean_dec(x_7);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = l_Lean_JsonNumber_fromNat(x_19);
x_21 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_10 = x_21;
x_11 = x_4;
goto block_17;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_unsigned_to_nat(2u);
x_23 = l_Lean_JsonNumber_fromNat(x_22);
x_24 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_10 = x_24;
x_11 = x_4;
goto block_17;
}
block_17:
{
lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_usize_of_nat(x_12);
x_14 = lean_usize_add(x_2, x_13);
x_15 = lean_array_uset(x_9, x_2, x_10);
x_2 = x_14;
x_3 = x_15;
x_4 = x_11;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Widget_instRpcEncodableDiagnosticWith_enc____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853____at___Lean_Server_FileWorker_handlePreRequestSpecialCases_x3f_spec__2_spec__4(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_18; 
x_7 = lean_array_uget(x_3, x_2);
x_8 = lean_box(0);
x_9 = lean_array_uset(x_3, x_2, x_8);
x_18 = lean_unbox(x_7);
lean_dec(x_7);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = l_Lean_JsonNumber_fromNat(x_19);
x_21 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_10 = x_21;
x_11 = x_4;
goto block_17;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_unsigned_to_nat(2u);
x_23 = l_Lean_JsonNumber_fromNat(x_22);
x_24 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_10 = x_24;
x_11 = x_4;
goto block_17;
}
block_17:
{
lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_usize_of_nat(x_12);
x_14 = lean_usize_add(x_2, x_13);
x_15 = lean_array_uset(x_9, x_2, x_10);
x_2 = x_14;
x_3 = x_15;
x_4 = x_11;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableDiagnosticWith_enc____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853____at___Lean_Server_FileWorker_handlePreRequestSpecialCases_x3f_spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_181; lean_object* x_182; lean_object* x_211; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = l___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonRange____x40_Lean_Data_Lsp_Basic___hyg_615_(x_3);
x_211 = lean_ctor_get(x_1, 1);
lean_inc(x_211);
if (lean_obj_tag(x_211) == 0)
{
lean_object* x_212; 
x_212 = lean_box(0);
x_181 = x_212;
x_182 = x_2;
goto block_210;
}
else
{
uint8_t x_213; 
x_213 = !lean_is_exclusive(x_211);
if (x_213 == 0)
{
lean_object* x_214; lean_object* x_215; 
x_214 = lean_ctor_get(x_211, 0);
x_215 = l___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonRange____x40_Lean_Data_Lsp_Basic___hyg_615_(x_214);
lean_ctor_set(x_211, 0, x_215);
x_181 = x_211;
x_182 = x_2;
goto block_210;
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_216 = lean_ctor_get(x_211, 0);
lean_inc(x_216);
lean_dec(x_211);
x_217 = l___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonRange____x40_Lean_Data_Lsp_Basic___hyg_615_(x_216);
x_218 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_218, 0, x_217);
x_181 = x_218;
x_182 = x_2;
goto block_210;
}
}
block_19:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_1, 10);
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_16, 0, x_4);
lean_ctor_set(x_16, 1, x_9);
lean_ctor_set(x_16, 2, x_6);
lean_ctor_set(x_16, 3, x_12);
lean_ctor_set(x_16, 4, x_11);
lean_ctor_set(x_16, 5, x_8);
lean_ctor_set(x_16, 6, x_10);
lean_ctor_set(x_16, 7, x_5);
lean_ctor_set(x_16, 8, x_7);
lean_ctor_set(x_16, 9, x_13);
lean_ctor_set(x_16, 10, x_15);
x_17 = l___private_Lean_Widget_InteractiveDiagnostic_0__Lean_Widget_toJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveDiagnostic___hyg_2611_(x_16);
lean_dec(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_14);
return x_18;
}
block_53:
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_1, 9);
lean_inc(x_29);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; 
x_30 = lean_box(0);
x_5 = x_20;
x_6 = x_21;
x_7 = x_27;
x_8 = x_22;
x_9 = x_23;
x_10 = x_24;
x_11 = x_25;
x_12 = x_26;
x_13 = x_30;
x_14 = x_28;
goto block_19;
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_29);
if (x_31 == 0)
{
lean_object* x_32; size_t x_33; lean_object* x_34; size_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; size_t x_39; lean_object* x_40; lean_object* x_41; 
x_32 = lean_ctor_get(x_29, 0);
x_33 = lean_array_size(x_32);
x_34 = lean_unsigned_to_nat(0u);
x_35 = lean_usize_of_nat(x_34);
x_36 = l_Array_mapMUnsafe_map___at___Lean_Widget_instRpcEncodableDiagnosticWith_enc____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853____at___Lean_Server_FileWorker_handlePreRequestSpecialCases_x3f_spec__2_spec__2(x_33, x_35, x_32, x_28);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_array_size(x_37);
x_40 = l_Array_mapMUnsafe_map___at___Lean_Json_opt___at_____private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1558__spec__0_spec__0(x_39, x_35, x_37);
x_41 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_29, 0, x_41);
x_5 = x_20;
x_6 = x_21;
x_7 = x_27;
x_8 = x_22;
x_9 = x_23;
x_10 = x_24;
x_11 = x_25;
x_12 = x_26;
x_13 = x_29;
x_14 = x_38;
goto block_19;
}
else
{
lean_object* x_42; size_t x_43; lean_object* x_44; size_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; size_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_42 = lean_ctor_get(x_29, 0);
lean_inc(x_42);
lean_dec(x_29);
x_43 = lean_array_size(x_42);
x_44 = lean_unsigned_to_nat(0u);
x_45 = lean_usize_of_nat(x_44);
x_46 = l_Array_mapMUnsafe_map___at___Lean_Widget_instRpcEncodableDiagnosticWith_enc____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853____at___Lean_Server_FileWorker_handlePreRequestSpecialCases_x3f_spec__2_spec__2(x_43, x_45, x_42, x_28);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_array_size(x_47);
x_50 = l_Array_mapMUnsafe_map___at___Lean_Json_opt___at_____private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1558__spec__0_spec__0(x_49, x_45, x_47);
x_51 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_51, 0, x_50);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_5 = x_20;
x_6 = x_21;
x_7 = x_27;
x_8 = x_22;
x_9 = x_23;
x_10 = x_24;
x_11 = x_25;
x_12 = x_26;
x_13 = x_52;
x_14 = x_48;
goto block_19;
}
}
}
block_86:
{
lean_object* x_62; 
x_62 = lean_ctor_get(x_1, 8);
lean_inc(x_62);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; 
x_63 = lean_box(0);
x_20 = x_60;
x_21 = x_54;
x_22 = x_55;
x_23 = x_56;
x_24 = x_57;
x_25 = x_58;
x_26 = x_59;
x_27 = x_63;
x_28 = x_61;
goto block_53;
}
else
{
uint8_t x_64; 
x_64 = !lean_is_exclusive(x_62);
if (x_64 == 0)
{
lean_object* x_65; size_t x_66; lean_object* x_67; size_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; size_t x_72; lean_object* x_73; lean_object* x_74; 
x_65 = lean_ctor_get(x_62, 0);
x_66 = lean_array_size(x_65);
x_67 = lean_unsigned_to_nat(0u);
x_68 = lean_usize_of_nat(x_67);
x_69 = l_Array_mapMUnsafe_map___at___Lean_Widget_instRpcEncodableDiagnosticWith_enc____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853____at___Lean_Server_FileWorker_handlePreRequestSpecialCases_x3f_spec__2_spec__3(x_66, x_68, x_65, x_61);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = lean_array_size(x_70);
x_73 = l_Array_mapMUnsafe_map___at___Lean_Json_opt___at_____private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1558__spec__0_spec__0(x_72, x_68, x_70);
x_74 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_62, 0, x_74);
x_20 = x_60;
x_21 = x_54;
x_22 = x_55;
x_23 = x_56;
x_24 = x_57;
x_25 = x_58;
x_26 = x_59;
x_27 = x_62;
x_28 = x_71;
goto block_53;
}
else
{
lean_object* x_75; size_t x_76; lean_object* x_77; size_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; size_t x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_75 = lean_ctor_get(x_62, 0);
lean_inc(x_75);
lean_dec(x_62);
x_76 = lean_array_size(x_75);
x_77 = lean_unsigned_to_nat(0u);
x_78 = lean_usize_of_nat(x_77);
x_79 = l_Array_mapMUnsafe_map___at___Lean_Widget_instRpcEncodableDiagnosticWith_enc____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853____at___Lean_Server_FileWorker_handlePreRequestSpecialCases_x3f_spec__2_spec__3(x_76, x_78, x_75, x_61);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = lean_array_size(x_80);
x_83 = l_Array_mapMUnsafe_map___at___Lean_Json_opt___at_____private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1558__spec__0_spec__0(x_82, x_78, x_80);
x_84 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_84, 0, x_83);
x_85 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_85, 0, x_84);
x_20 = x_60;
x_21 = x_54;
x_22 = x_55;
x_23 = x_56;
x_24 = x_57;
x_25 = x_58;
x_26 = x_59;
x_27 = x_85;
x_28 = x_81;
goto block_53;
}
}
}
block_123:
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_93 = lean_ctor_get(x_1, 6);
lean_inc(x_93);
x_94 = lean_alloc_closure((void*)(l_Lean_Widget_instRpcEncodableMsgEmbed_enc____x40_Lean_Widget_InteractiveDiagnostic___hyg_570_), 2, 0);
x_95 = l_Lean_Widget_TaggedText_mapM___at___Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc____x40_Lean_Widget_InteractiveGoal___hyg_5__spec__2(lean_box(0), lean_box(0), x_94, x_93, x_92);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
x_98 = l___private_Lean_Widget_TaggedText_0__Lean_Widget_toJsonTaggedText____x40_Lean_Widget_TaggedText___hyg_621____at___Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc____x40_Lean_Widget_InteractiveGoal___hyg_5__spec__4(x_96);
x_99 = lean_ctor_get(x_1, 7);
lean_inc(x_99);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; 
x_100 = lean_box(0);
x_54 = x_87;
x_55 = x_91;
x_56 = x_88;
x_57 = x_98;
x_58 = x_89;
x_59 = x_90;
x_60 = x_100;
x_61 = x_97;
goto block_86;
}
else
{
uint8_t x_101; 
x_101 = !lean_is_exclusive(x_99);
if (x_101 == 0)
{
lean_object* x_102; size_t x_103; lean_object* x_104; size_t x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; size_t x_109; lean_object* x_110; lean_object* x_111; 
x_102 = lean_ctor_get(x_99, 0);
x_103 = lean_array_size(x_102);
x_104 = lean_unsigned_to_nat(0u);
x_105 = lean_usize_of_nat(x_104);
x_106 = l_Array_mapMUnsafe_map___at___Lean_Widget_instRpcEncodableDiagnosticWith_enc____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853____at___Lean_Server_FileWorker_handlePreRequestSpecialCases_x3f_spec__2_spec__4(x_103, x_105, x_102, x_97);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec(x_106);
x_109 = lean_array_size(x_107);
x_110 = l_Array_mapMUnsafe_map___at___Lean_Json_opt___at_____private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1558__spec__0_spec__0(x_109, x_105, x_107);
x_111 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_99, 0, x_111);
x_54 = x_87;
x_55 = x_91;
x_56 = x_88;
x_57 = x_98;
x_58 = x_89;
x_59 = x_90;
x_60 = x_99;
x_61 = x_108;
goto block_86;
}
else
{
lean_object* x_112; size_t x_113; lean_object* x_114; size_t x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; size_t x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_112 = lean_ctor_get(x_99, 0);
lean_inc(x_112);
lean_dec(x_99);
x_113 = lean_array_size(x_112);
x_114 = lean_unsigned_to_nat(0u);
x_115 = lean_usize_of_nat(x_114);
x_116 = l_Array_mapMUnsafe_map___at___Lean_Widget_instRpcEncodableDiagnosticWith_enc____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853____at___Lean_Server_FileWorker_handlePreRequestSpecialCases_x3f_spec__2_spec__4(x_113, x_115, x_112, x_97);
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
lean_dec(x_116);
x_119 = lean_array_size(x_117);
x_120 = l_Array_mapMUnsafe_map___at___Lean_Json_opt___at_____private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1558__spec__0_spec__0(x_119, x_115, x_117);
x_121 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_121, 0, x_120);
x_122 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_122, 0, x_121);
x_54 = x_87;
x_55 = x_91;
x_56 = x_88;
x_57 = x_98;
x_58 = x_89;
x_59 = x_90;
x_60 = x_122;
x_61 = x_118;
goto block_86;
}
}
}
block_137:
{
lean_object* x_129; 
x_129 = lean_ctor_get(x_1, 5);
lean_inc(x_129);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; 
x_130 = lean_box(0);
x_87 = x_124;
x_88 = x_125;
x_89 = x_127;
x_90 = x_126;
x_91 = x_130;
x_92 = x_128;
goto block_123;
}
else
{
uint8_t x_131; 
x_131 = !lean_is_exclusive(x_129);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; 
x_132 = lean_ctor_get(x_129, 0);
x_133 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_129, 0, x_133);
x_87 = x_124;
x_88 = x_125;
x_89 = x_127;
x_90 = x_126;
x_91 = x_129;
x_92 = x_128;
goto block_123;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_ctor_get(x_129, 0);
lean_inc(x_134);
lean_dec(x_129);
x_135 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_135, 0, x_134);
x_136 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_136, 0, x_135);
x_87 = x_124;
x_88 = x_125;
x_89 = x_127;
x_90 = x_126;
x_91 = x_136;
x_92 = x_128;
goto block_123;
}
}
}
block_144:
{
lean_object* x_143; 
x_143 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_143, 0, x_141);
x_124 = x_138;
x_125 = x_139;
x_126 = x_140;
x_127 = x_143;
x_128 = x_142;
goto block_137;
}
block_161:
{
lean_object* x_149; 
x_149 = lean_ctor_get(x_1, 4);
lean_inc(x_149);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; 
x_150 = lean_box(0);
x_124 = x_145;
x_125 = x_146;
x_126 = x_147;
x_127 = x_150;
x_128 = x_148;
goto block_137;
}
else
{
lean_object* x_151; 
x_151 = lean_ctor_get(x_149, 0);
lean_inc(x_151);
lean_dec(x_149);
if (lean_obj_tag(x_151) == 0)
{
uint8_t x_152; 
x_152 = !lean_is_exclusive(x_151);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; 
x_153 = lean_ctor_get(x_151, 0);
x_154 = l_Lean_JsonNumber_fromInt(x_153);
lean_ctor_set_tag(x_151, 2);
lean_ctor_set(x_151, 0, x_154);
x_138 = x_145;
x_139 = x_146;
x_140 = x_147;
x_141 = x_151;
x_142 = x_148;
goto block_144;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_155 = lean_ctor_get(x_151, 0);
lean_inc(x_155);
lean_dec(x_151);
x_156 = l_Lean_JsonNumber_fromInt(x_155);
x_157 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_157, 0, x_156);
x_138 = x_145;
x_139 = x_146;
x_140 = x_147;
x_141 = x_157;
x_142 = x_148;
goto block_144;
}
}
else
{
uint8_t x_158; 
x_158 = !lean_is_exclusive(x_151);
if (x_158 == 0)
{
lean_ctor_set_tag(x_151, 3);
x_138 = x_145;
x_139 = x_146;
x_140 = x_147;
x_141 = x_151;
x_142 = x_148;
goto block_144;
}
else
{
lean_object* x_159; lean_object* x_160; 
x_159 = lean_ctor_get(x_151, 0);
lean_inc(x_159);
lean_dec(x_151);
x_160 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_160, 0, x_159);
x_138 = x_145;
x_139 = x_146;
x_140 = x_147;
x_141 = x_160;
x_142 = x_148;
goto block_144;
}
}
}
}
block_175:
{
lean_object* x_165; 
x_165 = lean_ctor_get(x_1, 3);
lean_inc(x_165);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; 
x_166 = lean_box(0);
x_145 = x_163;
x_146 = x_162;
x_147 = x_166;
x_148 = x_164;
goto block_161;
}
else
{
uint8_t x_167; 
x_167 = !lean_is_exclusive(x_165);
if (x_167 == 0)
{
lean_object* x_168; lean_object* x_169; uint8_t x_170; 
x_168 = lean_ctor_get(x_165, 0);
x_169 = lean_alloc_ctor(1, 0, 1);
x_170 = lean_unbox(x_168);
lean_dec(x_168);
lean_ctor_set_uint8(x_169, 0, x_170);
lean_ctor_set(x_165, 0, x_169);
x_145 = x_163;
x_146 = x_162;
x_147 = x_165;
x_148 = x_164;
goto block_161;
}
else
{
lean_object* x_171; lean_object* x_172; uint8_t x_173; lean_object* x_174; 
x_171 = lean_ctor_get(x_165, 0);
lean_inc(x_171);
lean_dec(x_165);
x_172 = lean_alloc_ctor(1, 0, 1);
x_173 = lean_unbox(x_171);
lean_dec(x_171);
lean_ctor_set_uint8(x_172, 0, x_173);
x_174 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_174, 0, x_172);
x_145 = x_163;
x_146 = x_162;
x_147 = x_174;
x_148 = x_164;
goto block_161;
}
}
}
block_180:
{
lean_object* x_179; 
x_179 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_179, 0, x_177);
x_162 = x_176;
x_163 = x_179;
x_164 = x_178;
goto block_175;
}
block_210:
{
lean_object* x_183; 
x_183 = lean_ctor_get(x_1, 2);
lean_inc(x_183);
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_184; 
x_184 = lean_box(0);
x_162 = x_181;
x_163 = x_184;
x_164 = x_182;
goto block_175;
}
else
{
uint8_t x_185; 
x_185 = !lean_is_exclusive(x_183);
if (x_185 == 0)
{
lean_object* x_186; uint8_t x_187; 
x_186 = lean_ctor_get(x_183, 0);
x_187 = lean_unbox(x_186);
lean_dec(x_186);
switch (x_187) {
case 0:
{
lean_object* x_188; lean_object* x_189; 
x_188 = lean_unsigned_to_nat(1u);
x_189 = l_Lean_JsonNumber_fromNat(x_188);
lean_ctor_set_tag(x_183, 2);
lean_ctor_set(x_183, 0, x_189);
x_176 = x_181;
x_177 = x_183;
x_178 = x_182;
goto block_180;
}
case 1:
{
lean_object* x_190; lean_object* x_191; 
x_190 = lean_unsigned_to_nat(2u);
x_191 = l_Lean_JsonNumber_fromNat(x_190);
lean_ctor_set_tag(x_183, 2);
lean_ctor_set(x_183, 0, x_191);
x_176 = x_181;
x_177 = x_183;
x_178 = x_182;
goto block_180;
}
case 2:
{
lean_object* x_192; lean_object* x_193; 
x_192 = lean_unsigned_to_nat(3u);
x_193 = l_Lean_JsonNumber_fromNat(x_192);
lean_ctor_set_tag(x_183, 2);
lean_ctor_set(x_183, 0, x_193);
x_176 = x_181;
x_177 = x_183;
x_178 = x_182;
goto block_180;
}
default: 
{
lean_object* x_194; lean_object* x_195; 
x_194 = lean_unsigned_to_nat(4u);
x_195 = l_Lean_JsonNumber_fromNat(x_194);
lean_ctor_set_tag(x_183, 2);
lean_ctor_set(x_183, 0, x_195);
x_176 = x_181;
x_177 = x_183;
x_178 = x_182;
goto block_180;
}
}
}
else
{
lean_object* x_196; uint8_t x_197; 
x_196 = lean_ctor_get(x_183, 0);
lean_inc(x_196);
lean_dec(x_183);
x_197 = lean_unbox(x_196);
lean_dec(x_196);
switch (x_197) {
case 0:
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_198 = lean_unsigned_to_nat(1u);
x_199 = l_Lean_JsonNumber_fromNat(x_198);
x_200 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_200, 0, x_199);
x_176 = x_181;
x_177 = x_200;
x_178 = x_182;
goto block_180;
}
case 1:
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_201 = lean_unsigned_to_nat(2u);
x_202 = l_Lean_JsonNumber_fromNat(x_201);
x_203 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_203, 0, x_202);
x_176 = x_181;
x_177 = x_203;
x_178 = x_182;
goto block_180;
}
case 2:
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_204 = lean_unsigned_to_nat(3u);
x_205 = l_Lean_JsonNumber_fromNat(x_204);
x_206 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_206, 0, x_205);
x_176 = x_181;
x_177 = x_206;
x_178 = x_182;
goto block_180;
}
default: 
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_207 = lean_unsigned_to_nat(4u);
x_208 = l_Lean_JsonNumber_fromNat(x_207);
x_209 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_209, 0, x_208);
x_176 = x_181;
x_177 = x_209;
x_178 = x_182;
goto block_180;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Server_FileWorker_handlePreRequestSpecialCases_x3f_spec__6(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_7 = lean_array_uget(x_3, x_2);
x_8 = l_Lean_Widget_instRpcEncodableDiagnosticWith_enc____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853____at___Lean_Server_FileWorker_handlePreRequestSpecialCases_x3f_spec__2(x_7, x_4);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_box(0);
x_12 = lean_array_uset(x_3, x_2, x_11);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_usize_of_nat(x_13);
x_15 = lean_usize_add(x_2, x_14);
x_16 = lean_array_uset(x_12, x_2, x_9);
x_2 = x_15;
x_3 = x_16;
x_4 = x_10;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handlePreRequestSpecialCases_x3f___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lean_Server_FileWorker_waitUnknownIdentifierRanges(x_1, x_2, x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = l_Array_isEmpty___redArg(x_10);
if (x_12 == 0)
{
lean_object* x_13; 
lean_free_object(x_8);
x_13 = l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f(x_3, x_4, x_10, x_6, x_11);
lean_dec(x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_16 = x_13;
} else {
 lean_dec_ref(x_13);
 x_16 = lean_box(0);
}
if (lean_obj_tag(x_14) == 0)
{
x_17 = x_4;
goto block_21;
}
else
{
lean_object* x_22; 
lean_dec(x_4);
x_22 = lean_ctor_get(x_14, 0);
lean_inc(x_22);
lean_dec(x_14);
x_17 = x_22;
goto block_21;
}
block_21:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = l___private_Lean_Data_Lsp_CodeActions_0__Lean_Lsp_toJsonCodeAction____x40_Lean_Data_Lsp_CodeActions___hyg_1131_(x_17);
x_19 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set_uint8(x_19, sizeof(void*)*1, x_5);
if (lean_is_scalar(x_16)) {
 x_20 = lean_alloc_ctor(0, 2, 0);
} else {
 x_20 = x_16;
}
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_15);
return x_20;
}
}
else
{
uint8_t x_23; 
lean_dec(x_4);
x_23 = !lean_is_exclusive(x_13);
if (x_23 == 0)
{
return x_13;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_13, 0);
x_25 = lean_ctor_get(x_13, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_13);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_3);
x_27 = l___private_Lean_Data_Lsp_CodeActions_0__Lean_Lsp_toJsonCodeAction____x40_Lean_Data_Lsp_CodeActions___hyg_1131_(x_4);
x_28 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set_uint8(x_28, sizeof(void*)*1, x_5);
lean_ctor_set(x_8, 0, x_28);
return x_8;
}
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_ctor_get(x_8, 0);
x_30 = lean_ctor_get(x_8, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_8);
x_31 = l_Array_isEmpty___redArg(x_29);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f(x_3, x_4, x_29, x_6, x_30);
lean_dec(x_29);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_35 = x_32;
} else {
 lean_dec_ref(x_32);
 x_35 = lean_box(0);
}
if (lean_obj_tag(x_33) == 0)
{
x_36 = x_4;
goto block_40;
}
else
{
lean_object* x_41; 
lean_dec(x_4);
x_41 = lean_ctor_get(x_33, 0);
lean_inc(x_41);
lean_dec(x_33);
x_36 = x_41;
goto block_40;
}
block_40:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = l___private_Lean_Data_Lsp_CodeActions_0__Lean_Lsp_toJsonCodeAction____x40_Lean_Data_Lsp_CodeActions___hyg_1131_(x_36);
x_38 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set_uint8(x_38, sizeof(void*)*1, x_5);
if (lean_is_scalar(x_35)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_35;
}
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_34);
return x_39;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_4);
x_42 = lean_ctor_get(x_32, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_32, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_44 = x_32;
} else {
 lean_dec_ref(x_32);
 x_44 = lean_box(0);
}
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(1, 2, 0);
} else {
 x_45 = x_44;
}
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_29);
lean_dec(x_6);
lean_dec(x_3);
x_46 = l___private_Lean_Data_Lsp_CodeActions_0__Lean_Lsp_toJsonCodeAction____x40_Lean_Data_Lsp_CodeActions___hyg_1131_(x_4);
x_47 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set_uint8(x_47, sizeof(void*)*1, x_5);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_30);
return x_48;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handlePreRequestSpecialCases_x3f___lam__1(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handlePreRequestSpecialCases_x3f___lam__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handlePreRequestSpecialCases_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_mk_string_unchecked("$/lean/rpc/call", 15, 15);
x_9 = lean_string_dec_eq(x_4, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_mk_string_unchecked("codeAction/resolve", 18, 18);
x_11 = lean_string_dec_eq(x_4, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_7);
return x_13;
}
else
{
lean_object* x_14; 
x_14 = l_Lean_Server_RequestM_parseRequestParams___at___Lean_Server_registerLspRequestHandler___at___Lean_Server_initFn____x40_Lean_Server_CodeActions_Basic___hyg_1538__spec__0_spec__1(x_5, x_6, x_7);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 9);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_14, 0);
lean_dec(x_18);
x_19 = lean_mk_string_unchecked("Expected a data field on CodeAction.", 36, 36);
x_20 = l_Lean_Server_RequestError_invalidParams(x_19);
lean_ctor_set_tag(x_14, 1);
lean_ctor_set(x_14, 0, x_20);
return x_14;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
lean_dec(x_14);
x_22 = lean_mk_string_unchecked("Expected a data field on CodeAction.", 36, 36);
x_23 = l_Lean_Server_RequestError_invalidParams(x_22);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_21);
return x_24;
}
}
else
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_14, 1);
lean_inc(x_25);
lean_dec(x_14);
x_26 = !lean_is_exclusive(x_16);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_16, 0);
x_28 = l_Lean_Server_RequestM_parseRequestParams___at___Lean_Server_handleCodeActionResolve_spec__0___redArg(x_27, x_25);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_ctor_get(x_28, 1);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_Server_FileWorker_importAllUnknownIdentifiersProvider;
x_34 = lean_name_eq(x_32, x_33);
lean_dec(x_32);
if (x_34 == 0)
{
lean_object* x_35; 
lean_free_object(x_16);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_35 = lean_box(0);
lean_ctor_set(x_28, 0, x_35);
return x_28;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
lean_free_object(x_28);
x_36 = lean_unsigned_to_nat(0u);
x_37 = lean_ctor_get(x_2, 0);
lean_inc(x_37);
lean_dec(x_2);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_ctor_get(x_39, 3);
lean_inc(x_40);
lean_dec(x_39);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec(x_40);
x_42 = lean_string_utf8_byte_size(x_41);
lean_dec(x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_36);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_box(x_34);
x_45 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_handlePreRequestSpecialCases_x3f___lam__0___boxed), 7, 5);
lean_closure_set(x_45, 0, x_37);
lean_closure_set(x_45, 1, x_43);
lean_closure_set(x_45, 2, x_3);
lean_closure_set(x_45, 3, x_15);
lean_closure_set(x_45, 4, x_44);
x_46 = l_Lean_Server_RequestM_asTask___redArg(x_45, x_6, x_31);
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_46, 0);
lean_ctor_set(x_16, 0, x_48);
lean_ctor_set(x_46, 0, x_16);
return x_46;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_46, 0);
x_50 = lean_ctor_get(x_46, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_46);
lean_ctor_set(x_16, 0, x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_16);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_52 = lean_ctor_get(x_28, 0);
x_53 = lean_ctor_get(x_28, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_28);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = l_Lean_Server_FileWorker_importAllUnknownIdentifiersProvider;
x_56 = lean_name_eq(x_54, x_55);
lean_dec(x_54);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; 
lean_free_object(x_16);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_57 = lean_box(0);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_53);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_59 = lean_unsigned_to_nat(0u);
x_60 = lean_ctor_get(x_2, 0);
lean_inc(x_60);
lean_dec(x_2);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
lean_dec(x_61);
x_63 = lean_ctor_get(x_62, 3);
lean_inc(x_63);
lean_dec(x_62);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
lean_dec(x_63);
x_65 = lean_string_utf8_byte_size(x_64);
lean_dec(x_64);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_59);
lean_ctor_set(x_66, 1, x_65);
x_67 = lean_box(x_56);
x_68 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_handlePreRequestSpecialCases_x3f___lam__0___boxed), 7, 5);
lean_closure_set(x_68, 0, x_60);
lean_closure_set(x_68, 1, x_66);
lean_closure_set(x_68, 2, x_3);
lean_closure_set(x_68, 3, x_15);
lean_closure_set(x_68, 4, x_67);
x_69 = l_Lean_Server_RequestM_asTask___redArg(x_68, x_6, x_53);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_72 = x_69;
} else {
 lean_dec_ref(x_69);
 x_72 = lean_box(0);
}
lean_ctor_set(x_16, 0, x_70);
if (lean_is_scalar(x_72)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_72;
}
lean_ctor_set(x_73, 0, x_16);
lean_ctor_set(x_73, 1, x_71);
return x_73;
}
}
}
else
{
uint8_t x_74; 
lean_free_object(x_16);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_74 = !lean_is_exclusive(x_28);
if (x_74 == 0)
{
return x_28;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_28, 0);
x_76 = lean_ctor_get(x_28, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_28);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
else
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_16, 0);
lean_inc(x_78);
lean_dec(x_16);
x_79 = l_Lean_Server_RequestM_parseRequestParams___at___Lean_Server_handleCodeActionResolve_spec__0___redArg(x_78, x_25);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_82 = x_79;
} else {
 lean_dec_ref(x_79);
 x_82 = lean_box(0);
}
x_83 = lean_ctor_get(x_80, 1);
lean_inc(x_83);
lean_dec(x_80);
x_84 = l_Lean_Server_FileWorker_importAllUnknownIdentifiersProvider;
x_85 = lean_name_eq(x_83, x_84);
lean_dec(x_83);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; 
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_86 = lean_box(0);
if (lean_is_scalar(x_82)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_82;
}
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_81);
return x_87;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_82);
x_88 = lean_unsigned_to_nat(0u);
x_89 = lean_ctor_get(x_2, 0);
lean_inc(x_89);
lean_dec(x_2);
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
lean_dec(x_90);
x_92 = lean_ctor_get(x_91, 3);
lean_inc(x_92);
lean_dec(x_91);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
lean_dec(x_92);
x_94 = lean_string_utf8_byte_size(x_93);
lean_dec(x_93);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_88);
lean_ctor_set(x_95, 1, x_94);
x_96 = lean_box(x_85);
x_97 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_handlePreRequestSpecialCases_x3f___lam__0___boxed), 7, 5);
lean_closure_set(x_97, 0, x_89);
lean_closure_set(x_97, 1, x_95);
lean_closure_set(x_97, 2, x_3);
lean_closure_set(x_97, 3, x_15);
lean_closure_set(x_97, 4, x_96);
x_98 = l_Lean_Server_RequestM_asTask___redArg(x_97, x_6, x_81);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_101 = x_98;
} else {
 lean_dec_ref(x_98);
 x_101 = lean_box(0);
}
x_102 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_102, 0, x_99);
if (lean_is_scalar(x_101)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_101;
}
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_100);
return x_103;
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_104 = lean_ctor_get(x_79, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_79, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_106 = x_79;
} else {
 lean_dec_ref(x_79);
 x_106 = lean_box(0);
}
if (lean_is_scalar(x_106)) {
 x_107 = lean_alloc_ctor(1, 2, 0);
} else {
 x_107 = x_106;
}
lean_ctor_set(x_107, 0, x_104);
lean_ctor_set(x_107, 1, x_105);
return x_107;
}
}
}
}
else
{
uint8_t x_108; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_108 = !lean_is_exclusive(x_14);
if (x_108 == 0)
{
return x_14;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_14, 0);
x_110 = lean_ctor_get(x_14, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_14);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
}
}
else
{
lean_object* x_112; 
lean_dec(x_3);
x_112 = l_Lean_Server_RequestM_parseRequestParams___at___Lean_Server_registerLspRequestHandler___at___Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_409__spec__0_spec__1___redArg(x_5, x_7);
if (lean_obj_tag(x_112) == 0)
{
uint8_t x_113; 
x_113 = !lean_is_exclusive(x_112);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; 
x_114 = lean_ctor_get(x_112, 0);
x_115 = lean_ctor_get(x_112, 1);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
x_117 = lean_mk_string_unchecked("Lean", 4, 4);
x_118 = lean_mk_string_unchecked("Widget", 6, 6);
x_119 = lean_mk_string_unchecked("getInteractiveDiagnostics", 25, 25);
x_120 = l_Lean_Name_mkStr3(x_117, x_118, x_119);
x_121 = lean_name_eq(x_116, x_120);
lean_dec(x_120);
lean_dec(x_116);
if (x_121 == 0)
{
lean_object* x_122; 
lean_dec(x_114);
lean_dec(x_6);
lean_dec(x_2);
x_122 = lean_box(0);
lean_ctor_set(x_112, 0, x_122);
return x_112;
}
else
{
lean_object* x_123; uint64_t x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_2, 4);
lean_inc(x_123);
lean_dec(x_2);
x_124 = lean_ctor_get_uint64(x_114, sizeof(void*)*3);
x_125 = l_Lean_RBNode_find___at___Lean_Server_wrapRpcProcedure___at___Lean_Server_registerBuiltinRpcProcedure___at___Lean_Widget_initFn____x40_Lean_Server_FileWorker_WidgetRequests___hyg_394__spec__0_spec__0_spec__0___redArg(x_123, x_124);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; 
lean_dec(x_114);
lean_dec(x_6);
x_126 = l_Lean_Server_RequestError_rpcNeedsReconnect;
lean_ctor_set_tag(x_112, 1);
lean_ctor_set(x_112, 0, x_126);
return x_112;
}
else
{
uint8_t x_127; 
lean_free_object(x_112);
x_127 = !lean_is_exclusive(x_125);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_125, 0);
x_129 = lean_ctor_get(x_114, 2);
lean_inc(x_129);
lean_dec(x_114);
x_130 = l_Lean_Server_RequestM_parseRequestParams___at___Lean_Server_FileWorker_handlePreRequestSpecialCases_x3f_spec__0___redArg(x_129, x_115);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; size_t x_140; lean_object* x_141; size_t x_142; lean_object* x_143; uint8_t x_144; 
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
lean_dec(x_130);
x_133 = l_Lean_Server_FileWorker_handleGetInteractiveDiagnosticsRequest(x_1, x_131, x_6, x_132);
lean_dec(x_6);
lean_dec(x_131);
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
lean_dec(x_133);
x_136 = lean_st_ref_take(x_128, x_135);
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_136, 1);
lean_inc(x_138);
lean_dec(x_136);
x_139 = lean_ctor_get(x_137, 0);
lean_inc(x_139);
x_140 = lean_array_size(x_134);
x_141 = lean_unsigned_to_nat(0u);
x_142 = lean_usize_of_nat(x_141);
x_143 = l_Array_mapMUnsafe_map___at___Lean_Server_FileWorker_handlePreRequestSpecialCases_x3f_spec__6(x_140, x_142, x_134, x_139);
x_144 = !lean_is_exclusive(x_143);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; size_t x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; 
x_145 = lean_ctor_get(x_143, 0);
x_146 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_handlePreRequestSpecialCases_x3f___lam__1___boxed), 1, 0);
x_147 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_handlePreRequestSpecialCases_x3f___lam__2___boxed), 2, 1);
lean_closure_set(x_147, 0, x_137);
x_148 = lean_array_size(x_145);
x_149 = l_Array_mapMUnsafe_map___at___Lean_Json_opt___at_____private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1558__spec__0_spec__0(x_148, x_142, x_145);
x_150 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_143, 0, x_150);
x_151 = l_Prod_map(lean_box(0), lean_box(0), lean_box(0), lean_box(0), x_146, x_147, x_143);
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_151, 1);
lean_inc(x_153);
lean_dec(x_151);
x_154 = lean_st_ref_set(x_128, x_153, x_138);
lean_dec(x_128);
x_155 = !lean_is_exclusive(x_154);
if (x_155 == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_156 = lean_ctor_get(x_154, 0);
lean_dec(x_156);
x_157 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_157, 0, x_152);
lean_ctor_set_uint8(x_157, sizeof(void*)*1, x_121);
x_158 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_158, 0, x_157);
x_159 = lean_task_pure(x_158);
lean_ctor_set(x_125, 0, x_159);
lean_ctor_set(x_154, 0, x_125);
return x_154;
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_160 = lean_ctor_get(x_154, 1);
lean_inc(x_160);
lean_dec(x_154);
x_161 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_161, 0, x_152);
lean_ctor_set_uint8(x_161, sizeof(void*)*1, x_121);
x_162 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_162, 0, x_161);
x_163 = lean_task_pure(x_162);
lean_ctor_set(x_125, 0, x_163);
x_164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_164, 0, x_125);
lean_ctor_set(x_164, 1, x_160);
return x_164;
}
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; size_t x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_165 = lean_ctor_get(x_143, 0);
x_166 = lean_ctor_get(x_143, 1);
lean_inc(x_166);
lean_inc(x_165);
lean_dec(x_143);
x_167 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_handlePreRequestSpecialCases_x3f___lam__1___boxed), 1, 0);
x_168 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_handlePreRequestSpecialCases_x3f___lam__2___boxed), 2, 1);
lean_closure_set(x_168, 0, x_137);
x_169 = lean_array_size(x_165);
x_170 = l_Array_mapMUnsafe_map___at___Lean_Json_opt___at_____private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1558__spec__0_spec__0(x_169, x_142, x_165);
x_171 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_171, 0, x_170);
x_172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_166);
x_173 = l_Prod_map(lean_box(0), lean_box(0), lean_box(0), lean_box(0), x_167, x_168, x_172);
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_173, 1);
lean_inc(x_175);
lean_dec(x_173);
x_176 = lean_st_ref_set(x_128, x_175, x_138);
lean_dec(x_128);
x_177 = lean_ctor_get(x_176, 1);
lean_inc(x_177);
if (lean_is_exclusive(x_176)) {
 lean_ctor_release(x_176, 0);
 lean_ctor_release(x_176, 1);
 x_178 = x_176;
} else {
 lean_dec_ref(x_176);
 x_178 = lean_box(0);
}
x_179 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_179, 0, x_174);
lean_ctor_set_uint8(x_179, sizeof(void*)*1, x_121);
x_180 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_180, 0, x_179);
x_181 = lean_task_pure(x_180);
lean_ctor_set(x_125, 0, x_181);
if (lean_is_scalar(x_178)) {
 x_182 = lean_alloc_ctor(0, 2, 0);
} else {
 x_182 = x_178;
}
lean_ctor_set(x_182, 0, x_125);
lean_ctor_set(x_182, 1, x_177);
return x_182;
}
}
else
{
uint8_t x_183; 
lean_free_object(x_125);
lean_dec(x_128);
lean_dec(x_6);
x_183 = !lean_is_exclusive(x_130);
if (x_183 == 0)
{
return x_130;
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_184 = lean_ctor_get(x_130, 0);
x_185 = lean_ctor_get(x_130, 1);
lean_inc(x_185);
lean_inc(x_184);
lean_dec(x_130);
x_186 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_186, 0, x_184);
lean_ctor_set(x_186, 1, x_185);
return x_186;
}
}
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_187 = lean_ctor_get(x_125, 0);
lean_inc(x_187);
lean_dec(x_125);
x_188 = lean_ctor_get(x_114, 2);
lean_inc(x_188);
lean_dec(x_114);
x_189 = l_Lean_Server_RequestM_parseRequestParams___at___Lean_Server_FileWorker_handlePreRequestSpecialCases_x3f_spec__0___redArg(x_188, x_115);
if (lean_obj_tag(x_189) == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; size_t x_199; lean_object* x_200; size_t x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; size_t x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_189, 1);
lean_inc(x_191);
lean_dec(x_189);
x_192 = l_Lean_Server_FileWorker_handleGetInteractiveDiagnosticsRequest(x_1, x_190, x_6, x_191);
lean_dec(x_6);
lean_dec(x_190);
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_192, 1);
lean_inc(x_194);
lean_dec(x_192);
x_195 = lean_st_ref_take(x_187, x_194);
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_195, 1);
lean_inc(x_197);
lean_dec(x_195);
x_198 = lean_ctor_get(x_196, 0);
lean_inc(x_198);
x_199 = lean_array_size(x_193);
x_200 = lean_unsigned_to_nat(0u);
x_201 = lean_usize_of_nat(x_200);
x_202 = l_Array_mapMUnsafe_map___at___Lean_Server_FileWorker_handlePreRequestSpecialCases_x3f_spec__6(x_199, x_201, x_193, x_198);
x_203 = lean_ctor_get(x_202, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_202, 1);
lean_inc(x_204);
if (lean_is_exclusive(x_202)) {
 lean_ctor_release(x_202, 0);
 lean_ctor_release(x_202, 1);
 x_205 = x_202;
} else {
 lean_dec_ref(x_202);
 x_205 = lean_box(0);
}
x_206 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_handlePreRequestSpecialCases_x3f___lam__1___boxed), 1, 0);
x_207 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_handlePreRequestSpecialCases_x3f___lam__2___boxed), 2, 1);
lean_closure_set(x_207, 0, x_196);
x_208 = lean_array_size(x_203);
x_209 = l_Array_mapMUnsafe_map___at___Lean_Json_opt___at_____private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1558__spec__0_spec__0(x_208, x_201, x_203);
x_210 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_210, 0, x_209);
if (lean_is_scalar(x_205)) {
 x_211 = lean_alloc_ctor(0, 2, 0);
} else {
 x_211 = x_205;
}
lean_ctor_set(x_211, 0, x_210);
lean_ctor_set(x_211, 1, x_204);
x_212 = l_Prod_map(lean_box(0), lean_box(0), lean_box(0), lean_box(0), x_206, x_207, x_211);
x_213 = lean_ctor_get(x_212, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_212, 1);
lean_inc(x_214);
lean_dec(x_212);
x_215 = lean_st_ref_set(x_187, x_214, x_197);
lean_dec(x_187);
x_216 = lean_ctor_get(x_215, 1);
lean_inc(x_216);
if (lean_is_exclusive(x_215)) {
 lean_ctor_release(x_215, 0);
 lean_ctor_release(x_215, 1);
 x_217 = x_215;
} else {
 lean_dec_ref(x_215);
 x_217 = lean_box(0);
}
x_218 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_218, 0, x_213);
lean_ctor_set_uint8(x_218, sizeof(void*)*1, x_121);
x_219 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_219, 0, x_218);
x_220 = lean_task_pure(x_219);
x_221 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_221, 0, x_220);
if (lean_is_scalar(x_217)) {
 x_222 = lean_alloc_ctor(0, 2, 0);
} else {
 x_222 = x_217;
}
lean_ctor_set(x_222, 0, x_221);
lean_ctor_set(x_222, 1, x_216);
return x_222;
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
lean_dec(x_187);
lean_dec(x_6);
x_223 = lean_ctor_get(x_189, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_189, 1);
lean_inc(x_224);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 lean_ctor_release(x_189, 1);
 x_225 = x_189;
} else {
 lean_dec_ref(x_189);
 x_225 = lean_box(0);
}
if (lean_is_scalar(x_225)) {
 x_226 = lean_alloc_ctor(1, 2, 0);
} else {
 x_226 = x_225;
}
lean_ctor_set(x_226, 0, x_223);
lean_ctor_set(x_226, 1, x_224);
return x_226;
}
}
}
}
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; uint8_t x_234; 
x_227 = lean_ctor_get(x_112, 0);
x_228 = lean_ctor_get(x_112, 1);
lean_inc(x_228);
lean_inc(x_227);
lean_dec(x_112);
x_229 = lean_ctor_get(x_227, 1);
lean_inc(x_229);
x_230 = lean_mk_string_unchecked("Lean", 4, 4);
x_231 = lean_mk_string_unchecked("Widget", 6, 6);
x_232 = lean_mk_string_unchecked("getInteractiveDiagnostics", 25, 25);
x_233 = l_Lean_Name_mkStr3(x_230, x_231, x_232);
x_234 = lean_name_eq(x_229, x_233);
lean_dec(x_233);
lean_dec(x_229);
if (x_234 == 0)
{
lean_object* x_235; lean_object* x_236; 
lean_dec(x_227);
lean_dec(x_6);
lean_dec(x_2);
x_235 = lean_box(0);
x_236 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_236, 0, x_235);
lean_ctor_set(x_236, 1, x_228);
return x_236;
}
else
{
lean_object* x_237; uint64_t x_238; lean_object* x_239; 
x_237 = lean_ctor_get(x_2, 4);
lean_inc(x_237);
lean_dec(x_2);
x_238 = lean_ctor_get_uint64(x_227, sizeof(void*)*3);
x_239 = l_Lean_RBNode_find___at___Lean_Server_wrapRpcProcedure___at___Lean_Server_registerBuiltinRpcProcedure___at___Lean_Widget_initFn____x40_Lean_Server_FileWorker_WidgetRequests___hyg_394__spec__0_spec__0_spec__0___redArg(x_237, x_238);
if (lean_obj_tag(x_239) == 0)
{
lean_object* x_240; lean_object* x_241; 
lean_dec(x_227);
lean_dec(x_6);
x_240 = l_Lean_Server_RequestError_rpcNeedsReconnect;
x_241 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_241, 0, x_240);
lean_ctor_set(x_241, 1, x_228);
return x_241;
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_242 = lean_ctor_get(x_239, 0);
lean_inc(x_242);
if (lean_is_exclusive(x_239)) {
 lean_ctor_release(x_239, 0);
 x_243 = x_239;
} else {
 lean_dec_ref(x_239);
 x_243 = lean_box(0);
}
x_244 = lean_ctor_get(x_227, 2);
lean_inc(x_244);
lean_dec(x_227);
x_245 = l_Lean_Server_RequestM_parseRequestParams___at___Lean_Server_FileWorker_handlePreRequestSpecialCases_x3f_spec__0___redArg(x_244, x_228);
if (lean_obj_tag(x_245) == 0)
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; size_t x_255; lean_object* x_256; size_t x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; size_t x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_246 = lean_ctor_get(x_245, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_245, 1);
lean_inc(x_247);
lean_dec(x_245);
x_248 = l_Lean_Server_FileWorker_handleGetInteractiveDiagnosticsRequest(x_1, x_246, x_6, x_247);
lean_dec(x_6);
lean_dec(x_246);
x_249 = lean_ctor_get(x_248, 0);
lean_inc(x_249);
x_250 = lean_ctor_get(x_248, 1);
lean_inc(x_250);
lean_dec(x_248);
x_251 = lean_st_ref_take(x_242, x_250);
x_252 = lean_ctor_get(x_251, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_251, 1);
lean_inc(x_253);
lean_dec(x_251);
x_254 = lean_ctor_get(x_252, 0);
lean_inc(x_254);
x_255 = lean_array_size(x_249);
x_256 = lean_unsigned_to_nat(0u);
x_257 = lean_usize_of_nat(x_256);
x_258 = l_Array_mapMUnsafe_map___at___Lean_Server_FileWorker_handlePreRequestSpecialCases_x3f_spec__6(x_255, x_257, x_249, x_254);
x_259 = lean_ctor_get(x_258, 0);
lean_inc(x_259);
x_260 = lean_ctor_get(x_258, 1);
lean_inc(x_260);
if (lean_is_exclusive(x_258)) {
 lean_ctor_release(x_258, 0);
 lean_ctor_release(x_258, 1);
 x_261 = x_258;
} else {
 lean_dec_ref(x_258);
 x_261 = lean_box(0);
}
x_262 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_handlePreRequestSpecialCases_x3f___lam__1___boxed), 1, 0);
x_263 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_handlePreRequestSpecialCases_x3f___lam__2___boxed), 2, 1);
lean_closure_set(x_263, 0, x_252);
x_264 = lean_array_size(x_259);
x_265 = l_Array_mapMUnsafe_map___at___Lean_Json_opt___at_____private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1558__spec__0_spec__0(x_264, x_257, x_259);
x_266 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_266, 0, x_265);
if (lean_is_scalar(x_261)) {
 x_267 = lean_alloc_ctor(0, 2, 0);
} else {
 x_267 = x_261;
}
lean_ctor_set(x_267, 0, x_266);
lean_ctor_set(x_267, 1, x_260);
x_268 = l_Prod_map(lean_box(0), lean_box(0), lean_box(0), lean_box(0), x_262, x_263, x_267);
x_269 = lean_ctor_get(x_268, 0);
lean_inc(x_269);
x_270 = lean_ctor_get(x_268, 1);
lean_inc(x_270);
lean_dec(x_268);
x_271 = lean_st_ref_set(x_242, x_270, x_253);
lean_dec(x_242);
x_272 = lean_ctor_get(x_271, 1);
lean_inc(x_272);
if (lean_is_exclusive(x_271)) {
 lean_ctor_release(x_271, 0);
 lean_ctor_release(x_271, 1);
 x_273 = x_271;
} else {
 lean_dec_ref(x_271);
 x_273 = lean_box(0);
}
x_274 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_274, 0, x_269);
lean_ctor_set_uint8(x_274, sizeof(void*)*1, x_234);
x_275 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_275, 0, x_274);
x_276 = lean_task_pure(x_275);
if (lean_is_scalar(x_243)) {
 x_277 = lean_alloc_ctor(1, 1, 0);
} else {
 x_277 = x_243;
}
lean_ctor_set(x_277, 0, x_276);
if (lean_is_scalar(x_273)) {
 x_278 = lean_alloc_ctor(0, 2, 0);
} else {
 x_278 = x_273;
}
lean_ctor_set(x_278, 0, x_277);
lean_ctor_set(x_278, 1, x_272);
return x_278;
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; 
lean_dec(x_243);
lean_dec(x_242);
lean_dec(x_6);
x_279 = lean_ctor_get(x_245, 0);
lean_inc(x_279);
x_280 = lean_ctor_get(x_245, 1);
lean_inc(x_280);
if (lean_is_exclusive(x_245)) {
 lean_ctor_release(x_245, 0);
 lean_ctor_release(x_245, 1);
 x_281 = x_245;
} else {
 lean_dec_ref(x_245);
 x_281 = lean_box(0);
}
if (lean_is_scalar(x_281)) {
 x_282 = lean_alloc_ctor(1, 2, 0);
} else {
 x_282 = x_281;
}
lean_ctor_set(x_282, 0, x_279);
lean_ctor_set(x_282, 1, x_280);
return x_282;
}
}
}
}
}
else
{
uint8_t x_283; 
lean_dec(x_6);
lean_dec(x_2);
x_283 = !lean_is_exclusive(x_112);
if (x_283 == 0)
{
return x_112;
}
else
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; 
x_284 = lean_ctor_get(x_112, 0);
x_285 = lean_ctor_get(x_112, 1);
lean_inc(x_285);
lean_inc(x_284);
lean_dec(x_112);
x_286 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_286, 0, x_284);
lean_ctor_set(x_286, 1, x_285);
return x_286;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___Lean_Server_FileWorker_handlePreRequestSpecialCases_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_RequestM_parseRequestParams___at___Lean_Server_FileWorker_handlePreRequestSpecialCases_x3f_spec__0(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Widget_instRpcEncodableDiagnosticWith_enc____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853____at___Lean_Server_FileWorker_handlePreRequestSpecialCases_x3f_spec__2_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = l_Array_mapMUnsafe_map___at___Lean_Widget_instRpcEncodableDiagnosticWith_enc____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853____at___Lean_Server_FileWorker_handlePreRequestSpecialCases_x3f_spec__2_spec__2(x_5, x_6, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Widget_instRpcEncodableDiagnosticWith_enc____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853____at___Lean_Server_FileWorker_handlePreRequestSpecialCases_x3f_spec__2_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = l_Array_mapMUnsafe_map___at___Lean_Widget_instRpcEncodableDiagnosticWith_enc____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853____at___Lean_Server_FileWorker_handlePreRequestSpecialCases_x3f_spec__2_spec__3(x_5, x_6, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Widget_instRpcEncodableDiagnosticWith_enc____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853____at___Lean_Server_FileWorker_handlePreRequestSpecialCases_x3f_spec__2_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = l_Array_mapMUnsafe_map___at___Lean_Widget_instRpcEncodableDiagnosticWith_enc____x40_Lean_Widget_InteractiveDiagnostic___hyg_1853____at___Lean_Server_FileWorker_handlePreRequestSpecialCases_x3f_spec__2_spec__4(x_5, x_6, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Server_FileWorker_handlePreRequestSpecialCases_x3f_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = l_Array_mapMUnsafe_map___at___Lean_Server_FileWorker_handlePreRequestSpecialCases_x3f_spec__6(x_5, x_6, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handlePreRequestSpecialCases_x3f___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_5);
lean_dec(x_5);
x_9 = l_Lean_Server_FileWorker_handlePreRequestSpecialCases_x3f___lam__0(x_1, x_2, x_3, x_4, x_8, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handlePreRequestSpecialCases_x3f___lam__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Server_FileWorker_handlePreRequestSpecialCases_x3f___lam__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handlePreRequestSpecialCases_x3f___lam__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_FileWorker_handlePreRequestSpecialCases_x3f___lam__2(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handlePreRequestSpecialCases_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Server_FileWorker_handlePreRequestSpecialCases_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Server_FileWorker_handlePostRequestSpecialCases_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_array_uget(x_3, x_2);
x_7 = l___private_Lean_Data_Lsp_CodeActions_0__Lean_Lsp_fromJsonCodeAction____x40_Lean_Data_Lsp_CodeActions___hyg_1205_(x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
lean_dec(x_3);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
return x_7;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
x_12 = lean_box(0);
x_13 = lean_array_uset(x_3, x_2, x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_usize_of_nat(x_14);
x_16 = lean_usize_add(x_2, x_15);
x_17 = lean_array_uset(x_13, x_2, x_11);
x_2 = x_16;
x_3 = x_17;
goto _start;
}
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Array_contains___at___Lean_Server_FileWorker_handlePostRequestSpecialCases_spec__1_spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = lean_string_dec_eq(x_1, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; size_t x_9; size_t x_10; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_usize_of_nat(x_8);
x_10 = lean_usize_add(x_3, x_9);
x_3 = x_10;
goto _start;
}
else
{
return x_7;
}
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_box(0);
x_13 = lean_unbox(x_12);
return x_13;
}
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___Lean_Server_FileWorker_handlePostRequestSpecialCases_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
if (x_5 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
size_t x_6; size_t x_7; uint8_t x_8; 
x_6 = lean_usize_of_nat(x_3);
x_7 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_8 = l_Array_anyMUnsafe_any___at___Array_contains___at___Lean_Server_FileWorker_handlePostRequestSpecialCases_spec__1_spec__1(x_2, x_1, x_6, x_7);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handlePostRequestSpecialCases___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_144; lean_object* x_206; lean_object* x_207; 
x_206 = lean_ctor_get(x_2, 4);
lean_inc(x_206);
x_207 = lean_ctor_get(x_206, 1);
lean_inc(x_207);
lean_dec(x_206);
if (lean_obj_tag(x_207) == 0)
{
goto block_143;
}
else
{
lean_object* x_208; lean_object* x_209; uint8_t x_210; 
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
lean_dec(x_207);
x_209 = lean_mk_string_unchecked("source", 6, 6);
x_210 = l_Array_contains___at___Lean_Server_FileWorker_handlePostRequestSpecialCases_spec__1(x_208, x_209);
lean_dec(x_209);
if (x_210 == 0)
{
lean_object* x_211; uint8_t x_212; 
x_211 = lean_mk_string_unchecked("source.organizeImports", 22, 22);
x_212 = l_Array_contains___at___Lean_Server_FileWorker_handlePostRequestSpecialCases_spec__1(x_208, x_211);
lean_dec(x_211);
lean_dec(x_208);
x_144 = x_212;
goto block_205;
}
else
{
lean_dec(x_208);
x_144 = x_210;
goto block_205;
}
}
block_143:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get(x_8, 3);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_ctor_get(x_2, 3);
lean_inc(x_10);
x_11 = l_Lean_FileMap_lspRangeToUtf8Range(x_9, x_10);
lean_dec(x_9);
lean_inc(x_11);
x_12 = l_Lean_Server_FileWorker_waitUnknownIdentifierRanges(x_1, x_11, x_6);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_16 = l_Array_isEmpty___redArg(x_14);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_4, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 4)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; size_t x_20; lean_object* x_21; size_t x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_array_size(x_19);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_usize_of_nat(x_21);
x_23 = l_Array_mapMUnsafe_map___at___Lean_Server_FileWorker_handlePostRequestSpecialCases_spec__0(x_20, x_22, x_19);
if (lean_obj_tag(x_23) == 0)
{
lean_dec(x_23);
lean_free_object(x_17);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_ctor_set(x_12, 0, x_4);
return x_12;
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_free_object(x_12);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec(x_23);
x_25 = l_Lean_Server_RequestM_checkCancelled(x_5, x_15);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; uint32_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_unsigned_to_nat(1000u);
x_28 = lean_uint32_of_nat(x_27);
x_29 = l_IO_sleep(x_28, x_26);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = l_Lean_Server_RequestM_checkCancelled(x_5, x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction(x_3, x_2, x_11, x_14, x_5, x_32);
lean_dec(x_14);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; size_t x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = l_Array_append(lean_box(0), x_24, x_35);
lean_dec(x_35);
x_37 = lean_array_size(x_36);
x_38 = l_Array_mapMUnsafe_map___at___Lean_Server_registerLspRequestHandler___at___Lean_Server_initFn____x40_Lean_Server_CodeActions_Basic___hyg_1213__spec__0_spec__2(x_37, x_22, x_36);
lean_ctor_set(x_17, 0, x_38);
x_39 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
lean_dec(x_4);
x_40 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_40, 0, x_17);
lean_ctor_set_uint8(x_40, sizeof(void*)*1, x_39);
lean_ctor_set(x_33, 0, x_40);
return x_33;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; size_t x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; 
x_41 = lean_ctor_get(x_33, 0);
x_42 = lean_ctor_get(x_33, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_33);
x_43 = l_Array_append(lean_box(0), x_24, x_41);
lean_dec(x_41);
x_44 = lean_array_size(x_43);
x_45 = l_Array_mapMUnsafe_map___at___Lean_Server_registerLspRequestHandler___at___Lean_Server_initFn____x40_Lean_Server_CodeActions_Basic___hyg_1213__spec__0_spec__2(x_44, x_22, x_43);
lean_ctor_set(x_17, 0, x_45);
x_46 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
lean_dec(x_4);
x_47 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_47, 0, x_17);
lean_ctor_set_uint8(x_47, sizeof(void*)*1, x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_42);
return x_48;
}
}
else
{
uint8_t x_49; 
lean_dec(x_24);
lean_free_object(x_17);
lean_dec(x_4);
x_49 = !lean_is_exclusive(x_33);
if (x_49 == 0)
{
return x_33;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_33, 0);
x_51 = lean_ctor_get(x_33, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_33);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_24);
lean_free_object(x_17);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_53 = !lean_is_exclusive(x_31);
if (x_53 == 0)
{
return x_31;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_31, 0);
x_55 = lean_ctor_get(x_31, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_31);
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
lean_dec(x_24);
lean_free_object(x_17);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_57 = !lean_is_exclusive(x_25);
if (x_57 == 0)
{
return x_25;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_25, 0);
x_59 = lean_ctor_get(x_25, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_25);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
}
else
{
lean_object* x_61; size_t x_62; lean_object* x_63; size_t x_64; lean_object* x_65; 
x_61 = lean_ctor_get(x_17, 0);
lean_inc(x_61);
lean_dec(x_17);
x_62 = lean_array_size(x_61);
x_63 = lean_unsigned_to_nat(0u);
x_64 = lean_usize_of_nat(x_63);
x_65 = l_Array_mapMUnsafe_map___at___Lean_Server_FileWorker_handlePostRequestSpecialCases_spec__0(x_62, x_64, x_61);
if (lean_obj_tag(x_65) == 0)
{
lean_dec(x_65);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_ctor_set(x_12, 0, x_4);
return x_12;
}
else
{
lean_object* x_66; lean_object* x_67; 
lean_free_object(x_12);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
lean_dec(x_65);
x_67 = l_Lean_Server_RequestM_checkCancelled(x_5, x_15);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; uint32_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
lean_dec(x_67);
x_69 = lean_unsigned_to_nat(1000u);
x_70 = lean_uint32_of_nat(x_69);
x_71 = l_IO_sleep(x_70, x_68);
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
lean_dec(x_71);
x_73 = l_Lean_Server_RequestM_checkCancelled(x_5, x_72);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
lean_dec(x_73);
x_75 = l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction(x_3, x_2, x_11, x_14, x_5, x_74);
lean_dec(x_14);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; size_t x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; 
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
x_79 = l_Array_append(lean_box(0), x_66, x_76);
lean_dec(x_76);
x_80 = lean_array_size(x_79);
x_81 = l_Array_mapMUnsafe_map___at___Lean_Server_registerLspRequestHandler___at___Lean_Server_initFn____x40_Lean_Server_CodeActions_Basic___hyg_1213__spec__0_spec__2(x_80, x_64, x_79);
x_82 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_82, 0, x_81);
x_83 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
lean_dec(x_4);
x_84 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set_uint8(x_84, sizeof(void*)*1, x_83);
if (lean_is_scalar(x_78)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_78;
}
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_77);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_66);
lean_dec(x_4);
x_86 = lean_ctor_get(x_75, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_75, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_88 = x_75;
} else {
 lean_dec_ref(x_75);
 x_88 = lean_box(0);
}
if (lean_is_scalar(x_88)) {
 x_89 = lean_alloc_ctor(1, 2, 0);
} else {
 x_89 = x_88;
}
lean_ctor_set(x_89, 0, x_86);
lean_ctor_set(x_89, 1, x_87);
return x_89;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_66);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_90 = lean_ctor_get(x_73, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_73, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_92 = x_73;
} else {
 lean_dec_ref(x_73);
 x_92 = lean_box(0);
}
if (lean_is_scalar(x_92)) {
 x_93 = lean_alloc_ctor(1, 2, 0);
} else {
 x_93 = x_92;
}
lean_ctor_set(x_93, 0, x_90);
lean_ctor_set(x_93, 1, x_91);
return x_93;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_66);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_94 = lean_ctor_get(x_67, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_67, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_96 = x_67;
} else {
 lean_dec_ref(x_67);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(1, 2, 0);
} else {
 x_97 = x_96;
}
lean_ctor_set(x_97, 0, x_94);
lean_ctor_set(x_97, 1, x_95);
return x_97;
}
}
}
}
else
{
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_ctor_set(x_12, 0, x_4);
return x_12;
}
}
else
{
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_ctor_set(x_12, 0, x_4);
return x_12;
}
}
else
{
lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_98 = lean_ctor_get(x_12, 0);
x_99 = lean_ctor_get(x_12, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_12);
x_100 = l_Array_isEmpty___redArg(x_98);
if (x_100 == 0)
{
lean_object* x_101; 
x_101 = lean_ctor_get(x_4, 0);
lean_inc(x_101);
if (lean_obj_tag(x_101) == 4)
{
lean_object* x_102; lean_object* x_103; size_t x_104; lean_object* x_105; size_t x_106; lean_object* x_107; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 x_103 = x_101;
} else {
 lean_dec_ref(x_101);
 x_103 = lean_box(0);
}
x_104 = lean_array_size(x_102);
x_105 = lean_unsigned_to_nat(0u);
x_106 = lean_usize_of_nat(x_105);
x_107 = l_Array_mapMUnsafe_map___at___Lean_Server_FileWorker_handlePostRequestSpecialCases_spec__0(x_104, x_106, x_102);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; 
lean_dec(x_107);
lean_dec(x_103);
lean_dec(x_98);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_4);
lean_ctor_set(x_108, 1, x_99);
return x_108;
}
else
{
lean_object* x_109; lean_object* x_110; 
x_109 = lean_ctor_get(x_107, 0);
lean_inc(x_109);
lean_dec(x_107);
x_110 = l_Lean_Server_RequestM_checkCancelled(x_5, x_99);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; uint32_t x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_111 = lean_ctor_get(x_110, 1);
lean_inc(x_111);
lean_dec(x_110);
x_112 = lean_unsigned_to_nat(1000u);
x_113 = lean_uint32_of_nat(x_112);
x_114 = l_IO_sleep(x_113, x_111);
x_115 = lean_ctor_get(x_114, 1);
lean_inc(x_115);
lean_dec(x_114);
x_116 = l_Lean_Server_RequestM_checkCancelled(x_5, x_115);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; 
x_117 = lean_ctor_get(x_116, 1);
lean_inc(x_117);
lean_dec(x_116);
x_118 = l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction(x_3, x_2, x_11, x_98, x_5, x_117);
lean_dec(x_98);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; size_t x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; lean_object* x_127; lean_object* x_128; 
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_121 = x_118;
} else {
 lean_dec_ref(x_118);
 x_121 = lean_box(0);
}
x_122 = l_Array_append(lean_box(0), x_109, x_119);
lean_dec(x_119);
x_123 = lean_array_size(x_122);
x_124 = l_Array_mapMUnsafe_map___at___Lean_Server_registerLspRequestHandler___at___Lean_Server_initFn____x40_Lean_Server_CodeActions_Basic___hyg_1213__spec__0_spec__2(x_123, x_106, x_122);
if (lean_is_scalar(x_103)) {
 x_125 = lean_alloc_ctor(4, 1, 0);
} else {
 x_125 = x_103;
}
lean_ctor_set(x_125, 0, x_124);
x_126 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
lean_dec(x_4);
x_127 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set_uint8(x_127, sizeof(void*)*1, x_126);
if (lean_is_scalar(x_121)) {
 x_128 = lean_alloc_ctor(0, 2, 0);
} else {
 x_128 = x_121;
}
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_120);
return x_128;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_109);
lean_dec(x_103);
lean_dec(x_4);
x_129 = lean_ctor_get(x_118, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_118, 1);
lean_inc(x_130);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_131 = x_118;
} else {
 lean_dec_ref(x_118);
 x_131 = lean_box(0);
}
if (lean_is_scalar(x_131)) {
 x_132 = lean_alloc_ctor(1, 2, 0);
} else {
 x_132 = x_131;
}
lean_ctor_set(x_132, 0, x_129);
lean_ctor_set(x_132, 1, x_130);
return x_132;
}
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec(x_109);
lean_dec(x_103);
lean_dec(x_98);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_133 = lean_ctor_get(x_116, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_116, 1);
lean_inc(x_134);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_135 = x_116;
} else {
 lean_dec_ref(x_116);
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
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_dec(x_109);
lean_dec(x_103);
lean_dec(x_98);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_137 = lean_ctor_get(x_110, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_110, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_139 = x_110;
} else {
 lean_dec_ref(x_110);
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
}
else
{
lean_object* x_141; 
lean_dec(x_101);
lean_dec(x_98);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_4);
lean_ctor_set(x_141, 1, x_99);
return x_141;
}
}
else
{
lean_object* x_142; 
lean_dec(x_98);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_4);
lean_ctor_set(x_142, 1, x_99);
return x_142;
}
}
}
block_205:
{
if (x_144 == 0)
{
goto block_143;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; uint8_t x_153; 
lean_dec(x_5);
lean_dec(x_3);
x_145 = lean_unsigned_to_nat(0u);
x_146 = lean_ctor_get(x_1, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
lean_dec(x_146);
x_148 = lean_ctor_get(x_147, 3);
lean_inc(x_148);
lean_dec(x_147);
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
lean_dec(x_148);
x_150 = lean_string_utf8_byte_size(x_149);
lean_dec(x_149);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_145);
lean_ctor_set(x_151, 1, x_150);
x_152 = l_Lean_Server_FileWorker_waitUnknownIdentifierRanges(x_1, x_151, x_6);
x_153 = !lean_is_exclusive(x_152);
if (x_153 == 0)
{
lean_object* x_154; uint8_t x_155; 
x_154 = lean_ctor_get(x_152, 0);
x_155 = l_Array_isEmpty___redArg(x_154);
lean_dec(x_154);
if (x_155 == 0)
{
lean_object* x_156; 
x_156 = lean_ctor_get(x_4, 0);
lean_inc(x_156);
if (lean_obj_tag(x_156) == 4)
{
uint8_t x_157; 
x_157 = !lean_is_exclusive(x_156);
if (x_157 == 0)
{
lean_object* x_158; size_t x_159; size_t x_160; lean_object* x_161; 
x_158 = lean_ctor_get(x_156, 0);
x_159 = lean_array_size(x_158);
x_160 = lean_usize_of_nat(x_145);
x_161 = l_Array_mapMUnsafe_map___at___Lean_Server_FileWorker_handlePostRequestSpecialCases_spec__0(x_159, x_160, x_158);
if (lean_obj_tag(x_161) == 0)
{
lean_dec(x_161);
lean_free_object(x_156);
lean_dec(x_2);
lean_ctor_set(x_152, 0, x_4);
return x_152;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; size_t x_166; lean_object* x_167; uint8_t x_168; lean_object* x_169; 
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
lean_dec(x_161);
x_163 = lean_mk_string_unchecked("source.organizeImports", 22, 22);
x_164 = l_Lean_Server_FileWorker_importAllUnknownIdentifiersCodeAction(x_2, x_163);
x_165 = lean_array_push(x_162, x_164);
x_166 = lean_array_size(x_165);
x_167 = l_Array_mapMUnsafe_map___at___Lean_Server_registerLspRequestHandler___at___Lean_Server_initFn____x40_Lean_Server_CodeActions_Basic___hyg_1213__spec__0_spec__2(x_166, x_160, x_165);
lean_ctor_set(x_156, 0, x_167);
x_168 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
lean_dec(x_4);
x_169 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_169, 0, x_156);
lean_ctor_set_uint8(x_169, sizeof(void*)*1, x_168);
lean_ctor_set(x_152, 0, x_169);
return x_152;
}
}
else
{
lean_object* x_170; size_t x_171; size_t x_172; lean_object* x_173; 
x_170 = lean_ctor_get(x_156, 0);
lean_inc(x_170);
lean_dec(x_156);
x_171 = lean_array_size(x_170);
x_172 = lean_usize_of_nat(x_145);
x_173 = l_Array_mapMUnsafe_map___at___Lean_Server_FileWorker_handlePostRequestSpecialCases_spec__0(x_171, x_172, x_170);
if (lean_obj_tag(x_173) == 0)
{
lean_dec(x_173);
lean_dec(x_2);
lean_ctor_set(x_152, 0, x_4);
return x_152;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; size_t x_178; lean_object* x_179; lean_object* x_180; uint8_t x_181; lean_object* x_182; 
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
lean_dec(x_173);
x_175 = lean_mk_string_unchecked("source.organizeImports", 22, 22);
x_176 = l_Lean_Server_FileWorker_importAllUnknownIdentifiersCodeAction(x_2, x_175);
x_177 = lean_array_push(x_174, x_176);
x_178 = lean_array_size(x_177);
x_179 = l_Array_mapMUnsafe_map___at___Lean_Server_registerLspRequestHandler___at___Lean_Server_initFn____x40_Lean_Server_CodeActions_Basic___hyg_1213__spec__0_spec__2(x_178, x_172, x_177);
x_180 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_180, 0, x_179);
x_181 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
lean_dec(x_4);
x_182 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_182, 0, x_180);
lean_ctor_set_uint8(x_182, sizeof(void*)*1, x_181);
lean_ctor_set(x_152, 0, x_182);
return x_152;
}
}
}
else
{
lean_dec(x_156);
lean_dec(x_2);
lean_ctor_set(x_152, 0, x_4);
return x_152;
}
}
else
{
lean_dec(x_2);
lean_ctor_set(x_152, 0, x_4);
return x_152;
}
}
else
{
lean_object* x_183; lean_object* x_184; uint8_t x_185; 
x_183 = lean_ctor_get(x_152, 0);
x_184 = lean_ctor_get(x_152, 1);
lean_inc(x_184);
lean_inc(x_183);
lean_dec(x_152);
x_185 = l_Array_isEmpty___redArg(x_183);
lean_dec(x_183);
if (x_185 == 0)
{
lean_object* x_186; 
x_186 = lean_ctor_get(x_4, 0);
lean_inc(x_186);
if (lean_obj_tag(x_186) == 4)
{
lean_object* x_187; lean_object* x_188; size_t x_189; size_t x_190; lean_object* x_191; 
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
if (lean_is_exclusive(x_186)) {
 lean_ctor_release(x_186, 0);
 x_188 = x_186;
} else {
 lean_dec_ref(x_186);
 x_188 = lean_box(0);
}
x_189 = lean_array_size(x_187);
x_190 = lean_usize_of_nat(x_145);
x_191 = l_Array_mapMUnsafe_map___at___Lean_Server_FileWorker_handlePostRequestSpecialCases_spec__0(x_189, x_190, x_187);
if (lean_obj_tag(x_191) == 0)
{
lean_object* x_192; 
lean_dec(x_191);
lean_dec(x_188);
lean_dec(x_2);
x_192 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_192, 0, x_4);
lean_ctor_set(x_192, 1, x_184);
return x_192;
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; size_t x_197; lean_object* x_198; lean_object* x_199; uint8_t x_200; lean_object* x_201; lean_object* x_202; 
x_193 = lean_ctor_get(x_191, 0);
lean_inc(x_193);
lean_dec(x_191);
x_194 = lean_mk_string_unchecked("source.organizeImports", 22, 22);
x_195 = l_Lean_Server_FileWorker_importAllUnknownIdentifiersCodeAction(x_2, x_194);
x_196 = lean_array_push(x_193, x_195);
x_197 = lean_array_size(x_196);
x_198 = l_Array_mapMUnsafe_map___at___Lean_Server_registerLspRequestHandler___at___Lean_Server_initFn____x40_Lean_Server_CodeActions_Basic___hyg_1213__spec__0_spec__2(x_197, x_190, x_196);
if (lean_is_scalar(x_188)) {
 x_199 = lean_alloc_ctor(4, 1, 0);
} else {
 x_199 = x_188;
}
lean_ctor_set(x_199, 0, x_198);
x_200 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
lean_dec(x_4);
x_201 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set_uint8(x_201, sizeof(void*)*1, x_200);
x_202 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_202, 0, x_201);
lean_ctor_set(x_202, 1, x_184);
return x_202;
}
}
else
{
lean_object* x_203; 
lean_dec(x_186);
lean_dec(x_2);
x_203 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_203, 0, x_4);
lean_ctor_set(x_203, 1, x_184);
return x_203;
}
}
else
{
lean_object* x_204; 
lean_dec(x_2);
x_204 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_204, 0, x_4);
lean_ctor_set(x_204, 1, x_184);
return x_204;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handlePostRequestSpecialCases(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_Server_RequestM_readDoc___at___Lean_Server_RequestM_withWaitFindSnapAtPos_spec__0(x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_mk_string_unchecked("textDocument/codeAction", 23, 23);
x_12 = lean_string_dec_eq(x_2, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
lean_ctor_set(x_7, 0, x_4);
return x_7;
}
else
{
lean_object* x_13; 
x_13 = l___private_Lean_Data_Lsp_CodeActions_0__Lean_Lsp_fromJsonCodeActionParams____x40_Lean_Data_Lsp_CodeActions___hyg_390_(x_3);
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
lean_ctor_set(x_7, 0, x_4);
return x_7;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_free_object(x_7);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_handlePostRequestSpecialCases___lam__0), 6, 3);
lean_closure_set(x_15, 0, x_9);
lean_closure_set(x_15, 1, x_14);
lean_closure_set(x_15, 2, x_1);
x_16 = l_Lean_Server_RequestM_mapRequestTaskCostly___redArg(x_4, x_15, x_5, x_10);
return x_16;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_7, 0);
x_18 = lean_ctor_get(x_7, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_7);
x_19 = lean_mk_string_unchecked("textDocument/codeAction", 23, 23);
x_20 = lean_string_dec_eq(x_2, x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_17);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_4);
lean_ctor_set(x_21, 1, x_18);
return x_21;
}
else
{
lean_object* x_22; 
x_22 = l___private_Lean_Data_Lsp_CodeActions_0__Lean_Lsp_fromJsonCodeActionParams____x40_Lean_Data_Lsp_CodeActions___hyg_390_(x_3);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
lean_dec(x_22);
lean_dec(x_17);
lean_dec(x_5);
lean_dec(x_1);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_4);
lean_ctor_set(x_23, 1, x_18);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_handlePostRequestSpecialCases___lam__0), 6, 3);
lean_closure_set(x_25, 0, x_17);
lean_closure_set(x_25, 1, x_24);
lean_closure_set(x_25, 2, x_1);
x_26 = l_Lean_Server_RequestM_mapRequestTaskCostly___redArg(x_4, x_25, x_5, x_18);
return x_26;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Server_FileWorker_handlePostRequestSpecialCases_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lean_Server_FileWorker_handlePostRequestSpecialCases_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Array_contains___at___Lean_Server_FileWorker_handlePostRequestSpecialCases_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at___Array_contains___at___Lean_Server_FileWorker_handlePostRequestSpecialCases_spec__1_spec__1(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___Lean_Server_FileWorker_handlePostRequestSpecialCases_spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_contains___at___Lean_Server_FileWorker_handlePostRequestSpecialCases_spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handlePostRequestSpecialCases___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Server_FileWorker_handlePostRequestSpecialCases(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_emitRequestResponse_emitResponse___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_5, x_6);
if (x_1 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
lean_inc(x_4);
x_11 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_7);
lean_ctor_set(x_11, 2, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_2);
x_12 = lean_box(0);
lean_inc(x_4);
x_13 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_7);
lean_ctor_set(x_13, 2, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_emitRequestResponse_emitResponse(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = l_Std_Channel_Sync_send___redArg(x_6, x_3, x_5);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_io_mono_ms_now(x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_box(x_4);
x_13 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_emitRequestResponse_emitResponse___lam__0___boxed), 3, 2);
lean_closure_set(x_13, 0, x_12);
lean_closure_set(x_13, 1, x_10);
x_14 = l_Lean_Server_FileWorker_WorkerContext_modifyPartialHandler(x_2, x_1, x_13, x_11);
lean_dec(x_2);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
return x_14;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_14);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_emitRequestResponse_emitResponse___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_Server_FileWorker_emitRequestResponse_emitResponse___lam__0(x_4, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_emitRequestResponse_emitResponse___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_4);
lean_dec(x_4);
x_7 = l_Lean_Server_FileWorker_emitRequestResponse_emitResponse(x_1, x_2, x_3, x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_emitRequestResponse___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = l_Lean_Server_RequestError_toLspResponseError(x_1, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get_uint8(x_8, sizeof(void*)*3);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_11);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set_uint8(x_13, sizeof(void*)*3, x_10);
x_14 = lean_box(0);
x_15 = lean_unbox(x_14);
x_16 = l_Lean_Server_FileWorker_emitRequestResponse_emitResponse(x_2, x_3, x_13, x_15, x_6);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_5, 0);
x_18 = l_Lean_Server_RequestCancellationToken_wasCancelledByCancelRequest(x_4, x_6);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_18, 1);
x_23 = lean_ctor_get(x_18, 0);
lean_dec(x_23);
x_24 = lean_ctor_get(x_17, 0);
lean_inc(x_24);
lean_ctor_set_tag(x_18, 2);
lean_ctor_set(x_18, 1, x_24);
lean_ctor_set(x_18, 0, x_1);
x_25 = lean_ctor_get_uint8(x_17, sizeof(void*)*1);
x_26 = l_Lean_Server_FileWorker_emitRequestResponse_emitResponse(x_2, x_3, x_18, x_25, x_22);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_18, 1);
lean_inc(x_27);
lean_dec(x_18);
x_28 = lean_ctor_get(x_17, 0);
lean_inc(x_28);
x_29 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_29, 0, x_1);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_ctor_get_uint8(x_17, sizeof(void*)*1);
x_31 = l_Lean_Server_FileWorker_emitRequestResponse_emitResponse(x_2, x_3, x_29, x_30, x_27);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; uint8_t x_43; 
x_32 = lean_ctor_get(x_18, 1);
lean_inc(x_32);
lean_dec(x_18);
x_33 = l_Lean_Server_RequestError_requestCancelled;
x_34 = l_Lean_Server_RequestError_toLspResponseError(x_1, x_33);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get_uint8(x_34, sizeof(void*)*3);
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_dec(x_34);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(x_39, 0, x_35);
lean_ctor_set(x_39, 1, x_37);
lean_ctor_set(x_39, 2, x_38);
lean_ctor_set_uint8(x_39, sizeof(void*)*3, x_36);
x_40 = lean_box(0);
x_41 = lean_unbox(x_40);
x_42 = l_Lean_Server_FileWorker_emitRequestResponse_emitResponse(x_2, x_3, x_39, x_41, x_32);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_42, 0);
lean_dec(x_44);
x_45 = lean_box(0);
lean_ctor_set(x_42, 0, x_45);
return x_42;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_42, 1);
lean_inc(x_46);
lean_dec(x_42);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_emitRequestResponse___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_7; 
lean_dec(x_2);
x_7 = !lean_is_exclusive(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; uint8_t x_18; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = l_Lean_Server_RequestError_toLspResponseError(x_3, x_8);
lean_dec(x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get_uint8(x_9, sizeof(void*)*3);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_12);
lean_ctor_set(x_14, 2, x_13);
lean_ctor_set_uint8(x_14, sizeof(void*)*3, x_11);
x_15 = lean_box(0);
x_16 = lean_unbox(x_15);
x_17 = l_Lean_Server_FileWorker_emitRequestResponse_emitResponse(x_4, x_5, x_14, x_16, x_6);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
x_20 = lean_box(0);
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 0, x_20);
x_21 = lean_task_pure(x_1);
lean_ctor_set(x_17, 0, x_21);
return x_17;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_dec(x_17);
x_23 = lean_box(0);
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 0, x_23);
x_24 = lean_task_pure(x_1);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_26 = lean_ctor_get(x_1, 0);
lean_inc(x_26);
lean_dec(x_1);
x_27 = l_Lean_Server_RequestError_toLspResponseError(x_3, x_26);
lean_dec(x_26);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get_uint8(x_27, sizeof(void*)*3);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(x_32, 0, x_28);
lean_ctor_set(x_32, 1, x_30);
lean_ctor_set(x_32, 2, x_31);
lean_ctor_set_uint8(x_32, sizeof(void*)*3, x_29);
x_33 = lean_box(0);
x_34 = lean_unbox(x_33);
x_35 = l_Lean_Server_FileWorker_emitRequestResponse_emitResponse(x_4, x_5, x_32, x_34, x_6);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_37 = x_35;
} else {
 lean_dec_ref(x_35);
 x_37 = lean_box(0);
}
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_40 = lean_task_pure(x_39);
if (lean_is_scalar(x_37)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_37;
}
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_36);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_42 = lean_ctor_get(x_1, 0);
lean_inc(x_42);
lean_dec(x_1);
x_43 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_emitRequestResponse___redArg___lam__0___boxed), 6, 4);
lean_closure_set(x_43, 0, x_3);
lean_closure_set(x_43, 1, x_4);
lean_closure_set(x_43, 2, x_5);
lean_closure_set(x_43, 3, x_2);
x_44 = l_Lean_Server_ServerTask_IO_mapTaskCheap___redArg(x_43, x_42, x_6);
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
return x_44;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_44, 0);
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_44);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_emitRequestResponse(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Server_FileWorker_emitRequestResponse___redArg(x_1, x_2, x_3, x_4, x_5, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_emitRequestResponse___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Server_FileWorker_emitRequestResponse___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_emitRequestResponse___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Server_FileWorker_emitRequestResponse(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleRequest___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_add(x_3, x_4);
x_6 = lean_box(0);
lean_inc(x_2);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set(x_7, 2, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleRequest(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_handleRequest___lam__0___boxed), 1, 0);
lean_inc(x_2);
x_11 = l_Lean_Server_FileWorker_WorkerContext_modifyPartialHandler(x_4, x_2, x_10, x_9);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_13 = l_Lean_Server_FileWorker_handleStatefulPreRequestSpecialCases(x_1, x_2, x_3, x_4, x_5, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_31; lean_object* x_32; lean_object* x_35; lean_object* x_36; lean_object* x_39; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = l_Lean_Server_RequestCancellationToken_new(x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_45 = lean_ctor_get(x_8, 4);
lean_inc(x_45);
x_46 = lean_ctor_get(x_8, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_4, 6);
lean_inc(x_47);
x_48 = lean_ctor_get(x_4, 7);
lean_inc(x_48);
lean_inc(x_4);
x_49 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_sendUntypedServerRequest), 4, 1);
lean_closure_set(x_49, 0, x_4);
lean_inc(x_18);
x_50 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_50, 0, x_45);
lean_ctor_set(x_50, 1, x_46);
lean_ctor_set(x_50, 2, x_47);
lean_ctor_set(x_50, 3, x_48);
lean_ctor_set(x_50, 4, x_18);
lean_ctor_set(x_50, 5, x_49);
lean_inc(x_50);
lean_inc(x_3);
lean_inc(x_1);
x_51 = l_Lean_Server_FileWorker_handlePreRequestSpecialCases_x3f(x_4, x_8, x_1, x_2, x_3, x_50, x_19);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
lean_inc(x_50);
lean_inc(x_3);
x_54 = l_Lean_Server_handleLspRequest(x_2, x_3, x_50, x_53);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
lean_inc(x_1);
x_57 = l_Lean_Server_FileWorker_handlePostRequestSpecialCases(x_1, x_2, x_3, x_55, x_50, x_56);
x_39 = x_57;
goto block_44;
}
else
{
lean_dec(x_50);
lean_dec(x_3);
x_39 = x_54;
goto block_44;
}
}
else
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_50);
lean_dec(x_3);
x_58 = lean_ctor_get(x_51, 1);
lean_inc(x_58);
lean_dec(x_51);
x_59 = lean_ctor_get(x_52, 0);
lean_inc(x_59);
lean_dec(x_52);
x_35 = x_59;
x_36 = x_58;
goto block_38;
}
}
else
{
lean_object* x_60; lean_object* x_61; 
lean_dec(x_50);
lean_dec(x_3);
x_60 = lean_ctor_get(x_51, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_51, 1);
lean_inc(x_61);
lean_dec(x_51);
x_31 = x_60;
x_32 = x_61;
goto block_34;
}
block_30:
{
lean_object* x_22; uint8_t x_23; 
lean_inc(x_1);
lean_inc(x_18);
x_22 = l_Lean_Server_FileWorker_emitRequestResponse___redArg(x_20, x_18, x_1, x_2, x_4, x_21);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 1);
lean_ctor_set(x_22, 1, x_18);
x_25 = l_Lean_Server_FileWorker_queueRequest___redArg(x_1, x_22, x_5, x_24);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_22, 0);
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_22);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_18);
x_29 = l_Lean_Server_FileWorker_queueRequest___redArg(x_1, x_28, x_5, x_27);
return x_29;
}
}
block_34:
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_31);
x_20 = x_33;
x_21 = x_32;
goto block_30;
}
block_38:
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_35);
x_20 = x_37;
x_21 = x_36;
goto block_30;
}
block_44:
{
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_35 = x_40;
x_36 = x_41;
goto block_38;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_39, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_39, 1);
lean_inc(x_43);
lean_dec(x_39);
x_31 = x_42;
x_32 = x_43;
goto block_34;
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_62 = !lean_is_exclusive(x_13);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_13, 0);
lean_dec(x_63);
x_64 = lean_box(0);
lean_ctor_set(x_13, 0, x_64);
return x_13;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_13, 1);
lean_inc(x_65);
lean_dec(x_13);
x_66 = lean_box(0);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleRequest___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Server_FileWorker_handleRequest___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleRequest___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Server_FileWorker_handleRequest(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleResponse___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_2);
x_6 = l_Lean_Server_FileWorker_WorkerContext_resolveServerRequestResponse(x_3, x_1, x_5, x_4);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
return x_6;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_6);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleResponse(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Server_FileWorker_handleResponse___redArg(x_1, x_2, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleResponse___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_FileWorker_handleResponse___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleResponse___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Server_FileWorker_handleResponse(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleResponseError___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*1, x_2);
x_7 = l_Lean_Server_FileWorker_WorkerContext_resolveServerRequestResponse(x_4, x_1, x_6, x_5);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
return x_7;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleResponseError(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Server_FileWorker_handleResponseError___redArg(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleResponseError___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_Lean_Server_FileWorker_handleResponseError___redArg(x_1, x_6, x_3, x_4, x_5);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleResponseError___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_2);
lean_dec(x_2);
x_8 = l_Lean_Server_FileWorker_handleResponseError(x_1, x_7, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_Server_FileWorker_mainLoop_spec__0_spec__0___redArg(uint64_t x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_2;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; uint8_t x_9; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_ctor_get(x_2, 3);
x_8 = lean_unbox_uint64(x_5);
x_9 = lean_uint64_dec_lt(x_1, x_8);
if (x_9 == 0)
{
uint64_t x_10; uint8_t x_11; 
x_10 = lean_unbox_uint64(x_5);
x_11 = lean_uint64_dec_eq(x_1, x_10);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = l_Lean_RBNode_isBlack___redArg(x_7);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_box(0);
x_14 = l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_Server_FileWorker_mainLoop_spec__0_spec__0___redArg(x_1, x_7);
lean_ctor_set(x_2, 3, x_14);
x_15 = lean_unbox(x_13);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_15);
return x_2;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_free_object(x_2);
x_16 = l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_Server_FileWorker_mainLoop_spec__0_spec__0___redArg(x_1, x_7);
x_17 = l_Lean_RBNode_balRight(lean_box(0), lean_box(0), x_4, x_5, x_6, x_16);
return x_17;
}
}
else
{
lean_object* x_18; 
lean_free_object(x_2);
lean_dec(x_6);
lean_dec(x_5);
x_18 = l_Lean_RBNode_appendTrees___redArg(x_4, x_7);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = l_Lean_RBNode_isBlack___redArg(x_4);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_box(0);
x_21 = l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_Server_FileWorker_mainLoop_spec__0_spec__0___redArg(x_1, x_4);
lean_ctor_set(x_2, 0, x_21);
x_22 = lean_unbox(x_20);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_22);
return x_2;
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_free_object(x_2);
x_23 = l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_Server_FileWorker_mainLoop_spec__0_spec__0___redArg(x_1, x_4);
x_24 = l_Lean_RBNode_balLeft___redArg(x_23, x_5, x_6, x_7);
return x_24;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint64_t x_29; uint8_t x_30; 
x_25 = lean_ctor_get(x_2, 0);
x_26 = lean_ctor_get(x_2, 1);
x_27 = lean_ctor_get(x_2, 2);
x_28 = lean_ctor_get(x_2, 3);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_2);
x_29 = lean_unbox_uint64(x_26);
x_30 = lean_uint64_dec_lt(x_1, x_29);
if (x_30 == 0)
{
uint64_t x_31; uint8_t x_32; 
x_31 = lean_unbox_uint64(x_26);
x_32 = lean_uint64_dec_eq(x_1, x_31);
if (x_32 == 0)
{
uint8_t x_33; 
x_33 = l_Lean_RBNode_isBlack___redArg(x_28);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_34 = lean_box(0);
x_35 = l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_Server_FileWorker_mainLoop_spec__0_spec__0___redArg(x_1, x_28);
x_36 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_36, 0, x_25);
lean_ctor_set(x_36, 1, x_26);
lean_ctor_set(x_36, 2, x_27);
lean_ctor_set(x_36, 3, x_35);
x_37 = lean_unbox(x_34);
lean_ctor_set_uint8(x_36, sizeof(void*)*4, x_37);
return x_36;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_Server_FileWorker_mainLoop_spec__0_spec__0___redArg(x_1, x_28);
x_39 = l_Lean_RBNode_balRight(lean_box(0), lean_box(0), x_25, x_26, x_27, x_38);
return x_39;
}
}
else
{
lean_object* x_40; 
lean_dec(x_27);
lean_dec(x_26);
x_40 = l_Lean_RBNode_appendTrees___redArg(x_25, x_28);
return x_40;
}
}
else
{
uint8_t x_41; 
x_41 = l_Lean_RBNode_isBlack___redArg(x_25);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_42 = lean_box(0);
x_43 = l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_Server_FileWorker_mainLoop_spec__0_spec__0___redArg(x_1, x_25);
x_44 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_26);
lean_ctor_set(x_44, 2, x_27);
lean_ctor_set(x_44, 3, x_28);
x_45 = lean_unbox(x_42);
lean_ctor_set_uint8(x_44, sizeof(void*)*4, x_45);
return x_44;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_Server_FileWorker_mainLoop_spec__0_spec__0___redArg(x_1, x_25);
x_47 = l_Lean_RBNode_balLeft___redArg(x_46, x_26, x_27, x_28);
return x_47;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_Server_FileWorker_mainLoop_spec__0_spec__0(lean_object* x_1, uint64_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_Server_FileWorker_mainLoop_spec__0_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___at___Lean_Server_FileWorker_mainLoop_spec__0___redArg(uint64_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_Server_FileWorker_mainLoop_spec__0_spec__0___redArg(x_1, x_2);
x_4 = l_Lean_RBNode_setBlack___redArg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___at___Lean_Server_FileWorker_mainLoop_spec__0(lean_object* x_1, uint64_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_erase___at___Lean_Server_FileWorker_mainLoop_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___at___Lean_RBNode_foldM___at___Lean_Server_FileWorker_mainLoop_spec__2_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 3);
lean_inc(x_8);
lean_dec(x_2);
x_9 = l_Lean_RBNode_foldM___at___Lean_RBNode_foldM___at___Lean_Server_FileWorker_mainLoop_spec__2_spec__2___redArg(x_1, x_5, x_3);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_16 = lean_ctor_get(x_7, 0);
lean_inc(x_16);
lean_dec(x_7);
x_17 = l_Lean_Server_ServerTask_hasFinished(lean_box(0), x_16, x_11);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_unbox(x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_16);
lean_dec(x_6);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_1 = x_10;
x_2 = x_8;
x_3 = x_20;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_dec(x_17);
x_23 = lean_task_get_own(x_16);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_10);
lean_dec(x_8);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_mk_string_unchecked("Failed responding to request ", 29, 29);
switch (lean_obj_tag(x_6)) {
case 0:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_6, 0);
lean_inc(x_38);
lean_dec(x_6);
x_39 = lean_mk_string_unchecked("\"", 1, 1);
lean_inc(x_39);
x_40 = lean_string_append(x_39, x_38);
lean_dec(x_38);
x_41 = lean_string_append(x_40, x_39);
lean_dec(x_39);
x_26 = x_41;
goto block_37;
}
case 1:
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_6, 0);
lean_inc(x_42);
lean_dec(x_6);
x_43 = l_Lean_JsonNumber_toString(x_42);
x_26 = x_43;
goto block_37;
}
default: 
{
lean_object* x_44; 
x_44 = lean_mk_string_unchecked("null", 4, 4);
x_26 = x_44;
goto block_37;
}
}
block_37:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_27 = lean_string_append(x_25, x_26);
lean_dec(x_26);
x_28 = lean_mk_string_unchecked(": ", 2, 2);
x_29 = lean_string_append(x_27, x_28);
lean_dec(x_28);
x_30 = lean_io_error_to_string(x_24);
x_31 = lean_string_append(x_29, x_30);
lean_dec(x_30);
x_32 = l_IO_throwServerError(lean_box(0), x_31, x_22);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
return x_32;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_32);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_dec(x_23);
x_12 = x_22;
goto block_15;
}
}
block_15:
{
lean_object* x_13; 
x_13 = l_Lean_RBNode_erase___at___Lean_Server_FileWorker_handleCancelRequest_spec__1___redArg(x_6, x_10);
x_1 = x_13;
x_2 = x_8;
x_3 = x_12;
goto _start;
}
}
else
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___at___Lean_RBNode_foldM___at___Lean_Server_FileWorker_mainLoop_spec__2_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_RBNode_foldM___at___Lean_RBNode_foldM___at___Lean_Server_FileWorker_mainLoop_spec__2_spec__2___redArg(x_1, x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___at___Lean_Server_FileWorker_mainLoop_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 3);
lean_inc(x_10);
lean_dec(x_2);
x_11 = l_Lean_RBNode_foldM___at___Lean_RBNode_foldM___at___Lean_Server_FileWorker_mainLoop_spec__2_spec__2___redArg(x_1, x_7, x_5);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_18 = lean_ctor_get(x_9, 0);
lean_inc(x_18);
lean_dec(x_9);
x_19 = l_Lean_Server_ServerTask_hasFinished(lean_box(0), x_18, x_13);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_unbox(x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_18);
lean_dec(x_8);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = l_Lean_RBNode_foldM___at___Lean_RBNode_foldM___at___Lean_Server_FileWorker_mainLoop_spec__2_spec__2___redArg(x_12, x_10, x_22);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_dec(x_19);
x_25 = lean_task_get_own(x_18);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_12);
lean_dec(x_10);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_mk_string_unchecked("Failed responding to request ", 29, 29);
switch (lean_obj_tag(x_8)) {
case 0:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_8, 0);
lean_inc(x_40);
lean_dec(x_8);
x_41 = lean_mk_string_unchecked("\"", 1, 1);
lean_inc(x_41);
x_42 = lean_string_append(x_41, x_40);
lean_dec(x_40);
x_43 = lean_string_append(x_42, x_41);
lean_dec(x_41);
x_28 = x_43;
goto block_39;
}
case 1:
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_8, 0);
lean_inc(x_44);
lean_dec(x_8);
x_45 = l_Lean_JsonNumber_toString(x_44);
x_28 = x_45;
goto block_39;
}
default: 
{
lean_object* x_46; 
x_46 = lean_mk_string_unchecked("null", 4, 4);
x_28 = x_46;
goto block_39;
}
}
block_39:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_29 = lean_string_append(x_27, x_28);
lean_dec(x_28);
x_30 = lean_mk_string_unchecked(": ", 2, 2);
x_31 = lean_string_append(x_29, x_30);
lean_dec(x_30);
x_32 = lean_io_error_to_string(x_26);
x_33 = lean_string_append(x_31, x_32);
lean_dec(x_32);
x_34 = l_IO_throwServerError(lean_box(0), x_33, x_24);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
return x_34;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_34, 0);
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_34);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
lean_dec(x_25);
x_14 = x_24;
goto block_17;
}
}
block_17:
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_Lean_RBNode_erase___at___Lean_Server_FileWorker_handleCancelRequest_spec__1___redArg(x_8, x_12);
x_16 = l_Lean_RBNode_foldM___at___Lean_RBNode_foldM___at___Lean_Server_FileWorker_mainLoop_spec__2_spec__2___redArg(x_15, x_10, x_14);
return x_16;
}
}
else
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at___Lean_Server_FileWorker_mainLoop_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_2);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 3);
lean_inc(x_9);
lean_dec(x_1);
x_10 = l_Lean_RBNode_forIn_visit___at___Lean_Server_FileWorker_mainLoop_spec__4___redArg(x_6, x_2, x_3);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_st_ref_get(x_8, x_12);
lean_dec(x_8);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Server_FileWorker_RpcSession_hasExpired(x_15, x_16);
lean_dec(x_15);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_unbox(x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_7);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_1 = x_9;
x_2 = x_13;
x_3 = x_20;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint64_t x_28; lean_object* x_29; lean_object* x_30; 
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_dec(x_17);
x_23 = lean_ctor_get(x_13, 4);
lean_inc(x_23);
x_24 = lean_ctor_get(x_13, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_13, 1);
lean_inc(x_25);
x_26 = lean_ctor_get(x_13, 2);
lean_inc(x_26);
x_27 = lean_ctor_get(x_13, 3);
lean_inc(x_27);
lean_dec(x_13);
x_28 = lean_unbox_uint64(x_7);
lean_dec(x_7);
x_29 = l_Lean_RBNode_erase___at___Lean_Server_FileWorker_mainLoop_spec__0___redArg(x_28, x_23);
x_30 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_30, 0, x_24);
lean_ctor_set(x_30, 1, x_25);
lean_ctor_set(x_30, 2, x_26);
lean_ctor_set(x_30, 3, x_27);
lean_ctor_set(x_30, 4, x_29);
x_1 = x_9;
x_2 = x_30;
x_3 = x_22;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at___Lean_Server_FileWorker_mainLoop_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_RBNode_forIn_visit___at___Lean_Server_FileWorker_mainLoop_spec__4___redArg(x_1, x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_mainLoop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_st_ref_get(x_3, x_4);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
lean_inc(x_1);
x_41 = l_IO_FS_Stream_readLspMessage(x_1, x_40);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_ctor_get(x_39, 3);
lean_inc(x_44);
lean_inc(x_44);
x_45 = l_Lean_RBNode_foldM___at___Lean_Server_FileWorker_mainLoop_spec__2(x_44, x_44, x_2, x_3, x_43);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_106; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_ctor_get(x_39, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_39, 1);
lean_inc(x_49);
x_50 = lean_ctor_get(x_39, 2);
lean_inc(x_50);
x_51 = lean_ctor_get(x_39, 4);
lean_inc(x_51);
lean_dec(x_39);
lean_inc(x_51);
x_52 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_52, 0, x_48);
lean_ctor_set(x_52, 1, x_49);
lean_ctor_set(x_52, 2, x_50);
lean_ctor_set(x_52, 3, x_46);
lean_ctor_set(x_52, 4, x_51);
x_53 = l_Lean_RBNode_forIn_visit___at___Lean_Server_FileWorker_mainLoop_spec__4___redArg(x_51, x_52, x_47);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_106 = lean_ctor_get(x_54, 0);
lean_inc(x_106);
lean_dec(x_54);
x_56 = x_106;
goto block_105;
block_105:
{
lean_object* x_57; 
x_57 = lean_st_ref_set(x_3, x_56, x_55);
switch (lean_obj_tag(x_42)) {
case 0:
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_42, 2);
lean_inc(x_58);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; 
lean_dec(x_42);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_5 = x_59;
goto block_8;
}
else
{
lean_object* x_60; 
x_60 = lean_ctor_get(x_58, 0);
lean_inc(x_60);
lean_dec(x_58);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_61 = lean_ctor_get(x_57, 1);
lean_inc(x_61);
lean_dec(x_57);
x_62 = lean_ctor_get(x_42, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_42, 1);
lean_inc(x_63);
lean_dec(x_42);
x_64 = !lean_is_exclusive(x_60);
if (x_64 == 0)
{
lean_ctor_set_tag(x_60, 4);
x_9 = x_62;
x_10 = x_63;
x_11 = x_61;
x_12 = x_60;
goto block_16;
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_60, 0);
lean_inc(x_65);
lean_dec(x_60);
x_66 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_66, 0, x_65);
x_9 = x_62;
x_10 = x_63;
x_11 = x_61;
x_12 = x_66;
goto block_16;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_67 = lean_ctor_get(x_57, 1);
lean_inc(x_67);
lean_dec(x_57);
x_68 = lean_ctor_get(x_42, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_42, 1);
lean_inc(x_69);
lean_dec(x_42);
x_70 = !lean_is_exclusive(x_60);
if (x_70 == 0)
{
lean_ctor_set_tag(x_60, 5);
x_9 = x_68;
x_10 = x_69;
x_11 = x_67;
x_12 = x_60;
goto block_16;
}
else
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_60, 0);
lean_inc(x_71);
lean_dec(x_60);
x_72 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_72, 0, x_71);
x_9 = x_68;
x_10 = x_69;
x_11 = x_67;
x_12 = x_72;
goto block_16;
}
}
}
}
case 1:
{
uint8_t x_73; 
x_73 = !lean_is_exclusive(x_57);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_74 = lean_ctor_get(x_57, 1);
x_75 = lean_ctor_get(x_57, 0);
lean_dec(x_75);
x_76 = lean_ctor_get(x_42, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_42, 1);
lean_inc(x_77);
lean_dec(x_42);
x_78 = lean_mk_string_unchecked("exit", 4, 4);
x_79 = lean_string_dec_eq(x_76, x_78);
if (x_79 == 0)
{
lean_dec(x_78);
lean_free_object(x_57);
if (lean_obj_tag(x_77) == 0)
{
lean_dec(x_76);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = x_74;
goto block_8;
}
else
{
lean_object* x_80; 
x_80 = lean_ctor_get(x_77, 0);
lean_inc(x_80);
lean_dec(x_77);
x_26 = x_76;
x_27 = x_80;
x_28 = x_2;
x_29 = x_3;
x_30 = x_74;
goto block_37;
}
}
else
{
lean_dec(x_76);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_81; 
lean_dec(x_78);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_81 = lean_box(0);
lean_ctor_set(x_57, 0, x_81);
return x_57;
}
else
{
lean_object* x_82; 
lean_free_object(x_57);
x_82 = lean_ctor_get(x_77, 0);
lean_inc(x_82);
lean_dec(x_77);
x_26 = x_78;
x_27 = x_82;
x_28 = x_2;
x_29 = x_3;
x_30 = x_74;
goto block_37;
}
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_83 = lean_ctor_get(x_57, 1);
lean_inc(x_83);
lean_dec(x_57);
x_84 = lean_ctor_get(x_42, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_42, 1);
lean_inc(x_85);
lean_dec(x_42);
x_86 = lean_mk_string_unchecked("exit", 4, 4);
x_87 = lean_string_dec_eq(x_84, x_86);
if (x_87 == 0)
{
lean_dec(x_86);
if (lean_obj_tag(x_85) == 0)
{
lean_dec(x_84);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = x_83;
goto block_8;
}
else
{
lean_object* x_88; 
x_88 = lean_ctor_get(x_85, 0);
lean_inc(x_88);
lean_dec(x_85);
x_26 = x_84;
x_27 = x_88;
x_28 = x_2;
x_29 = x_3;
x_30 = x_83;
goto block_37;
}
}
else
{
lean_dec(x_84);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_89; lean_object* x_90; 
lean_dec(x_86);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_89 = lean_box(0);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_83);
return x_90;
}
else
{
lean_object* x_91; 
x_91 = lean_ctor_get(x_85, 0);
lean_inc(x_91);
lean_dec(x_85);
x_26 = x_86;
x_27 = x_91;
x_28 = x_2;
x_29 = x_3;
x_30 = x_83;
goto block_37;
}
}
}
}
case 2:
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_92 = lean_ctor_get(x_57, 1);
lean_inc(x_92);
lean_dec(x_57);
x_93 = lean_ctor_get(x_42, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_42, 1);
lean_inc(x_94);
lean_dec(x_42);
x_95 = l_Lean_Server_FileWorker_handleResponse___redArg(x_93, x_94, x_2, x_92);
x_96 = lean_ctor_get(x_95, 1);
lean_inc(x_96);
lean_dec(x_95);
x_4 = x_96;
goto _start;
}
default: 
{
lean_object* x_98; lean_object* x_99; uint8_t x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_98 = lean_ctor_get(x_57, 1);
lean_inc(x_98);
lean_dec(x_57);
x_99 = lean_ctor_get(x_42, 0);
lean_inc(x_99);
x_100 = lean_ctor_get_uint8(x_42, sizeof(void*)*3);
x_101 = lean_ctor_get(x_42, 1);
lean_inc(x_101);
lean_dec(x_42);
x_102 = l_Lean_Server_FileWorker_handleResponseError___redArg(x_99, x_100, x_101, x_2, x_98);
x_103 = lean_ctor_get(x_102, 1);
lean_inc(x_103);
lean_dec(x_102);
x_4 = x_103;
goto _start;
}
}
}
}
else
{
uint8_t x_107; 
lean_dec(x_42);
lean_dec(x_39);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_107 = !lean_is_exclusive(x_45);
if (x_107 == 0)
{
return x_45;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_45, 0);
x_109 = lean_ctor_get(x_45, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_45);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
return x_110;
}
}
}
else
{
uint8_t x_111; 
lean_dec(x_39);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_111 = !lean_is_exclusive(x_41);
if (x_111 == 0)
{
return x_41;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_41, 0);
x_113 = lean_ctor_get(x_41, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_41);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
return x_114;
}
}
block_8:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_mk_string_unchecked("Got invalid JSON-RPC message", 28, 28);
x_7 = l_IO_throwServerError(lean_box(0), x_6, x_5);
return x_7;
}
block_16:
{
lean_object* x_13; lean_object* x_14; 
lean_inc(x_2);
x_13 = l_Lean_Server_FileWorker_handleRequest(x_9, x_10, x_12, x_2, x_3, x_11);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_4 = x_14;
goto _start;
}
block_25:
{
lean_object* x_22; 
lean_inc(x_18);
lean_inc(x_20);
x_22 = l_Lean_Server_FileWorker_handleNotification(x_17, x_21, x_20, x_18, x_19);
lean_dec(x_17);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_2 = x_20;
x_3 = x_18;
x_4 = x_23;
goto _start;
}
else
{
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_1);
return x_22;
}
}
block_37:
{
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_27);
if (x_31 == 0)
{
lean_ctor_set_tag(x_27, 4);
x_17 = x_26;
x_18 = x_29;
x_19 = x_30;
x_20 = x_28;
x_21 = x_27;
goto block_25;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_27, 0);
lean_inc(x_32);
lean_dec(x_27);
x_33 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_17 = x_26;
x_18 = x_29;
x_19 = x_30;
x_20 = x_28;
x_21 = x_33;
goto block_25;
}
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_27);
if (x_34 == 0)
{
lean_ctor_set_tag(x_27, 5);
x_17 = x_26;
x_18 = x_29;
x_19 = x_30;
x_20 = x_28;
x_21 = x_27;
goto block_25;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_27, 0);
lean_inc(x_35);
lean_dec(x_27);
x_36 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_17 = x_26;
x_18 = x_29;
x_19 = x_30;
x_20 = x_28;
x_21 = x_36;
goto block_25;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_Server_FileWorker_mainLoop_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_Server_FileWorker_mainLoop_spec__0_spec__0___redArg(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_Server_FileWorker_mainLoop_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_Server_FileWorker_mainLoop_spec__0_spec__0(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___at___Lean_Server_FileWorker_mainLoop_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = l_Lean_RBNode_erase___at___Lean_Server_FileWorker_mainLoop_spec__0___redArg(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___at___Lean_Server_FileWorker_mainLoop_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = l_Lean_RBNode_erase___at___Lean_Server_FileWorker_mainLoop_spec__0(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___at___Lean_RBNode_foldM___at___Lean_Server_FileWorker_mainLoop_spec__2_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_RBNode_foldM___at___Lean_RBNode_foldM___at___Lean_Server_FileWorker_mainLoop_spec__2_spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___at___Lean_Server_FileWorker_mainLoop_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_RBNode_foldM___at___Lean_Server_FileWorker_mainLoop_spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at___Lean_Server_FileWorker_mainLoop_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_RBNode_forIn_visit___at___Lean_Server_FileWorker_mainLoop_spec__4(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Server_FileWorker_runRefreshTasks_sleepWithCancellation_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint32_t x_5; lean_object* x_47; uint32_t x_48; uint32_t x_49; uint8_t x_50; 
x_3 = lean_box(0);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_47 = lean_unsigned_to_nat(0u);
x_48 = lean_uint32_of_nat(x_47);
x_49 = lean_unbox_uint32(x_4);
x_50 = lean_uint32_dec_lt(x_48, x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_3);
lean_ctor_set(x_51, 1, x_4);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_2);
return x_52;
}
else
{
lean_object* x_53; uint32_t x_54; uint32_t x_55; uint8_t x_56; 
x_53 = lean_unsigned_to_nat(200u);
x_54 = lean_uint32_of_nat(x_53);
x_55 = lean_unbox_uint32(x_4);
x_56 = lean_uint32_dec_lt(x_55, x_54);
if (x_56 == 0)
{
x_5 = x_54;
goto block_46;
}
else
{
uint32_t x_57; 
x_57 = lean_unbox_uint32(x_4);
x_5 = x_57;
goto block_46;
}
}
block_46:
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_IO_sleep(x_5, x_2);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_6, 1);
x_9 = lean_ctor_get(x_6, 0);
lean_dec(x_9);
x_10 = lean_io_check_canceled(x_8);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint32_t x_14; uint32_t x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_14 = lean_unbox_uint32(x_4);
lean_dec(x_4);
x_15 = lean_uint32_sub(x_14, x_5);
x_16 = lean_unbox(x_12);
if (x_16 == 0)
{
lean_object* x_17; 
lean_free_object(x_10);
lean_dec(x_12);
x_17 = lean_box_uint32(x_15);
lean_ctor_set(x_6, 1, x_17);
lean_ctor_set(x_6, 0, x_3);
x_1 = x_6;
x_2 = x_13;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_12);
x_20 = lean_box_uint32(x_15);
lean_ctor_set(x_6, 1, x_20);
lean_ctor_set(x_6, 0, x_19);
lean_ctor_set(x_10, 0, x_6);
return x_10;
}
}
else
{
lean_object* x_21; lean_object* x_22; uint32_t x_23; uint32_t x_24; uint8_t x_25; 
x_21 = lean_ctor_get(x_10, 0);
x_22 = lean_ctor_get(x_10, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_10);
x_23 = lean_unbox_uint32(x_4);
lean_dec(x_4);
x_24 = lean_uint32_sub(x_23, x_5);
x_25 = lean_unbox(x_21);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_21);
x_26 = lean_box_uint32(x_24);
lean_ctor_set(x_6, 1, x_26);
lean_ctor_set(x_6, 0, x_3);
x_1 = x_6;
x_2 = x_22;
goto _start;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_21);
x_29 = lean_box_uint32(x_24);
lean_ctor_set(x_6, 1, x_29);
lean_ctor_set(x_6, 0, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_6);
lean_ctor_set(x_30, 1, x_22);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint32_t x_36; uint32_t x_37; uint8_t x_38; 
x_31 = lean_ctor_get(x_6, 1);
lean_inc(x_31);
lean_dec(x_6);
x_32 = lean_io_check_canceled(x_31);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_35 = x_32;
} else {
 lean_dec_ref(x_32);
 x_35 = lean_box(0);
}
x_36 = lean_unbox_uint32(x_4);
lean_dec(x_4);
x_37 = lean_uint32_sub(x_36, x_5);
x_38 = lean_unbox(x_33);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_35);
lean_dec(x_33);
x_39 = lean_box_uint32(x_37);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_3);
lean_ctor_set(x_40, 1, x_39);
x_1 = x_40;
x_2 = x_34;
goto _start;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_33);
x_43 = lean_box_uint32(x_37);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
if (lean_is_scalar(x_35)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_35;
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_34);
return x_45;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_runRefreshTasks_sleepWithCancellation(uint32_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_io_check_canceled(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_unbox(x_4);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_ctor_get(x_3, 0);
lean_dec(x_8);
x_9 = lean_box(0);
x_10 = lean_box_uint32(x_1);
lean_ctor_set(x_3, 1, x_10);
lean_ctor_set(x_3, 0, x_9);
x_11 = l_Lean_Loop_forIn_loop___at___Lean_Server_FileWorker_runRefreshTasks_sleepWithCancellation_spec__0(x_3, x_7);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_11);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_11, 0);
lean_dec(x_15);
lean_ctor_set(x_11, 0, x_4);
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_4);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
lean_dec(x_4);
x_18 = !lean_is_exclusive(x_11);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_11, 0);
lean_dec(x_19);
x_20 = lean_ctor_get(x_13, 0);
lean_inc(x_20);
lean_dec(x_13);
lean_ctor_set(x_11, 0, x_20);
return x_11;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_11, 1);
lean_inc(x_21);
lean_dec(x_11);
x_22 = lean_ctor_get(x_13, 0);
lean_inc(x_22);
lean_dec(x_13);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_24 = lean_ctor_get(x_3, 1);
lean_inc(x_24);
lean_dec(x_3);
x_25 = lean_box(0);
x_26 = lean_box_uint32(x_1);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_Loop_forIn_loop___at___Lean_Server_FileWorker_runRefreshTasks_sleepWithCancellation_spec__0(x_27, x_24);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec(x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_32 = x_28;
} else {
 lean_dec_ref(x_28);
 x_32 = lean_box(0);
}
if (lean_is_scalar(x_32)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_32;
}
lean_ctor_set(x_33, 0, x_4);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_4);
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
x_36 = lean_ctor_get(x_30, 0);
lean_inc(x_36);
lean_dec(x_30);
if (lean_is_scalar(x_35)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_35;
}
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_34);
return x_37;
}
}
}
else
{
lean_dec(x_4);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_runRefreshTasks_sleepWithCancellation___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = l_Lean_Server_FileWorker_runRefreshTasks_sleepWithCancellation(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_WorkerContext_initPendingServerRequest___at___Lean_Server_FileWorker_sendServerRequest___at___Lean_Server_FileWorker_runRefreshTasks_spec__0_spec__0___redArg___lam__0(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
lean_ctor_set(x_1, 0, x_4);
return x_1;
}
else
{
lean_object* x_5; 
x_5 = l_Lean_Json_getNat_x3f(x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
lean_free_object(x_1);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_box(3);
x_8 = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(x_8, 0, x_6);
x_9 = lean_unbox(x_7);
lean_ctor_set_uint8(x_8, sizeof(void*)*1, x_9);
return x_8;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_5);
if (x_10 == 0)
{
lean_ctor_set(x_1, 0, x_5);
return x_1;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_5, 0);
lean_inc(x_11);
lean_dec(x_5);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_1, 0, x_12);
return x_1;
}
}
}
}
else
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
else
{
lean_object* x_16; 
x_16 = l_Lean_Json_getNat_x3f(x_13);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_box(3);
x_19 = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(x_19, 0, x_17);
x_20 = lean_unbox(x_18);
lean_ctor_set_uint8(x_19, sizeof(void*)*1, x_20);
return x_19;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_16, 0);
lean_inc(x_21);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 x_22 = x_16;
} else {
 lean_dec_ref(x_16);
 x_22 = lean_box(0);
}
if (lean_is_scalar(x_22)) {
 x_23 = lean_alloc_ctor(1, 1, 0);
} else {
 x_23 = x_22;
}
lean_ctor_set(x_23, 0, x_21);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
}
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_1);
if (x_25 == 0)
{
return x_1;
}
else
{
uint8_t x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_27 = lean_ctor_get(x_1, 0);
lean_inc(x_27);
lean_dec(x_1);
x_28 = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set_uint8(x_28, sizeof(void*)*1, x_26);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_WorkerContext_initPendingServerRequest___at___Lean_Server_FileWorker_sendServerRequest___at___Lean_Server_FileWorker_runRefreshTasks_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_4 = lean_io_promise_new(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_1, 5);
x_8 = lean_st_ref_take(x_7, x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_5);
x_11 = l_Std_DTreeMap_Internal_Impl_insert___at___Lean_Server_FileWorker_WorkerContext_initPendingServerRequest___at___Lean_Server_FileWorker_sendServerRequest___at___Lean_Server_FileWorker_sendUntypedServerRequest_spec__0_spec__0_spec__0___redArg(x_2, x_5, x_9);
x_12 = lean_st_ref_set(x_7, x_11, x_10);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
x_15 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_WorkerContext_initPendingServerRequest___at___Lean_Server_FileWorker_sendServerRequest___at___Lean_Server_FileWorker_runRefreshTasks_spec__0_spec__0___redArg___lam__0), 1, 0);
x_16 = l_IO_Promise_result_x21___redArg(x_5);
lean_dec(x_5);
x_17 = l_Lean_Server_ServerTask_mapCheap___redArg(x_15, x_16);
lean_ctor_set(x_12, 0, x_17);
return x_12;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_dec(x_12);
x_19 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_WorkerContext_initPendingServerRequest___at___Lean_Server_FileWorker_sendServerRequest___at___Lean_Server_FileWorker_runRefreshTasks_spec__0_spec__0___redArg___lam__0), 1, 0);
x_20 = l_IO_Promise_result_x21___redArg(x_5);
lean_dec(x_5);
x_21 = l_Lean_Server_ServerTask_mapCheap___redArg(x_19, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_18);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_WorkerContext_initPendingServerRequest___at___Lean_Server_FileWorker_sendServerRequest___at___Lean_Server_FileWorker_runRefreshTasks_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_FileWorker_WorkerContext_initPendingServerRequest___at___Lean_Server_FileWorker_sendServerRequest___at___Lean_Server_FileWorker_runRefreshTasks_spec__0_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___Lean_Server_FileWorker_sendServerRequest___at___Lean_Server_FileWorker_runRefreshTasks_spec__0_spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_11; 
x_11 = lean_box(0);
x_2 = x_11;
goto block_10;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_1);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = l_Lean_JsonNumber_fromNat(x_13);
lean_ctor_set_tag(x_1, 2);
lean_ctor_set(x_1, 0, x_14);
x_2 = x_1;
goto block_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec(x_1);
x_16 = l_Lean_JsonNumber_fromNat(x_15);
x_17 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_2 = x_17;
goto block_10;
}
}
block_10:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_mk_string_unchecked("expected structured object, got '", 33, 33);
x_4 = lean_unsigned_to_nat(80u);
x_5 = l_Lean_Json_pretty(x_2, x_4);
x_6 = lean_string_append(x_3, x_5);
lean_dec(x_5);
x_7 = lean_mk_string_unchecked("'", 1, 1);
x_8 = lean_string_append(x_6, x_7);
lean_dec(x_7);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_sendServerRequest___at___Lean_Server_FileWorker_runRefreshTasks_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
lean_dec(x_4);
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
x_7 = lean_st_ref_take(x_6, x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_to_int(x_10);
x_12 = lean_int_add(x_8, x_11);
lean_dec(x_11);
x_13 = lean_st_ref_set(x_6, x_12, x_9);
lean_dec(x_6);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Lean_JsonNumber_fromInt(x_8);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
lean_inc(x_16);
x_17 = l_Lean_Server_FileWorker_WorkerContext_initPendingServerRequest___at___Lean_Server_FileWorker_sendServerRequest___at___Lean_Server_FileWorker_runRefreshTasks_spec__0_spec__0___redArg(x_2, x_16, x_14);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_2, 0);
lean_inc(x_20);
lean_dec(x_2);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_22, 0, x_16);
lean_ctor_set(x_22, 1, x_3);
lean_ctor_set(x_22, 2, x_21);
x_23 = l_Std_Channel_Sync_send___redArg(x_20, x_22, x_19);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
lean_ctor_set(x_23, 0, x_18);
return x_23;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_18);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Server_FileWorker_runRefreshTasks_spec__3_spec__3___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 2);
lean_inc(x_3);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
x_9 = lean_nat_dec_le(x_1, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
lean_dec(x_7);
lean_ctor_set(x_3, 0, x_10);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_2);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_free_object(x_3);
lean_dec(x_7);
x_12 = lean_box(0);
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_14);
lean_dec(x_2);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_14);
lean_ctor_set(x_16, 2, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_3, 0);
lean_inc(x_18);
lean_dec(x_3);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
x_20 = lean_nat_dec_le(x_1, x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_2);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_18);
x_24 = lean_box(0);
x_25 = lean_ctor_get(x_2, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_2, 1);
lean_inc(x_26);
lean_dec(x_2);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_26);
lean_ctor_set(x_28, 2, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_24);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Server_FileWorker_runRefreshTasks_spec__3_spec__3___redArg___lam__1(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_3, 2);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_1);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
x_11 = lean_nat_dec_lt(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_dec(x_8);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_13, x_14);
lean_dec(x_13);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set(x_4, 0, x_16);
x_17 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_10);
lean_ctor_set(x_17, 2, x_4);
x_18 = lean_box(x_2);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_10);
lean_free_object(x_4);
lean_dec(x_8);
lean_dec(x_1);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_3);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_4, 0);
lean_inc(x_22);
lean_dec(x_4);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_ctor_get(x_3, 1);
lean_inc(x_24);
x_25 = lean_nat_dec_lt(x_23, x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_26 = lean_ctor_get(x_3, 0);
lean_inc(x_26);
lean_dec(x_3);
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_dec(x_22);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_27, x_28);
lean_dec(x_27);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_32, 0, x_26);
lean_ctor_set(x_32, 1, x_24);
lean_ctor_set(x_32, 2, x_31);
x_33 = lean_box(x_2);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_1);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_3);
return x_36;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Server_FileWorker_runRefreshTasks_spec__3_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_unsigned_to_nat(10u);
x_7 = lean_alloc_closure((void*)(l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Server_FileWorker_runRefreshTasks_spec__3_spec__3___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_7, 0, x_6);
lean_inc(x_2);
x_8 = l_Lean_Server_FileWorker_WorkerContext_modifyGetPartialHandler___redArg(x_1, x_2, x_7, x_5);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = lean_box(0);
if (lean_obj_tag(x_10) == 0)
{
uint32_t x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_uint32_of_nat(x_3);
x_14 = l_Lean_Server_FileWorker_runRefreshTasks_sleepWithCancellation(x_13, x_11);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_free_object(x_8);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_5 = x_17;
goto _start;
}
else
{
uint8_t x_19; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_14);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_14, 0);
lean_dec(x_20);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_12);
lean_ctor_set(x_8, 1, x_12);
lean_ctor_set(x_8, 0, x_21);
lean_ctor_set(x_14, 0, x_8);
return x_14;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
lean_dec(x_14);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_12);
lean_ctor_set(x_8, 1, x_12);
lean_ctor_set(x_8, 0, x_23);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_8);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
lean_free_object(x_8);
x_25 = lean_ctor_get(x_10, 0);
lean_inc(x_25);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 x_26 = x_10;
} else {
 lean_dec_ref(x_10);
 x_26 = lean_box(0);
}
x_27 = lean_io_mono_ms_now(x_11);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_27, 1);
x_31 = lean_box(1);
x_74 = lean_nat_sub(x_29, x_25);
lean_dec(x_25);
lean_dec(x_29);
x_75 = lean_nat_sub(x_3, x_74);
lean_dec(x_74);
x_76 = lean_unsigned_to_nat(0u);
x_77 = lean_nat_dec_lt(x_76, x_75);
if (x_77 == 0)
{
lean_dec(x_75);
lean_free_object(x_27);
x_32 = x_30;
goto block_73;
}
else
{
uint32_t x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_78 = lean_uint32_of_nat(x_75);
lean_dec(x_75);
x_79 = l_Lean_Server_FileWorker_runRefreshTasks_sleepWithCancellation(x_78, x_30);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_unbox(x_80);
lean_dec(x_80);
if (x_81 == 0)
{
lean_object* x_82; 
lean_free_object(x_27);
x_82 = lean_ctor_get(x_79, 1);
lean_inc(x_82);
lean_dec(x_79);
x_32 = x_82;
goto block_73;
}
else
{
uint8_t x_83; 
lean_dec(x_26);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_83 = !lean_is_exclusive(x_79);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_79, 0);
lean_dec(x_84);
x_85 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_85, 0, x_12);
lean_ctor_set(x_27, 1, x_12);
lean_ctor_set(x_27, 0, x_85);
lean_ctor_set(x_79, 0, x_27);
return x_79;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_79, 1);
lean_inc(x_86);
lean_dec(x_79);
x_87 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_87, 0, x_12);
lean_ctor_set(x_27, 1, x_12);
lean_ctor_set(x_27, 0, x_87);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_27);
lean_ctor_set(x_88, 1, x_86);
return x_88;
}
}
}
block_73:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_33 = lean_io_mono_ms_now(x_32);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_alloc_closure((void*)(l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Server_FileWorker_runRefreshTasks_spec__3_spec__3___redArg___lam__1___boxed), 3, 2);
lean_closure_set(x_36, 0, x_34);
lean_closure_set(x_36, 1, x_31);
lean_inc(x_2);
x_37 = l_Lean_Server_FileWorker_WorkerContext_modifyGetPartialHandler___redArg(x_1, x_2, x_36, x_35);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_unbox(x_38);
lean_dec(x_38);
if (x_39 == 0)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_37);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; uint32_t x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_41 = lean_ctor_get(x_37, 1);
x_42 = lean_ctor_get(x_37, 0);
lean_dec(x_42);
x_43 = lean_uint32_of_nat(x_3);
x_44 = l_Lean_Server_FileWorker_runRefreshTasks_sleepWithCancellation(x_43, x_41);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_unbox(x_45);
lean_dec(x_45);
if (x_46 == 0)
{
lean_object* x_47; 
lean_free_object(x_37);
lean_dec(x_26);
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
lean_dec(x_44);
x_5 = x_47;
goto _start;
}
else
{
uint8_t x_49; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_44);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_44, 0);
lean_dec(x_50);
if (lean_is_scalar(x_26)) {
 x_51 = lean_alloc_ctor(1, 1, 0);
} else {
 x_51 = x_26;
}
lean_ctor_set(x_51, 0, x_12);
lean_ctor_set(x_37, 1, x_12);
lean_ctor_set(x_37, 0, x_51);
lean_ctor_set(x_44, 0, x_37);
return x_44;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_44, 1);
lean_inc(x_52);
lean_dec(x_44);
if (lean_is_scalar(x_26)) {
 x_53 = lean_alloc_ctor(1, 1, 0);
} else {
 x_53 = x_26;
}
lean_ctor_set(x_53, 0, x_12);
lean_ctor_set(x_37, 1, x_12);
lean_ctor_set(x_37, 0, x_53);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_37);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
}
else
{
lean_object* x_55; uint32_t x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_55 = lean_ctor_get(x_37, 1);
lean_inc(x_55);
lean_dec(x_37);
x_56 = lean_uint32_of_nat(x_3);
x_57 = l_Lean_Server_FileWorker_runRefreshTasks_sleepWithCancellation(x_56, x_55);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_unbox(x_58);
lean_dec(x_58);
if (x_59 == 0)
{
lean_object* x_60; 
lean_dec(x_26);
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
lean_dec(x_57);
x_5 = x_60;
goto _start;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_62 = lean_ctor_get(x_57, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_63 = x_57;
} else {
 lean_dec_ref(x_57);
 x_63 = lean_box(0);
}
if (lean_is_scalar(x_26)) {
 x_64 = lean_alloc_ctor(1, 1, 0);
} else {
 x_64 = x_26;
}
lean_ctor_set(x_64, 0, x_12);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_12);
if (lean_is_scalar(x_63)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_63;
}
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_62);
return x_66;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_26);
x_67 = lean_ctor_get(x_37, 1);
lean_inc(x_67);
lean_dec(x_37);
x_68 = lean_box(0);
x_69 = lean_box(0);
lean_inc(x_4);
lean_inc(x_1);
x_70 = l_Lean_Server_FileWorker_sendServerRequest___at___Lean_Server_FileWorker_runRefreshTasks_spec__0(x_68, x_1, x_4, x_69, x_67);
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
lean_dec(x_70);
x_5 = x_71;
goto _start;
}
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; 
x_89 = lean_ctor_get(x_27, 0);
x_90 = lean_ctor_get(x_27, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_27);
x_91 = lean_box(1);
x_120 = lean_nat_sub(x_89, x_25);
lean_dec(x_25);
lean_dec(x_89);
x_121 = lean_nat_sub(x_3, x_120);
lean_dec(x_120);
x_122 = lean_unsigned_to_nat(0u);
x_123 = lean_nat_dec_lt(x_122, x_121);
if (x_123 == 0)
{
lean_dec(x_121);
x_92 = x_90;
goto block_119;
}
else
{
uint32_t x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_124 = lean_uint32_of_nat(x_121);
lean_dec(x_121);
x_125 = l_Lean_Server_FileWorker_runRefreshTasks_sleepWithCancellation(x_124, x_90);
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_unbox(x_126);
lean_dec(x_126);
if (x_127 == 0)
{
lean_object* x_128; 
x_128 = lean_ctor_get(x_125, 1);
lean_inc(x_128);
lean_dec(x_125);
x_92 = x_128;
goto block_119;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
lean_dec(x_26);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_129 = lean_ctor_get(x_125, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 x_130 = x_125;
} else {
 lean_dec_ref(x_125);
 x_130 = lean_box(0);
}
x_131 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_131, 0, x_12);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_12);
if (lean_is_scalar(x_130)) {
 x_133 = lean_alloc_ctor(0, 2, 0);
} else {
 x_133 = x_130;
}
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_129);
return x_133;
}
}
block_119:
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; 
x_93 = lean_io_mono_ms_now(x_92);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
x_96 = lean_alloc_closure((void*)(l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Server_FileWorker_runRefreshTasks_spec__3_spec__3___redArg___lam__1___boxed), 3, 2);
lean_closure_set(x_96, 0, x_94);
lean_closure_set(x_96, 1, x_91);
lean_inc(x_2);
x_97 = l_Lean_Server_FileWorker_WorkerContext_modifyGetPartialHandler___redArg(x_1, x_2, x_96, x_95);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_unbox(x_98);
lean_dec(x_98);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; uint32_t x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; 
x_100 = lean_ctor_get(x_97, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_101 = x_97;
} else {
 lean_dec_ref(x_97);
 x_101 = lean_box(0);
}
x_102 = lean_uint32_of_nat(x_3);
x_103 = l_Lean_Server_FileWorker_runRefreshTasks_sleepWithCancellation(x_102, x_100);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_unbox(x_104);
lean_dec(x_104);
if (x_105 == 0)
{
lean_object* x_106; 
lean_dec(x_101);
lean_dec(x_26);
x_106 = lean_ctor_get(x_103, 1);
lean_inc(x_106);
lean_dec(x_103);
x_5 = x_106;
goto _start;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_108 = lean_ctor_get(x_103, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_109 = x_103;
} else {
 lean_dec_ref(x_103);
 x_109 = lean_box(0);
}
if (lean_is_scalar(x_26)) {
 x_110 = lean_alloc_ctor(1, 1, 0);
} else {
 x_110 = x_26;
}
lean_ctor_set(x_110, 0, x_12);
if (lean_is_scalar(x_101)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_101;
}
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_12);
if (lean_is_scalar(x_109)) {
 x_112 = lean_alloc_ctor(0, 2, 0);
} else {
 x_112 = x_109;
}
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_108);
return x_112;
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_26);
x_113 = lean_ctor_get(x_97, 1);
lean_inc(x_113);
lean_dec(x_97);
x_114 = lean_box(0);
x_115 = lean_box(0);
lean_inc(x_4);
lean_inc(x_1);
x_116 = l_Lean_Server_FileWorker_sendServerRequest___at___Lean_Server_FileWorker_runRefreshTasks_spec__0(x_114, x_1, x_4, x_115, x_113);
x_117 = lean_ctor_get(x_116, 1);
lean_inc(x_117);
lean_dec(x_116);
x_5 = x_117;
goto _start;
}
}
}
}
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_ctor_get(x_8, 0);
x_135 = lean_ctor_get(x_8, 1);
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_8);
x_136 = lean_box(0);
if (lean_obj_tag(x_134) == 0)
{
uint32_t x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; 
x_137 = lean_uint32_of_nat(x_3);
x_138 = l_Lean_Server_FileWorker_runRefreshTasks_sleepWithCancellation(x_137, x_135);
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
x_140 = lean_unbox(x_139);
lean_dec(x_139);
if (x_140 == 0)
{
lean_object* x_141; 
x_141 = lean_ctor_get(x_138, 1);
lean_inc(x_141);
lean_dec(x_138);
x_5 = x_141;
goto _start;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_143 = lean_ctor_get(x_138, 1);
lean_inc(x_143);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_144 = x_138;
} else {
 lean_dec_ref(x_138);
 x_144 = lean_box(0);
}
x_145 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_145, 0, x_136);
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_136);
if (lean_is_scalar(x_144)) {
 x_147 = lean_alloc_ctor(0, 2, 0);
} else {
 x_147 = x_144;
}
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_143);
return x_147;
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_183; lean_object* x_184; lean_object* x_185; uint8_t x_186; 
x_148 = lean_ctor_get(x_134, 0);
lean_inc(x_148);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 x_149 = x_134;
} else {
 lean_dec_ref(x_134);
 x_149 = lean_box(0);
}
x_150 = lean_io_mono_ms_now(x_135);
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_150, 1);
lean_inc(x_152);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_153 = x_150;
} else {
 lean_dec_ref(x_150);
 x_153 = lean_box(0);
}
x_154 = lean_box(1);
x_183 = lean_nat_sub(x_151, x_148);
lean_dec(x_148);
lean_dec(x_151);
x_184 = lean_nat_sub(x_3, x_183);
lean_dec(x_183);
x_185 = lean_unsigned_to_nat(0u);
x_186 = lean_nat_dec_lt(x_185, x_184);
if (x_186 == 0)
{
lean_dec(x_184);
lean_dec(x_153);
x_155 = x_152;
goto block_182;
}
else
{
uint32_t x_187; lean_object* x_188; lean_object* x_189; uint8_t x_190; 
x_187 = lean_uint32_of_nat(x_184);
lean_dec(x_184);
x_188 = l_Lean_Server_FileWorker_runRefreshTasks_sleepWithCancellation(x_187, x_152);
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
x_190 = lean_unbox(x_189);
lean_dec(x_189);
if (x_190 == 0)
{
lean_object* x_191; 
lean_dec(x_153);
x_191 = lean_ctor_get(x_188, 1);
lean_inc(x_191);
lean_dec(x_188);
x_155 = x_191;
goto block_182;
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
lean_dec(x_149);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_192 = lean_ctor_get(x_188, 1);
lean_inc(x_192);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 x_193 = x_188;
} else {
 lean_dec_ref(x_188);
 x_193 = lean_box(0);
}
x_194 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_194, 0, x_136);
if (lean_is_scalar(x_153)) {
 x_195 = lean_alloc_ctor(0, 2, 0);
} else {
 x_195 = x_153;
}
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set(x_195, 1, x_136);
if (lean_is_scalar(x_193)) {
 x_196 = lean_alloc_ctor(0, 2, 0);
} else {
 x_196 = x_193;
}
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_192);
return x_196;
}
}
block_182:
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; 
x_156 = lean_io_mono_ms_now(x_155);
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
lean_dec(x_156);
x_159 = lean_alloc_closure((void*)(l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Server_FileWorker_runRefreshTasks_spec__3_spec__3___redArg___lam__1___boxed), 3, 2);
lean_closure_set(x_159, 0, x_157);
lean_closure_set(x_159, 1, x_154);
lean_inc(x_2);
x_160 = l_Lean_Server_FileWorker_WorkerContext_modifyGetPartialHandler___redArg(x_1, x_2, x_159, x_158);
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
x_162 = lean_unbox(x_161);
lean_dec(x_161);
if (x_162 == 0)
{
lean_object* x_163; lean_object* x_164; uint32_t x_165; lean_object* x_166; lean_object* x_167; uint8_t x_168; 
x_163 = lean_ctor_get(x_160, 1);
lean_inc(x_163);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 x_164 = x_160;
} else {
 lean_dec_ref(x_160);
 x_164 = lean_box(0);
}
x_165 = lean_uint32_of_nat(x_3);
x_166 = l_Lean_Server_FileWorker_runRefreshTasks_sleepWithCancellation(x_165, x_163);
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
x_168 = lean_unbox(x_167);
lean_dec(x_167);
if (x_168 == 0)
{
lean_object* x_169; 
lean_dec(x_164);
lean_dec(x_149);
x_169 = lean_ctor_get(x_166, 1);
lean_inc(x_169);
lean_dec(x_166);
x_5 = x_169;
goto _start;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_171 = lean_ctor_get(x_166, 1);
lean_inc(x_171);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 lean_ctor_release(x_166, 1);
 x_172 = x_166;
} else {
 lean_dec_ref(x_166);
 x_172 = lean_box(0);
}
if (lean_is_scalar(x_149)) {
 x_173 = lean_alloc_ctor(1, 1, 0);
} else {
 x_173 = x_149;
}
lean_ctor_set(x_173, 0, x_136);
if (lean_is_scalar(x_164)) {
 x_174 = lean_alloc_ctor(0, 2, 0);
} else {
 x_174 = x_164;
}
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_136);
if (lean_is_scalar(x_172)) {
 x_175 = lean_alloc_ctor(0, 2, 0);
} else {
 x_175 = x_172;
}
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_171);
return x_175;
}
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_149);
x_176 = lean_ctor_get(x_160, 1);
lean_inc(x_176);
lean_dec(x_160);
x_177 = lean_box(0);
x_178 = lean_box(0);
lean_inc(x_4);
lean_inc(x_1);
x_179 = l_Lean_Server_FileWorker_sendServerRequest___at___Lean_Server_FileWorker_runRefreshTasks_spec__0(x_177, x_1, x_4, x_178, x_176);
x_180 = lean_ctor_get(x_179, 1);
lean_inc(x_180);
lean_dec(x_179);
x_5 = x_180;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Server_FileWorker_runRefreshTasks_spec__3_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Server_FileWorker_runRefreshTasks_spec__3_spec__3___redArg(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Server_FileWorker_runRefreshTasks_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_unsigned_to_nat(10u);
x_7 = lean_alloc_closure((void*)(l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Server_FileWorker_runRefreshTasks_spec__3_spec__3___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_7, 0, x_6);
lean_inc(x_2);
x_8 = l_Lean_Server_FileWorker_WorkerContext_modifyGetPartialHandler___redArg(x_1, x_2, x_7, x_5);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = lean_box(0);
if (lean_obj_tag(x_10) == 0)
{
uint32_t x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_uint32_of_nat(x_3);
x_14 = l_Lean_Server_FileWorker_runRefreshTasks_sleepWithCancellation(x_13, x_11);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_free_object(x_8);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Server_FileWorker_runRefreshTasks_spec__3_spec__3___redArg(x_1, x_2, x_3, x_4, x_17);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_14);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_14, 0);
lean_dec(x_20);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_12);
lean_ctor_set(x_8, 1, x_12);
lean_ctor_set(x_8, 0, x_21);
lean_ctor_set(x_14, 0, x_8);
return x_14;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
lean_dec(x_14);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_12);
lean_ctor_set(x_8, 1, x_12);
lean_ctor_set(x_8, 0, x_23);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_8);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
lean_free_object(x_8);
x_25 = lean_ctor_get(x_10, 0);
lean_inc(x_25);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 x_26 = x_10;
} else {
 lean_dec_ref(x_10);
 x_26 = lean_box(0);
}
x_27 = lean_io_mono_ms_now(x_11);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_27, 1);
x_31 = lean_box(1);
x_74 = lean_nat_sub(x_29, x_25);
lean_dec(x_25);
lean_dec(x_29);
x_75 = lean_nat_sub(x_3, x_74);
lean_dec(x_74);
x_76 = lean_unsigned_to_nat(0u);
x_77 = lean_nat_dec_lt(x_76, x_75);
if (x_77 == 0)
{
lean_dec(x_75);
lean_free_object(x_27);
x_32 = x_30;
goto block_73;
}
else
{
uint32_t x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_78 = lean_uint32_of_nat(x_75);
lean_dec(x_75);
x_79 = l_Lean_Server_FileWorker_runRefreshTasks_sleepWithCancellation(x_78, x_30);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_unbox(x_80);
lean_dec(x_80);
if (x_81 == 0)
{
lean_object* x_82; 
lean_free_object(x_27);
x_82 = lean_ctor_get(x_79, 1);
lean_inc(x_82);
lean_dec(x_79);
x_32 = x_82;
goto block_73;
}
else
{
uint8_t x_83; 
lean_dec(x_26);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_83 = !lean_is_exclusive(x_79);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_79, 0);
lean_dec(x_84);
x_85 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_85, 0, x_12);
lean_ctor_set(x_27, 1, x_12);
lean_ctor_set(x_27, 0, x_85);
lean_ctor_set(x_79, 0, x_27);
return x_79;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_79, 1);
lean_inc(x_86);
lean_dec(x_79);
x_87 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_87, 0, x_12);
lean_ctor_set(x_27, 1, x_12);
lean_ctor_set(x_27, 0, x_87);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_27);
lean_ctor_set(x_88, 1, x_86);
return x_88;
}
}
}
block_73:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_33 = lean_io_mono_ms_now(x_32);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_alloc_closure((void*)(l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Server_FileWorker_runRefreshTasks_spec__3_spec__3___redArg___lam__1___boxed), 3, 2);
lean_closure_set(x_36, 0, x_34);
lean_closure_set(x_36, 1, x_31);
lean_inc(x_2);
x_37 = l_Lean_Server_FileWorker_WorkerContext_modifyGetPartialHandler___redArg(x_1, x_2, x_36, x_35);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_unbox(x_38);
lean_dec(x_38);
if (x_39 == 0)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_37);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; uint32_t x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_41 = lean_ctor_get(x_37, 1);
x_42 = lean_ctor_get(x_37, 0);
lean_dec(x_42);
x_43 = lean_uint32_of_nat(x_3);
x_44 = l_Lean_Server_FileWorker_runRefreshTasks_sleepWithCancellation(x_43, x_41);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_unbox(x_45);
lean_dec(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
lean_free_object(x_37);
lean_dec(x_26);
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
lean_dec(x_44);
x_48 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Server_FileWorker_runRefreshTasks_spec__3_spec__3___redArg(x_1, x_2, x_3, x_4, x_47);
return x_48;
}
else
{
uint8_t x_49; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_44);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_44, 0);
lean_dec(x_50);
if (lean_is_scalar(x_26)) {
 x_51 = lean_alloc_ctor(1, 1, 0);
} else {
 x_51 = x_26;
}
lean_ctor_set(x_51, 0, x_12);
lean_ctor_set(x_37, 1, x_12);
lean_ctor_set(x_37, 0, x_51);
lean_ctor_set(x_44, 0, x_37);
return x_44;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_44, 1);
lean_inc(x_52);
lean_dec(x_44);
if (lean_is_scalar(x_26)) {
 x_53 = lean_alloc_ctor(1, 1, 0);
} else {
 x_53 = x_26;
}
lean_ctor_set(x_53, 0, x_12);
lean_ctor_set(x_37, 1, x_12);
lean_ctor_set(x_37, 0, x_53);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_37);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
}
else
{
lean_object* x_55; uint32_t x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_55 = lean_ctor_get(x_37, 1);
lean_inc(x_55);
lean_dec(x_37);
x_56 = lean_uint32_of_nat(x_3);
x_57 = l_Lean_Server_FileWorker_runRefreshTasks_sleepWithCancellation(x_56, x_55);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_unbox(x_58);
lean_dec(x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; 
lean_dec(x_26);
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
lean_dec(x_57);
x_61 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Server_FileWorker_runRefreshTasks_spec__3_spec__3___redArg(x_1, x_2, x_3, x_4, x_60);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_62 = lean_ctor_get(x_57, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_63 = x_57;
} else {
 lean_dec_ref(x_57);
 x_63 = lean_box(0);
}
if (lean_is_scalar(x_26)) {
 x_64 = lean_alloc_ctor(1, 1, 0);
} else {
 x_64 = x_26;
}
lean_ctor_set(x_64, 0, x_12);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_12);
if (lean_is_scalar(x_63)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_63;
}
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_62);
return x_66;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_26);
x_67 = lean_ctor_get(x_37, 1);
lean_inc(x_67);
lean_dec(x_37);
x_68 = lean_box(0);
x_69 = lean_box(0);
lean_inc(x_4);
lean_inc(x_1);
x_70 = l_Lean_Server_FileWorker_sendServerRequest___at___Lean_Server_FileWorker_runRefreshTasks_spec__0(x_68, x_1, x_4, x_69, x_67);
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
lean_dec(x_70);
x_72 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Server_FileWorker_runRefreshTasks_spec__3_spec__3___redArg(x_1, x_2, x_3, x_4, x_71);
return x_72;
}
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; 
x_89 = lean_ctor_get(x_27, 0);
x_90 = lean_ctor_get(x_27, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_27);
x_91 = lean_box(1);
x_120 = lean_nat_sub(x_89, x_25);
lean_dec(x_25);
lean_dec(x_89);
x_121 = lean_nat_sub(x_3, x_120);
lean_dec(x_120);
x_122 = lean_unsigned_to_nat(0u);
x_123 = lean_nat_dec_lt(x_122, x_121);
if (x_123 == 0)
{
lean_dec(x_121);
x_92 = x_90;
goto block_119;
}
else
{
uint32_t x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_124 = lean_uint32_of_nat(x_121);
lean_dec(x_121);
x_125 = l_Lean_Server_FileWorker_runRefreshTasks_sleepWithCancellation(x_124, x_90);
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_unbox(x_126);
lean_dec(x_126);
if (x_127 == 0)
{
lean_object* x_128; 
x_128 = lean_ctor_get(x_125, 1);
lean_inc(x_128);
lean_dec(x_125);
x_92 = x_128;
goto block_119;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
lean_dec(x_26);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_129 = lean_ctor_get(x_125, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 x_130 = x_125;
} else {
 lean_dec_ref(x_125);
 x_130 = lean_box(0);
}
x_131 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_131, 0, x_12);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_12);
if (lean_is_scalar(x_130)) {
 x_133 = lean_alloc_ctor(0, 2, 0);
} else {
 x_133 = x_130;
}
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_129);
return x_133;
}
}
block_119:
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; 
x_93 = lean_io_mono_ms_now(x_92);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
x_96 = lean_alloc_closure((void*)(l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Server_FileWorker_runRefreshTasks_spec__3_spec__3___redArg___lam__1___boxed), 3, 2);
lean_closure_set(x_96, 0, x_94);
lean_closure_set(x_96, 1, x_91);
lean_inc(x_2);
x_97 = l_Lean_Server_FileWorker_WorkerContext_modifyGetPartialHandler___redArg(x_1, x_2, x_96, x_95);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_unbox(x_98);
lean_dec(x_98);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; uint32_t x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; 
x_100 = lean_ctor_get(x_97, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_101 = x_97;
} else {
 lean_dec_ref(x_97);
 x_101 = lean_box(0);
}
x_102 = lean_uint32_of_nat(x_3);
x_103 = l_Lean_Server_FileWorker_runRefreshTasks_sleepWithCancellation(x_102, x_100);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_unbox(x_104);
lean_dec(x_104);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; 
lean_dec(x_101);
lean_dec(x_26);
x_106 = lean_ctor_get(x_103, 1);
lean_inc(x_106);
lean_dec(x_103);
x_107 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Server_FileWorker_runRefreshTasks_spec__3_spec__3___redArg(x_1, x_2, x_3, x_4, x_106);
return x_107;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_108 = lean_ctor_get(x_103, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_109 = x_103;
} else {
 lean_dec_ref(x_103);
 x_109 = lean_box(0);
}
if (lean_is_scalar(x_26)) {
 x_110 = lean_alloc_ctor(1, 1, 0);
} else {
 x_110 = x_26;
}
lean_ctor_set(x_110, 0, x_12);
if (lean_is_scalar(x_101)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_101;
}
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_12);
if (lean_is_scalar(x_109)) {
 x_112 = lean_alloc_ctor(0, 2, 0);
} else {
 x_112 = x_109;
}
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_108);
return x_112;
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_dec(x_26);
x_113 = lean_ctor_get(x_97, 1);
lean_inc(x_113);
lean_dec(x_97);
x_114 = lean_box(0);
x_115 = lean_box(0);
lean_inc(x_4);
lean_inc(x_1);
x_116 = l_Lean_Server_FileWorker_sendServerRequest___at___Lean_Server_FileWorker_runRefreshTasks_spec__0(x_114, x_1, x_4, x_115, x_113);
x_117 = lean_ctor_get(x_116, 1);
lean_inc(x_117);
lean_dec(x_116);
x_118 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Server_FileWorker_runRefreshTasks_spec__3_spec__3___redArg(x_1, x_2, x_3, x_4, x_117);
return x_118;
}
}
}
}
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_ctor_get(x_8, 0);
x_135 = lean_ctor_get(x_8, 1);
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_8);
x_136 = lean_box(0);
if (lean_obj_tag(x_134) == 0)
{
uint32_t x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; 
x_137 = lean_uint32_of_nat(x_3);
x_138 = l_Lean_Server_FileWorker_runRefreshTasks_sleepWithCancellation(x_137, x_135);
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
x_140 = lean_unbox(x_139);
lean_dec(x_139);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; 
x_141 = lean_ctor_get(x_138, 1);
lean_inc(x_141);
lean_dec(x_138);
x_142 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Server_FileWorker_runRefreshTasks_spec__3_spec__3___redArg(x_1, x_2, x_3, x_4, x_141);
return x_142;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_143 = lean_ctor_get(x_138, 1);
lean_inc(x_143);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_144 = x_138;
} else {
 lean_dec_ref(x_138);
 x_144 = lean_box(0);
}
x_145 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_145, 0, x_136);
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_136);
if (lean_is_scalar(x_144)) {
 x_147 = lean_alloc_ctor(0, 2, 0);
} else {
 x_147 = x_144;
}
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_143);
return x_147;
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_183; lean_object* x_184; lean_object* x_185; uint8_t x_186; 
x_148 = lean_ctor_get(x_134, 0);
lean_inc(x_148);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 x_149 = x_134;
} else {
 lean_dec_ref(x_134);
 x_149 = lean_box(0);
}
x_150 = lean_io_mono_ms_now(x_135);
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_150, 1);
lean_inc(x_152);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_153 = x_150;
} else {
 lean_dec_ref(x_150);
 x_153 = lean_box(0);
}
x_154 = lean_box(1);
x_183 = lean_nat_sub(x_151, x_148);
lean_dec(x_148);
lean_dec(x_151);
x_184 = lean_nat_sub(x_3, x_183);
lean_dec(x_183);
x_185 = lean_unsigned_to_nat(0u);
x_186 = lean_nat_dec_lt(x_185, x_184);
if (x_186 == 0)
{
lean_dec(x_184);
lean_dec(x_153);
x_155 = x_152;
goto block_182;
}
else
{
uint32_t x_187; lean_object* x_188; lean_object* x_189; uint8_t x_190; 
x_187 = lean_uint32_of_nat(x_184);
lean_dec(x_184);
x_188 = l_Lean_Server_FileWorker_runRefreshTasks_sleepWithCancellation(x_187, x_152);
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
x_190 = lean_unbox(x_189);
lean_dec(x_189);
if (x_190 == 0)
{
lean_object* x_191; 
lean_dec(x_153);
x_191 = lean_ctor_get(x_188, 1);
lean_inc(x_191);
lean_dec(x_188);
x_155 = x_191;
goto block_182;
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
lean_dec(x_149);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_192 = lean_ctor_get(x_188, 1);
lean_inc(x_192);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 x_193 = x_188;
} else {
 lean_dec_ref(x_188);
 x_193 = lean_box(0);
}
x_194 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_194, 0, x_136);
if (lean_is_scalar(x_153)) {
 x_195 = lean_alloc_ctor(0, 2, 0);
} else {
 x_195 = x_153;
}
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set(x_195, 1, x_136);
if (lean_is_scalar(x_193)) {
 x_196 = lean_alloc_ctor(0, 2, 0);
} else {
 x_196 = x_193;
}
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_192);
return x_196;
}
}
block_182:
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; 
x_156 = lean_io_mono_ms_now(x_155);
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
lean_dec(x_156);
x_159 = lean_alloc_closure((void*)(l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Server_FileWorker_runRefreshTasks_spec__3_spec__3___redArg___lam__1___boxed), 3, 2);
lean_closure_set(x_159, 0, x_157);
lean_closure_set(x_159, 1, x_154);
lean_inc(x_2);
x_160 = l_Lean_Server_FileWorker_WorkerContext_modifyGetPartialHandler___redArg(x_1, x_2, x_159, x_158);
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
x_162 = lean_unbox(x_161);
lean_dec(x_161);
if (x_162 == 0)
{
lean_object* x_163; lean_object* x_164; uint32_t x_165; lean_object* x_166; lean_object* x_167; uint8_t x_168; 
x_163 = lean_ctor_get(x_160, 1);
lean_inc(x_163);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 x_164 = x_160;
} else {
 lean_dec_ref(x_160);
 x_164 = lean_box(0);
}
x_165 = lean_uint32_of_nat(x_3);
x_166 = l_Lean_Server_FileWorker_runRefreshTasks_sleepWithCancellation(x_165, x_163);
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
x_168 = lean_unbox(x_167);
lean_dec(x_167);
if (x_168 == 0)
{
lean_object* x_169; lean_object* x_170; 
lean_dec(x_164);
lean_dec(x_149);
x_169 = lean_ctor_get(x_166, 1);
lean_inc(x_169);
lean_dec(x_166);
x_170 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Server_FileWorker_runRefreshTasks_spec__3_spec__3___redArg(x_1, x_2, x_3, x_4, x_169);
return x_170;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_171 = lean_ctor_get(x_166, 1);
lean_inc(x_171);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 lean_ctor_release(x_166, 1);
 x_172 = x_166;
} else {
 lean_dec_ref(x_166);
 x_172 = lean_box(0);
}
if (lean_is_scalar(x_149)) {
 x_173 = lean_alloc_ctor(1, 1, 0);
} else {
 x_173 = x_149;
}
lean_ctor_set(x_173, 0, x_136);
if (lean_is_scalar(x_164)) {
 x_174 = lean_alloc_ctor(0, 2, 0);
} else {
 x_174 = x_164;
}
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_136);
if (lean_is_scalar(x_172)) {
 x_175 = lean_alloc_ctor(0, 2, 0);
} else {
 x_175 = x_172;
}
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_171);
return x_175;
}
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
lean_dec(x_149);
x_176 = lean_ctor_get(x_160, 1);
lean_inc(x_176);
lean_dec(x_160);
x_177 = lean_box(0);
x_178 = lean_box(0);
lean_inc(x_4);
lean_inc(x_1);
x_179 = l_Lean_Server_FileWorker_sendServerRequest___at___Lean_Server_FileWorker_runRefreshTasks_spec__0(x_177, x_1, x_4, x_178, x_176);
x_180 = lean_ctor_get(x_179, 1);
lean_inc(x_180);
lean_dec(x_179);
x_181 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Server_FileWorker_runRefreshTasks_spec__3_spec__3___redArg(x_1, x_2, x_3, x_4, x_180);
return x_181;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Server_FileWorker_runRefreshTasks_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Loop_forIn_loop___at___Lean_Server_FileWorker_runRefreshTasks_spec__3___redArg(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_runRefreshTasks_spec__5_spec__5___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = l_Lean_Loop_forIn_loop___at___Lean_Server_FileWorker_runRefreshTasks_spec__3___redArg(x_1, x_2, x_3, x_4, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_7, 0);
lean_dec(x_11);
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
lean_dec(x_9);
lean_ctor_set(x_7, 0, x_12);
return x_7;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
lean_dec(x_7);
x_14 = lean_ctor_get(x_9, 0);
lean_inc(x_14);
lean_dec(x_9);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_runRefreshTasks_spec__5_spec__5___redArg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; 
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
x_14 = lean_box(0);
lean_inc(x_1);
x_15 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_runRefreshTasks_spec__5_spec__5___redArg___lam__0___boxed), 6, 5);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_11);
lean_closure_set(x_15, 2, x_13);
lean_closure_set(x_15, 3, x_12);
lean_closure_set(x_15, 4, x_14);
x_16 = l_Lean_Server_ServerTask_BaseIO_asTask___redArg(x_15, x_6);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_array_push(x_5, x_17);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_usize_of_nat(x_20);
x_22 = lean_usize_add(x_4, x_21);
x_4 = x_22;
x_5 = x_19;
x_6 = x_18;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_runRefreshTasks_spec__5_spec__5(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_runRefreshTasks_spec__5_spec__5___redArg(x_1, x_2, x_3, x_4, x_5, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_runRefreshTasks_spec__5(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_4, x_3);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; 
x_11 = lean_array_uget(x_2, x_4);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_box(0);
lean_inc(x_1);
x_17 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_runRefreshTasks_spec__5_spec__5___redArg___lam__0___boxed), 6, 5);
lean_closure_set(x_17, 0, x_1);
lean_closure_set(x_17, 1, x_13);
lean_closure_set(x_17, 2, x_15);
lean_closure_set(x_17, 3, x_14);
lean_closure_set(x_17, 4, x_16);
x_18 = l_Lean_Server_ServerTask_BaseIO_asTask___redArg(x_17, x_8);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_array_push(x_5, x_19);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_usize_of_nat(x_22);
x_24 = lean_usize_add(x_4, x_23);
x_25 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_runRefreshTasks_spec__5_spec__5___redArg(x_1, x_2, x_3, x_24, x_21, x_20);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_runRefreshTasks(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_4 = l_Lean_Server_partialLspRequestHandlerMethods(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_mk_empty_array_with_capacity(x_7);
x_9 = lean_array_size(x_5);
x_10 = lean_usize_of_nat(x_7);
lean_inc(x_1);
x_11 = l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_runRefreshTasks_spec__5(x_1, x_5, x_9, x_10, x_8, x_1, x_2, x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_WorkerContext_initPendingServerRequest___at___Lean_Server_FileWorker_sendServerRequest___at___Lean_Server_FileWorker_runRefreshTasks_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_FileWorker_WorkerContext_initPendingServerRequest___at___Lean_Server_FileWorker_sendServerRequest___at___Lean_Server_FileWorker_runRefreshTasks_spec__0_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_WorkerContext_initPendingServerRequest___at___Lean_Server_FileWorker_sendServerRequest___at___Lean_Server_FileWorker_runRefreshTasks_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_FileWorker_WorkerContext_initPendingServerRequest___at___Lean_Server_FileWorker_sendServerRequest___at___Lean_Server_FileWorker_runRefreshTasks_spec__0_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_sendServerRequest___at___Lean_Server_FileWorker_runRefreshTasks_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Server_FileWorker_sendServerRequest___at___Lean_Server_FileWorker_runRefreshTasks_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Server_FileWorker_runRefreshTasks_spec__3_spec__3___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Server_FileWorker_runRefreshTasks_spec__3_spec__3___redArg___lam__0(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Server_FileWorker_runRefreshTasks_spec__3_spec__3___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Server_FileWorker_runRefreshTasks_spec__3_spec__3___redArg___lam__1(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Server_FileWorker_runRefreshTasks_spec__3_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Server_FileWorker_runRefreshTasks_spec__3_spec__3___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Server_FileWorker_runRefreshTasks_spec__3_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Server_FileWorker_runRefreshTasks_spec__3_spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Server_FileWorker_runRefreshTasks_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Loop_forIn_loop___at___Lean_Server_FileWorker_runRefreshTasks_spec__3___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Server_FileWorker_runRefreshTasks_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Loop_forIn_loop___at___Lean_Server_FileWorker_runRefreshTasks_spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_runRefreshTasks_spec__5_spec__5___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_runRefreshTasks_spec__5_spec__5___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_runRefreshTasks_spec__5_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_runRefreshTasks_spec__5_spec__5___redArg(x_1, x_2, x_7, x_8, x_5, x_6);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_runRefreshTasks_spec__5_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_runRefreshTasks_spec__5_spec__5(x_1, x_2, x_9, x_10, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_runRefreshTasks_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_runRefreshTasks_spec__5(x_1, x_2, x_9, x_10, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_runRefreshTasks___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_FileWorker_runRefreshTasks(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_initAndRunWorker_writeErrorDiag(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_35; lean_object* x_36; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_5);
lean_inc(x_6);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_ctor_get(x_2, 3);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_string_utf8_byte_size(x_11);
lean_dec(x_11);
x_13 = l_Lean_FileMap_utf8PosToLspPos(x_10, x_12);
lean_dec(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_6);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_box(0);
x_19 = lean_box(0);
x_20 = lean_box(0);
x_21 = lean_io_error_to_string(x_3);
x_22 = lean_box(0);
x_23 = lean_box(0);
x_24 = lean_box(0);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_26, 0, x_9);
lean_ctor_set(x_26, 1, x_15);
lean_ctor_set(x_26, 2, x_17);
lean_ctor_set(x_26, 3, x_18);
lean_ctor_set(x_26, 4, x_19);
lean_ctor_set(x_26, 5, x_20);
lean_ctor_set(x_26, 6, x_21);
lean_ctor_set(x_26, 7, x_22);
lean_ctor_set(x_26, 8, x_23);
lean_ctor_set(x_26, 9, x_24);
lean_ctor_set(x_26, 10, x_25);
x_27 = lean_mk_empty_array_with_capacity(x_7);
x_28 = lean_array_push(x_27, x_26);
x_29 = l_Lean_Server_mkPublishDiagnosticsNotification(x_2, x_28);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
lean_dec(x_29);
x_36 = l_Lean_Json_toStructured_x3f___at_____private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_publishDiagnostics_spec__1(x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; 
lean_dec(x_36);
x_37 = lean_box(0);
x_31 = x_37;
goto block_34;
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_36);
if (x_38 == 0)
{
x_31 = x_36;
goto block_34;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_36, 0);
lean_inc(x_39);
lean_dec(x_36);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_31 = x_40;
goto block_34;
}
}
block_34:
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_IO_FS_Stream_writeLspMessage(x_1, x_32, x_4);
return x_33;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___IO_FS_Stream_readRequestAs___at___IO_FS_Stream_readLspRequestAs___at___Lean_Server_FileWorker_initAndRunWorker_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l_Lean_Json_getInt_x3f(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___IO_FS_Stream_readRequestAs___at___IO_FS_Stream_readLspRequestAs___at___Lean_Server_FileWorker_initAndRunWorker_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_fromJsonClientInfo____x40_Lean_Data_Lsp_InitShutdown___hyg_70_(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___IO_FS_Stream_readRequestAs___at___IO_FS_Stream_readLspRequestAs___at___Lean_Server_FileWorker_initAndRunWorker_spec__0_spec__0_spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_fromJsonInitializationOptions____x40_Lean_Data_Lsp_InitShutdown___hyg_343_(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___IO_FS_Stream_readRequestAs___at___IO_FS_Stream_readLspRequestAs___at___Lean_Server_FileWorker_initAndRunWorker_spec__0_spec__0_spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l___private_Lean_Data_Lsp_Capabilities_0__Lean_Lsp_fromJsonClientCapabilities____x40_Lean_Data_Lsp_Capabilities___hyg_1347_(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___IO_FS_Stream_readRequestAs___at___IO_FS_Stream_readLspRequestAs___at___Lean_Server_FileWorker_initAndRunWorker_spec__0_spec__0_spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_Json_getObjValD(x_1, x_2);
x_7 = l_Lean_Json_getStr_x3f(x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_dec(x_7);
goto block_5;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_mk_string_unchecked("off", 3, 3);
x_11 = lean_string_dec_eq(x_9, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_mk_string_unchecked("messages", 8, 8);
x_13 = lean_string_dec_eq(x_9, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_mk_string_unchecked("verbose", 7, 7);
x_15 = lean_string_dec_eq(x_9, x_14);
lean_dec(x_14);
lean_dec(x_9);
if (x_15 == 0)
{
lean_free_object(x_7);
goto block_5;
}
else
{
lean_object* x_16; 
x_16 = lean_box(2);
lean_ctor_set(x_7, 0, x_16);
return x_7;
}
}
else
{
lean_object* x_17; 
lean_dec(x_9);
x_17 = lean_box(1);
lean_ctor_set(x_7, 0, x_17);
return x_7;
}
}
else
{
lean_object* x_18; 
lean_dec(x_9);
x_18 = lean_box(0);
lean_ctor_set(x_7, 0, x_18);
return x_7;
}
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_7, 0);
lean_inc(x_19);
lean_dec(x_7);
x_20 = lean_mk_string_unchecked("off", 3, 3);
x_21 = lean_string_dec_eq(x_19, x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_mk_string_unchecked("messages", 8, 8);
x_23 = lean_string_dec_eq(x_19, x_22);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_mk_string_unchecked("verbose", 7, 7);
x_25 = lean_string_dec_eq(x_19, x_24);
lean_dec(x_24);
lean_dec(x_19);
if (x_25 == 0)
{
goto block_5;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_box(2);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_19);
x_28 = lean_box(1);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_19);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
}
block_5:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_mk_string_unchecked("unknown trace", 13, 13);
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Json_getObjValAs_x3f___at___IO_FS_Stream_readRequestAs___at___IO_FS_Stream_readLspRequestAs___at___Lean_Server_FileWorker_initAndRunWorker_spec__0_spec__0_spec__5_spec__5(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_array_uget(x_3, x_2);
x_7 = l___private_Lean_Data_Lsp_Workspace_0__Lean_Lsp_fromJsonWorkspaceFolder____x40_Lean_Data_Lsp_Workspace___hyg_77_(x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
lean_dec(x_3);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
return x_7;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
x_12 = lean_box(0);
x_13 = lean_array_uset(x_3, x_2, x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_usize_of_nat(x_14);
x_16 = lean_usize_add(x_2, x_15);
x_17 = lean_array_uset(x_13, x_2, x_11);
x_2 = x_16;
x_3 = x_17;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___IO_FS_Stream_readRequestAs___at___IO_FS_Stream_readLspRequestAs___at___Lean_Server_FileWorker_initAndRunWorker_spec__0_spec__0_spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
if (lean_obj_tag(x_3) == 4)
{
lean_object* x_4; size_t x_5; lean_object* x_6; size_t x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_array_size(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_usize_of_nat(x_6);
x_8 = l_Array_mapMUnsafe_map___at___Lean_Json_getObjValAs_x3f___at___IO_FS_Stream_readRequestAs___at___IO_FS_Stream_readLspRequestAs___at___Lean_Server_FileWorker_initAndRunWorker_spec__0_spec__0_spec__5_spec__5(x_5, x_7, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_mk_string_unchecked("expected JSON array, got '", 26, 26);
x_10 = lean_unsigned_to_nat(80u);
x_11 = l_Lean_Json_pretty(x_3, x_10);
x_12 = lean_string_append(x_9, x_11);
lean_dec(x_11);
x_13 = lean_mk_string_unchecked("'", 1, 1);
x_14 = lean_string_append(x_12, x_13);
lean_dec(x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readRequestAs___at___IO_FS_Stream_readLspRequestAs___at___Lean_Server_FileWorker_initAndRunWorker_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_FS_Stream_readMessage(x_1, x_2, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_86; uint8_t x_129; 
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_8 = x_5;
} else {
 lean_dec_ref(x_5);
 x_8 = lean_box(0);
}
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_6, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_6, 2);
lean_inc(x_11);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 x_12 = x_6;
} else {
 lean_dec_ref(x_6);
 x_12 = lean_box(0);
}
x_129 = lean_string_dec_eq(x_10, x_3);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
x_130 = lean_mk_string_unchecked("Expected method '", 17, 17);
x_131 = lean_string_append(x_130, x_3);
lean_dec(x_3);
x_132 = lean_mk_string_unchecked("', got method '", 15, 15);
x_133 = lean_string_append(x_131, x_132);
lean_dec(x_132);
x_134 = lean_string_append(x_133, x_10);
lean_dec(x_10);
x_135 = lean_mk_string_unchecked("'", 1, 1);
x_136 = lean_string_append(x_134, x_135);
lean_dec(x_135);
x_137 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_137, 0, x_136);
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_7);
return x_138;
}
else
{
lean_dec(x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_139; 
x_139 = lean_box(0);
x_86 = x_139;
goto block_128;
}
else
{
lean_object* x_140; 
x_140 = lean_ctor_get(x_11, 0);
lean_inc(x_140);
lean_dec(x_11);
if (lean_obj_tag(x_140) == 0)
{
uint8_t x_141; 
x_141 = !lean_is_exclusive(x_140);
if (x_141 == 0)
{
lean_ctor_set_tag(x_140, 4);
x_86 = x_140;
goto block_128;
}
else
{
lean_object* x_142; lean_object* x_143; 
x_142 = lean_ctor_get(x_140, 0);
lean_inc(x_142);
lean_dec(x_140);
x_143 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_143, 0, x_142);
x_86 = x_143;
goto block_128;
}
}
else
{
uint8_t x_144; 
x_144 = !lean_is_exclusive(x_140);
if (x_144 == 0)
{
lean_ctor_set_tag(x_140, 5);
x_86 = x_140;
goto block_128;
}
else
{
lean_object* x_145; lean_object* x_146; 
x_145 = lean_ctor_get(x_140, 0);
lean_inc(x_145);
lean_dec(x_140);
x_146 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_146, 0, x_145);
x_86 = x_146;
goto block_128;
}
}
}
}
block_23:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_15);
lean_ctor_set(x_20, 2, x_14);
lean_ctor_set(x_20, 3, x_17);
lean_ctor_set(x_20, 4, x_13);
lean_ctor_set(x_20, 5, x_19);
lean_ctor_set_uint8(x_20, sizeof(void*)*6, x_18);
if (lean_is_scalar(x_12)) {
 x_21 = lean_alloc_ctor(0, 3, 0);
} else {
 x_21 = x_12;
}
lean_ctor_set(x_21, 0, x_9);
lean_ctor_set(x_21, 1, x_3);
lean_ctor_set(x_21, 2, x_20);
if (lean_is_scalar(x_8)) {
 x_22 = lean_alloc_ctor(0, 2, 0);
} else {
 x_22 = x_8;
}
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_7);
return x_22;
}
block_35:
{
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_31; 
lean_dec(x_28);
x_31 = lean_box(0);
x_13 = x_24;
x_14 = x_25;
x_15 = x_27;
x_16 = x_26;
x_17 = x_30;
x_18 = x_29;
x_19 = x_31;
goto block_23;
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_28);
if (x_32 == 0)
{
x_13 = x_24;
x_14 = x_25;
x_15 = x_27;
x_16 = x_26;
x_17 = x_30;
x_18 = x_29;
x_19 = x_28;
goto block_23;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_28, 0);
lean_inc(x_33);
lean_dec(x_28);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_13 = x_24;
x_14 = x_25;
x_15 = x_27;
x_16 = x_26;
x_17 = x_30;
x_18 = x_29;
x_19 = x_34;
goto block_23;
}
}
}
block_47:
{
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_43; 
lean_dec(x_37);
x_43 = lean_box(0);
x_24 = x_36;
x_25 = x_42;
x_26 = x_39;
x_27 = x_38;
x_28 = x_40;
x_29 = x_41;
x_30 = x_43;
goto block_35;
}
else
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_37);
if (x_44 == 0)
{
x_24 = x_36;
x_25 = x_42;
x_26 = x_39;
x_27 = x_38;
x_28 = x_40;
x_29 = x_41;
x_30 = x_37;
goto block_35;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_37, 0);
lean_inc(x_45);
lean_dec(x_37);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_45);
x_24 = x_36;
x_25 = x_42;
x_26 = x_39;
x_27 = x_38;
x_28 = x_40;
x_29 = x_41;
x_30 = x_46;
goto block_35;
}
}
}
block_59:
{
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_55; 
lean_dec(x_50);
x_55 = lean_box(0);
x_36 = x_48;
x_37 = x_49;
x_38 = x_54;
x_39 = x_51;
x_40 = x_52;
x_41 = x_53;
x_42 = x_55;
goto block_47;
}
else
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_50);
if (x_56 == 0)
{
x_36 = x_48;
x_37 = x_49;
x_38 = x_54;
x_39 = x_51;
x_40 = x_52;
x_41 = x_53;
x_42 = x_50;
goto block_47;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_50, 0);
lean_inc(x_57);
lean_dec(x_50);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_57);
x_36 = x_48;
x_37 = x_49;
x_38 = x_54;
x_39 = x_51;
x_40 = x_52;
x_41 = x_53;
x_42 = x_58;
goto block_47;
}
}
}
block_71:
{
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_67; 
lean_dec(x_62);
x_67 = lean_box(0);
x_48 = x_60;
x_49 = x_61;
x_50 = x_63;
x_51 = x_66;
x_52 = x_64;
x_53 = x_65;
x_54 = x_67;
goto block_59;
}
else
{
uint8_t x_68; 
x_68 = !lean_is_exclusive(x_62);
if (x_68 == 0)
{
x_48 = x_60;
x_49 = x_61;
x_50 = x_63;
x_51 = x_66;
x_52 = x_64;
x_53 = x_65;
x_54 = x_62;
goto block_59;
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_62, 0);
lean_inc(x_69);
lean_dec(x_62);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_69);
x_48 = x_60;
x_49 = x_61;
x_50 = x_63;
x_51 = x_66;
x_52 = x_64;
x_53 = x_65;
x_54 = x_70;
goto block_59;
}
}
}
block_85:
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_mk_string_unchecked("workspaceFolders", 16, 16);
x_80 = l_Lean_Json_getObjValAs_x3f___at___IO_FS_Stream_readRequestAs___at___IO_FS_Stream_readLspRequestAs___at___Lean_Server_FileWorker_initAndRunWorker_spec__0_spec__0_spec__5(x_77, x_79);
lean_dec(x_79);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_81; 
lean_dec(x_72);
x_81 = lean_box(0);
x_60 = x_73;
x_61 = x_74;
x_62 = x_76;
x_63 = x_75;
x_64 = x_80;
x_65 = x_78;
x_66 = x_81;
goto block_71;
}
else
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_72);
if (x_82 == 0)
{
x_60 = x_73;
x_61 = x_74;
x_62 = x_76;
x_63 = x_75;
x_64 = x_80;
x_65 = x_78;
x_66 = x_72;
goto block_71;
}
else
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_72, 0);
lean_inc(x_83);
lean_dec(x_72);
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_83);
x_60 = x_73;
x_61 = x_74;
x_62 = x_76;
x_63 = x_75;
x_64 = x_80;
x_65 = x_78;
x_66 = x_84;
goto block_71;
}
}
}
block_128:
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_mk_string_unchecked("capabilities", 12, 12);
lean_inc(x_86);
x_88 = l_Lean_Json_getObjValAs_x3f___at___IO_FS_Stream_readRequestAs___at___IO_FS_Stream_readLspRequestAs___at___Lean_Server_FileWorker_initAndRunWorker_spec__0_spec__0_spec__3(x_86, x_87);
lean_dec(x_87);
if (lean_obj_tag(x_88) == 0)
{
uint8_t x_89; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
x_89 = !lean_is_exclusive(x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_90 = lean_ctor_get(x_88, 0);
x_91 = lean_mk_string_unchecked("Unexpected param '", 18, 18);
x_92 = l_Lean_Json_compress(x_86);
x_93 = lean_string_append(x_91, x_92);
lean_dec(x_92);
x_94 = lean_mk_string_unchecked("' for method '", 14, 14);
x_95 = lean_string_append(x_93, x_94);
lean_dec(x_94);
x_96 = lean_string_append(x_95, x_3);
lean_dec(x_3);
x_97 = lean_mk_string_unchecked("'\n", 2, 2);
x_98 = lean_string_append(x_96, x_97);
lean_dec(x_97);
x_99 = lean_string_append(x_98, x_90);
lean_dec(x_90);
lean_ctor_set_tag(x_88, 18);
lean_ctor_set(x_88, 0, x_99);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_88);
lean_ctor_set(x_100, 1, x_7);
return x_100;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_101 = lean_ctor_get(x_88, 0);
lean_inc(x_101);
lean_dec(x_88);
x_102 = lean_mk_string_unchecked("Unexpected param '", 18, 18);
x_103 = l_Lean_Json_compress(x_86);
x_104 = lean_string_append(x_102, x_103);
lean_dec(x_103);
x_105 = lean_mk_string_unchecked("' for method '", 14, 14);
x_106 = lean_string_append(x_104, x_105);
lean_dec(x_105);
x_107 = lean_string_append(x_106, x_3);
lean_dec(x_3);
x_108 = lean_mk_string_unchecked("'\n", 2, 2);
x_109 = lean_string_append(x_107, x_108);
lean_dec(x_108);
x_110 = lean_string_append(x_109, x_101);
lean_dec(x_101);
x_111 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_111, 0, x_110);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_7);
return x_112;
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_113 = lean_ctor_get(x_88, 0);
lean_inc(x_113);
lean_dec(x_88);
x_114 = lean_mk_string_unchecked("processId", 9, 9);
x_115 = lean_mk_string_unchecked("clientInfo", 10, 10);
x_116 = lean_mk_string_unchecked("rootUri", 7, 7);
x_117 = lean_mk_string_unchecked("initializationOptions", 21, 21);
lean_inc(x_86);
x_118 = l_Lean_Json_getObjValAs_x3f___at___IO_FS_Stream_readRequestAs___at___IO_FS_Stream_readLspRequestAs___at___Lean_Server_FileWorker_initAndRunWorker_spec__0_spec__0_spec__0(x_86, x_114);
lean_dec(x_114);
lean_inc(x_86);
x_119 = l_Lean_Json_getObjValAs_x3f___at___IO_FS_Stream_readRequestAs___at___IO_FS_Stream_readLspRequestAs___at___Lean_Server_FileWorker_initAndRunWorker_spec__0_spec__0_spec__1(x_86, x_115);
lean_dec(x_115);
lean_inc(x_86);
x_120 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Window_0__fromJsonShowMessageParams____x40_Lean_Data_Lsp_Window___hyg_139__spec__1(x_86, x_116);
lean_dec(x_116);
lean_inc(x_86);
x_121 = l_Lean_Json_getObjValAs_x3f___at___IO_FS_Stream_readRequestAs___at___IO_FS_Stream_readLspRequestAs___at___Lean_Server_FileWorker_initAndRunWorker_spec__0_spec__0_spec__2(x_86, x_117);
lean_dec(x_117);
x_122 = lean_mk_string_unchecked("trace", 5, 5);
lean_inc(x_86);
x_123 = l_Lean_Json_getObjValAs_x3f___at___IO_FS_Stream_readRequestAs___at___IO_FS_Stream_readLspRequestAs___at___Lean_Server_FileWorker_initAndRunWorker_spec__0_spec__0_spec__4(x_86, x_122);
lean_dec(x_122);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; uint8_t x_125; 
lean_dec(x_123);
x_124 = lean_box(0);
x_125 = lean_unbox(x_124);
x_72 = x_118;
x_73 = x_113;
x_74 = x_121;
x_75 = x_120;
x_76 = x_119;
x_77 = x_86;
x_78 = x_125;
goto block_85;
}
else
{
lean_object* x_126; uint8_t x_127; 
x_126 = lean_ctor_get(x_123, 0);
lean_inc(x_126);
lean_dec(x_123);
x_127 = lean_unbox(x_126);
lean_dec(x_126);
x_72 = x_118;
x_73 = x_113;
x_74 = x_121;
x_75 = x_120;
x_76 = x_119;
x_77 = x_86;
x_78 = x_127;
goto block_85;
}
}
}
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
lean_dec(x_3);
x_147 = lean_ctor_get(x_5, 1);
lean_inc(x_147);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_148 = x_5;
} else {
 lean_dec_ref(x_5);
 x_148 = lean_box(0);
}
x_149 = lean_mk_string_unchecked("Expected JSON-RPC request, got: '", 33, 33);
x_150 = lean_mk_string_unchecked("jsonrpc", 7, 7);
x_151 = lean_mk_string_unchecked("2.0", 3, 3);
x_152 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_152, 0, x_151);
x_153 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_153, 0, x_150);
lean_ctor_set(x_153, 1, x_152);
switch (lean_obj_tag(x_6)) {
case 0:
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_164 = lean_ctor_get(x_6, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_6, 1);
lean_inc(x_165);
x_166 = lean_ctor_get(x_6, 2);
lean_inc(x_166);
lean_dec(x_6);
x_167 = lean_mk_string_unchecked("id", 2, 2);
if (lean_obj_tag(x_164) == 0)
{
uint8_t x_180; 
x_180 = !lean_is_exclusive(x_164);
if (x_180 == 0)
{
lean_ctor_set_tag(x_164, 3);
x_168 = x_164;
goto block_179;
}
else
{
lean_object* x_181; lean_object* x_182; 
x_181 = lean_ctor_get(x_164, 0);
lean_inc(x_181);
lean_dec(x_164);
x_182 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_182, 0, x_181);
x_168 = x_182;
goto block_179;
}
}
else
{
uint8_t x_183; 
x_183 = !lean_is_exclusive(x_164);
if (x_183 == 0)
{
lean_ctor_set_tag(x_164, 2);
x_168 = x_164;
goto block_179;
}
else
{
lean_object* x_184; lean_object* x_185; 
x_184 = lean_ctor_get(x_164, 0);
lean_inc(x_184);
lean_dec(x_164);
x_185 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_185, 0, x_184);
x_168 = x_185;
goto block_179;
}
}
block_179:
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_169, 0, x_167);
lean_ctor_set(x_169, 1, x_168);
x_170 = lean_mk_string_unchecked("method", 6, 6);
x_171 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_171, 0, x_165);
x_172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_172, 0, x_170);
lean_ctor_set(x_172, 1, x_171);
x_173 = lean_box(0);
x_174 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_174, 0, x_172);
lean_ctor_set(x_174, 1, x_173);
x_175 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_175, 0, x_169);
lean_ctor_set(x_175, 1, x_174);
x_176 = lean_mk_string_unchecked("params", 6, 6);
x_177 = l_Lean_Json_opt___at___IO_FS_Stream_writeMessage_spec__0(x_176, x_166);
x_178 = l_List_appendTR(lean_box(0), x_175, x_177);
x_154 = x_178;
goto block_163;
}
}
case 1:
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_186 = lean_ctor_get(x_6, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_6, 1);
lean_inc(x_187);
lean_dec(x_6);
x_188 = lean_mk_string_unchecked("method", 6, 6);
x_189 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_189, 0, x_186);
x_190 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_190, 0, x_188);
lean_ctor_set(x_190, 1, x_189);
x_191 = lean_mk_string_unchecked("params", 6, 6);
x_192 = l_Lean_Json_opt___at___IO_FS_Stream_writeMessage_spec__0(x_191, x_187);
x_193 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_193, 0, x_190);
lean_ctor_set(x_193, 1, x_192);
x_154 = x_193;
goto block_163;
}
case 2:
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_194 = lean_ctor_get(x_6, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_6, 1);
lean_inc(x_195);
lean_dec(x_6);
x_196 = lean_mk_string_unchecked("id", 2, 2);
if (lean_obj_tag(x_194) == 0)
{
uint8_t x_205; 
x_205 = !lean_is_exclusive(x_194);
if (x_205 == 0)
{
lean_ctor_set_tag(x_194, 3);
x_197 = x_194;
goto block_204;
}
else
{
lean_object* x_206; lean_object* x_207; 
x_206 = lean_ctor_get(x_194, 0);
lean_inc(x_206);
lean_dec(x_194);
x_207 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_207, 0, x_206);
x_197 = x_207;
goto block_204;
}
}
else
{
uint8_t x_208; 
x_208 = !lean_is_exclusive(x_194);
if (x_208 == 0)
{
lean_ctor_set_tag(x_194, 2);
x_197 = x_194;
goto block_204;
}
else
{
lean_object* x_209; lean_object* x_210; 
x_209 = lean_ctor_get(x_194, 0);
lean_inc(x_209);
lean_dec(x_194);
x_210 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_210, 0, x_209);
x_197 = x_210;
goto block_204;
}
}
block_204:
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_198 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_198, 0, x_196);
lean_ctor_set(x_198, 1, x_197);
x_199 = lean_mk_string_unchecked("result", 6, 6);
x_200 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_200, 0, x_199);
lean_ctor_set(x_200, 1, x_195);
x_201 = lean_box(0);
x_202 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_202, 0, x_200);
lean_ctor_set(x_202, 1, x_201);
x_203 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_203, 0, x_198);
lean_ctor_set(x_203, 1, x_202);
x_154 = x_203;
goto block_163;
}
}
default: 
{
lean_object* x_211; uint8_t x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_234; lean_object* x_235; 
x_211 = lean_ctor_get(x_6, 0);
lean_inc(x_211);
x_212 = lean_ctor_get_uint8(x_6, sizeof(void*)*3);
x_213 = lean_ctor_get(x_6, 1);
lean_inc(x_213);
x_214 = lean_ctor_get(x_6, 2);
lean_inc(x_214);
lean_dec(x_6);
x_234 = lean_mk_string_unchecked("id", 2, 2);
if (lean_obj_tag(x_211) == 0)
{
uint8_t x_300; 
x_300 = !lean_is_exclusive(x_211);
if (x_300 == 0)
{
lean_ctor_set_tag(x_211, 3);
x_235 = x_211;
goto block_299;
}
else
{
lean_object* x_301; lean_object* x_302; 
x_301 = lean_ctor_get(x_211, 0);
lean_inc(x_301);
lean_dec(x_211);
x_302 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_302, 0, x_301);
x_235 = x_302;
goto block_299;
}
}
else
{
uint8_t x_303; 
x_303 = !lean_is_exclusive(x_211);
if (x_303 == 0)
{
lean_ctor_set_tag(x_211, 2);
x_235 = x_211;
goto block_299;
}
else
{
lean_object* x_304; lean_object* x_305; 
x_304 = lean_ctor_get(x_211, 0);
lean_inc(x_304);
lean_dec(x_211);
x_305 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_305, 0, x_304);
x_235 = x_305;
goto block_299;
}
}
block_233:
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_219 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_219, 0, x_215);
lean_ctor_set(x_219, 1, x_218);
x_220 = lean_mk_string_unchecked("message", 7, 7);
x_221 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_221, 0, x_213);
x_222 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_222, 0, x_220);
lean_ctor_set(x_222, 1, x_221);
x_223 = lean_box(0);
x_224 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_224, 0, x_222);
lean_ctor_set(x_224, 1, x_223);
x_225 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_225, 0, x_219);
lean_ctor_set(x_225, 1, x_224);
x_226 = lean_mk_string_unchecked("data", 4, 4);
x_227 = l_Lean_Json_opt___at_____private_Lean_Widget_InteractiveCode_0__Lean_Widget_toJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveCode___hyg_552__spec__0(x_226, x_214);
lean_dec(x_214);
x_228 = l_List_appendTR(lean_box(0), x_225, x_227);
x_229 = l_Lean_Json_mkObj(x_228);
x_230 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_230, 0, x_216);
lean_ctor_set(x_230, 1, x_229);
x_231 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_231, 0, x_230);
lean_ctor_set(x_231, 1, x_223);
x_232 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_232, 0, x_217);
lean_ctor_set(x_232, 1, x_231);
x_154 = x_232;
goto block_163;
}
block_299:
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_236 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_236, 0, x_234);
lean_ctor_set(x_236, 1, x_235);
x_237 = lean_mk_string_unchecked("error", 5, 5);
x_238 = lean_mk_string_unchecked("code", 4, 4);
switch (x_212) {
case 0:
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
x_239 = lean_unsigned_to_nat(32700u);
x_240 = lean_nat_to_int(x_239);
x_241 = lean_int_neg(x_240);
lean_dec(x_240);
x_242 = l_Lean_JsonNumber_fromInt(x_241);
x_243 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_243, 0, x_242);
x_215 = x_238;
x_216 = x_237;
x_217 = x_236;
x_218 = x_243;
goto block_233;
}
case 1:
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_244 = lean_unsigned_to_nat(32600u);
x_245 = lean_nat_to_int(x_244);
x_246 = lean_int_neg(x_245);
lean_dec(x_245);
x_247 = l_Lean_JsonNumber_fromInt(x_246);
x_248 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_248, 0, x_247);
x_215 = x_238;
x_216 = x_237;
x_217 = x_236;
x_218 = x_248;
goto block_233;
}
case 2:
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_249 = lean_unsigned_to_nat(32601u);
x_250 = lean_nat_to_int(x_249);
x_251 = lean_int_neg(x_250);
lean_dec(x_250);
x_252 = l_Lean_JsonNumber_fromInt(x_251);
x_253 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_253, 0, x_252);
x_215 = x_238;
x_216 = x_237;
x_217 = x_236;
x_218 = x_253;
goto block_233;
}
case 3:
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_254 = lean_unsigned_to_nat(32602u);
x_255 = lean_nat_to_int(x_254);
x_256 = lean_int_neg(x_255);
lean_dec(x_255);
x_257 = l_Lean_JsonNumber_fromInt(x_256);
x_258 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_258, 0, x_257);
x_215 = x_238;
x_216 = x_237;
x_217 = x_236;
x_218 = x_258;
goto block_233;
}
case 4:
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
x_259 = lean_unsigned_to_nat(32603u);
x_260 = lean_nat_to_int(x_259);
x_261 = lean_int_neg(x_260);
lean_dec(x_260);
x_262 = l_Lean_JsonNumber_fromInt(x_261);
x_263 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_263, 0, x_262);
x_215 = x_238;
x_216 = x_237;
x_217 = x_236;
x_218 = x_263;
goto block_233;
}
case 5:
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_264 = lean_unsigned_to_nat(32002u);
x_265 = lean_nat_to_int(x_264);
x_266 = lean_int_neg(x_265);
lean_dec(x_265);
x_267 = l_Lean_JsonNumber_fromInt(x_266);
x_268 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_268, 0, x_267);
x_215 = x_238;
x_216 = x_237;
x_217 = x_236;
x_218 = x_268;
goto block_233;
}
case 6:
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; 
x_269 = lean_unsigned_to_nat(32001u);
x_270 = lean_nat_to_int(x_269);
x_271 = lean_int_neg(x_270);
lean_dec(x_270);
x_272 = l_Lean_JsonNumber_fromInt(x_271);
x_273 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_273, 0, x_272);
x_215 = x_238;
x_216 = x_237;
x_217 = x_236;
x_218 = x_273;
goto block_233;
}
case 7:
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_274 = lean_unsigned_to_nat(32801u);
x_275 = lean_nat_to_int(x_274);
x_276 = lean_int_neg(x_275);
lean_dec(x_275);
x_277 = l_Lean_JsonNumber_fromInt(x_276);
x_278 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_278, 0, x_277);
x_215 = x_238;
x_216 = x_237;
x_217 = x_236;
x_218 = x_278;
goto block_233;
}
case 8:
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; 
x_279 = lean_unsigned_to_nat(32800u);
x_280 = lean_nat_to_int(x_279);
x_281 = lean_int_neg(x_280);
lean_dec(x_280);
x_282 = l_Lean_JsonNumber_fromInt(x_281);
x_283 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_283, 0, x_282);
x_215 = x_238;
x_216 = x_237;
x_217 = x_236;
x_218 = x_283;
goto block_233;
}
case 9:
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; 
x_284 = lean_unsigned_to_nat(32900u);
x_285 = lean_nat_to_int(x_284);
x_286 = lean_int_neg(x_285);
lean_dec(x_285);
x_287 = l_Lean_JsonNumber_fromInt(x_286);
x_288 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_288, 0, x_287);
x_215 = x_238;
x_216 = x_237;
x_217 = x_236;
x_218 = x_288;
goto block_233;
}
case 10:
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; 
x_289 = lean_unsigned_to_nat(32901u);
x_290 = lean_nat_to_int(x_289);
x_291 = lean_int_neg(x_290);
lean_dec(x_290);
x_292 = l_Lean_JsonNumber_fromInt(x_291);
x_293 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_293, 0, x_292);
x_215 = x_238;
x_216 = x_237;
x_217 = x_236;
x_218 = x_293;
goto block_233;
}
default: 
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; 
x_294 = lean_unsigned_to_nat(32902u);
x_295 = lean_nat_to_int(x_294);
x_296 = lean_int_neg(x_295);
lean_dec(x_295);
x_297 = l_Lean_JsonNumber_fromInt(x_296);
x_298 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_298, 0, x_297);
x_215 = x_238;
x_216 = x_237;
x_217 = x_236;
x_218 = x_298;
goto block_233;
}
}
}
}
}
block_163:
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_154);
x_156 = l_Lean_Json_mkObj(x_155);
x_157 = l_Lean_Json_compress(x_156);
x_158 = lean_string_append(x_149, x_157);
lean_dec(x_157);
x_159 = lean_mk_string_unchecked("'", 1, 1);
x_160 = lean_string_append(x_158, x_159);
lean_dec(x_159);
x_161 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_161, 0, x_160);
if (lean_is_scalar(x_148)) {
 x_162 = lean_alloc_ctor(1, 2, 0);
} else {
 x_162 = x_148;
 lean_ctor_set_tag(x_162, 1);
}
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_147);
return x_162;
}
}
}
else
{
uint8_t x_306; 
lean_dec(x_3);
x_306 = !lean_is_exclusive(x_5);
if (x_306 == 0)
{
return x_5;
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_307 = lean_ctor_get(x_5, 0);
x_308 = lean_ctor_get(x_5, 1);
lean_inc(x_308);
lean_inc(x_307);
lean_dec(x_5);
x_309 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_309, 0, x_307);
lean_ctor_set(x_309, 1, x_308);
return x_309;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspRequestAs___at___Lean_Server_FileWorker_initAndRunWorker_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_12; 
lean_inc(x_1);
x_12 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader(x_1, x_3);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_IO_FS_Stream_readRequestAs___at___IO_FS_Stream_readLspRequestAs___at___Lean_Server_FileWorker_initAndRunWorker_spec__0_spec__0(x_1, x_13, x_2, x_14);
lean_dec(x_13);
if (lean_obj_tag(x_15) == 0)
{
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_4 = x_16;
x_5 = x_17;
goto block_11;
}
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_2);
lean_dec(x_1);
x_18 = lean_ctor_get(x_12, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_dec(x_12);
x_4 = x_18;
x_5 = x_19;
goto block_11;
}
block_11:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_mk_string_unchecked("Cannot read LSP request: ", 25, 25);
x_7 = lean_io_error_to_string(x_4);
x_8 = lean_string_append(x_6, x_7);
lean_dec(x_7);
x_9 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_5);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readNotificationAs___at___IO_FS_Stream_readLspNotificationAs___at___Lean_Server_FileWorker_initAndRunWorker_spec__9_spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_FS_Stream_readMessage(x_1, x_2, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_8 = x_5;
} else {
 lean_dec_ref(x_5);
 x_8 = lean_box(0);
}
if (lean_obj_tag(x_6) == 1)
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_6);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_40 = lean_ctor_get(x_6, 0);
x_41 = lean_ctor_get(x_6, 1);
x_42 = lean_string_dec_eq(x_40, x_3);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_41);
lean_dec(x_8);
x_43 = lean_mk_string_unchecked("Expected method '", 17, 17);
x_44 = lean_string_append(x_43, x_3);
lean_dec(x_3);
x_45 = lean_mk_string_unchecked("', got method '", 15, 15);
x_46 = lean_string_append(x_44, x_45);
lean_dec(x_45);
x_47 = lean_string_append(x_46, x_40);
lean_dec(x_40);
x_48 = lean_mk_string_unchecked("'", 1, 1);
x_49 = lean_string_append(x_47, x_48);
lean_dec(x_48);
x_50 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_6, 1, x_7);
lean_ctor_set(x_6, 0, x_50);
return x_6;
}
else
{
lean_free_object(x_6);
lean_dec(x_40);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_51; 
x_51 = lean_box(0);
x_9 = x_51;
goto block_38;
}
else
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_41, 0);
lean_inc(x_52);
lean_dec(x_41);
if (lean_obj_tag(x_52) == 0)
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_ctor_set_tag(x_52, 4);
x_9 = x_52;
goto block_38;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_52, 0);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_55, 0, x_54);
x_9 = x_55;
goto block_38;
}
}
else
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_52);
if (x_56 == 0)
{
lean_ctor_set_tag(x_52, 5);
x_9 = x_52;
goto block_38;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_52, 0);
lean_inc(x_57);
lean_dec(x_52);
x_58 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_58, 0, x_57);
x_9 = x_58;
goto block_38;
}
}
}
}
}
else
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_59 = lean_ctor_get(x_6, 0);
x_60 = lean_ctor_get(x_6, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_6);
x_61 = lean_string_dec_eq(x_59, x_3);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_60);
lean_dec(x_8);
x_62 = lean_mk_string_unchecked("Expected method '", 17, 17);
x_63 = lean_string_append(x_62, x_3);
lean_dec(x_3);
x_64 = lean_mk_string_unchecked("', got method '", 15, 15);
x_65 = lean_string_append(x_63, x_64);
lean_dec(x_64);
x_66 = lean_string_append(x_65, x_59);
lean_dec(x_59);
x_67 = lean_mk_string_unchecked("'", 1, 1);
x_68 = lean_string_append(x_66, x_67);
lean_dec(x_67);
x_69 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_69, 0, x_68);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_7);
return x_70;
}
else
{
lean_dec(x_59);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_71; 
x_71 = lean_box(0);
x_9 = x_71;
goto block_38;
}
else
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_60, 0);
lean_inc(x_72);
lean_dec(x_60);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 x_74 = x_72;
} else {
 lean_dec_ref(x_72);
 x_74 = lean_box(0);
}
if (lean_is_scalar(x_74)) {
 x_75 = lean_alloc_ctor(4, 1, 0);
} else {
 x_75 = x_74;
 lean_ctor_set_tag(x_75, 4);
}
lean_ctor_set(x_75, 0, x_73);
x_9 = x_75;
goto block_38;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_72, 0);
lean_inc(x_76);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 x_77 = x_72;
} else {
 lean_dec_ref(x_72);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(5, 1, 0);
} else {
 x_78 = x_77;
 lean_ctor_set_tag(x_78, 5);
}
lean_ctor_set(x_78, 0, x_76);
x_9 = x_78;
goto block_38;
}
}
}
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_8);
lean_dec(x_3);
x_79 = lean_mk_string_unchecked("Expected JSON-RPC notification, got: '", 38, 38);
x_80 = lean_mk_string_unchecked("jsonrpc", 7, 7);
x_81 = lean_mk_string_unchecked("2.0", 3, 3);
x_82 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_82, 0, x_81);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_80);
lean_ctor_set(x_83, 1, x_82);
switch (lean_obj_tag(x_6)) {
case 0:
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_94 = lean_ctor_get(x_6, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_6, 1);
lean_inc(x_95);
x_96 = lean_ctor_get(x_6, 2);
lean_inc(x_96);
lean_dec(x_6);
x_97 = lean_mk_string_unchecked("id", 2, 2);
if (lean_obj_tag(x_94) == 0)
{
uint8_t x_110; 
x_110 = !lean_is_exclusive(x_94);
if (x_110 == 0)
{
lean_ctor_set_tag(x_94, 3);
x_98 = x_94;
goto block_109;
}
else
{
lean_object* x_111; lean_object* x_112; 
x_111 = lean_ctor_get(x_94, 0);
lean_inc(x_111);
lean_dec(x_94);
x_112 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_112, 0, x_111);
x_98 = x_112;
goto block_109;
}
}
else
{
uint8_t x_113; 
x_113 = !lean_is_exclusive(x_94);
if (x_113 == 0)
{
lean_ctor_set_tag(x_94, 2);
x_98 = x_94;
goto block_109;
}
else
{
lean_object* x_114; lean_object* x_115; 
x_114 = lean_ctor_get(x_94, 0);
lean_inc(x_114);
lean_dec(x_94);
x_115 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_115, 0, x_114);
x_98 = x_115;
goto block_109;
}
}
block_109:
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
x_100 = lean_mk_string_unchecked("method", 6, 6);
x_101 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_101, 0, x_95);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
x_103 = lean_box(0);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_99);
lean_ctor_set(x_105, 1, x_104);
x_106 = lean_mk_string_unchecked("params", 6, 6);
x_107 = l_Lean_Json_opt___at___IO_FS_Stream_writeMessage_spec__0(x_106, x_96);
x_108 = l_List_appendTR(lean_box(0), x_105, x_107);
x_84 = x_108;
goto block_93;
}
}
case 1:
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_116 = lean_ctor_get(x_6, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_6, 1);
lean_inc(x_117);
lean_dec(x_6);
x_118 = lean_mk_string_unchecked("method", 6, 6);
x_119 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_119, 0, x_116);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
x_121 = lean_mk_string_unchecked("params", 6, 6);
x_122 = l_Lean_Json_opt___at___IO_FS_Stream_writeMessage_spec__0(x_121, x_117);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_120);
lean_ctor_set(x_123, 1, x_122);
x_84 = x_123;
goto block_93;
}
case 2:
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_124 = lean_ctor_get(x_6, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_6, 1);
lean_inc(x_125);
lean_dec(x_6);
x_126 = lean_mk_string_unchecked("id", 2, 2);
if (lean_obj_tag(x_124) == 0)
{
uint8_t x_135; 
x_135 = !lean_is_exclusive(x_124);
if (x_135 == 0)
{
lean_ctor_set_tag(x_124, 3);
x_127 = x_124;
goto block_134;
}
else
{
lean_object* x_136; lean_object* x_137; 
x_136 = lean_ctor_get(x_124, 0);
lean_inc(x_136);
lean_dec(x_124);
x_137 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_137, 0, x_136);
x_127 = x_137;
goto block_134;
}
}
else
{
uint8_t x_138; 
x_138 = !lean_is_exclusive(x_124);
if (x_138 == 0)
{
lean_ctor_set_tag(x_124, 2);
x_127 = x_124;
goto block_134;
}
else
{
lean_object* x_139; lean_object* x_140; 
x_139 = lean_ctor_get(x_124, 0);
lean_inc(x_139);
lean_dec(x_124);
x_140 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_140, 0, x_139);
x_127 = x_140;
goto block_134;
}
}
block_134:
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
x_129 = lean_mk_string_unchecked("result", 6, 6);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_125);
x_131 = lean_box(0);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_128);
lean_ctor_set(x_133, 1, x_132);
x_84 = x_133;
goto block_93;
}
}
default: 
{
lean_object* x_141; uint8_t x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_164; lean_object* x_165; 
x_141 = lean_ctor_get(x_6, 0);
lean_inc(x_141);
x_142 = lean_ctor_get_uint8(x_6, sizeof(void*)*3);
x_143 = lean_ctor_get(x_6, 1);
lean_inc(x_143);
x_144 = lean_ctor_get(x_6, 2);
lean_inc(x_144);
lean_dec(x_6);
x_164 = lean_mk_string_unchecked("id", 2, 2);
if (lean_obj_tag(x_141) == 0)
{
uint8_t x_230; 
x_230 = !lean_is_exclusive(x_141);
if (x_230 == 0)
{
lean_ctor_set_tag(x_141, 3);
x_165 = x_141;
goto block_229;
}
else
{
lean_object* x_231; lean_object* x_232; 
x_231 = lean_ctor_get(x_141, 0);
lean_inc(x_231);
lean_dec(x_141);
x_232 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_232, 0, x_231);
x_165 = x_232;
goto block_229;
}
}
else
{
uint8_t x_233; 
x_233 = !lean_is_exclusive(x_141);
if (x_233 == 0)
{
lean_ctor_set_tag(x_141, 2);
x_165 = x_141;
goto block_229;
}
else
{
lean_object* x_234; lean_object* x_235; 
x_234 = lean_ctor_get(x_141, 0);
lean_inc(x_234);
lean_dec(x_141);
x_235 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_235, 0, x_234);
x_165 = x_235;
goto block_229;
}
}
block_163:
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_145);
lean_ctor_set(x_149, 1, x_148);
x_150 = lean_mk_string_unchecked("message", 7, 7);
x_151 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_151, 0, x_143);
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_151);
x_153 = lean_box(0);
x_154 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_154, 0, x_152);
lean_ctor_set(x_154, 1, x_153);
x_155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_155, 0, x_149);
lean_ctor_set(x_155, 1, x_154);
x_156 = lean_mk_string_unchecked("data", 4, 4);
x_157 = l_Lean_Json_opt___at_____private_Lean_Widget_InteractiveCode_0__Lean_Widget_toJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveCode___hyg_552__spec__0(x_156, x_144);
lean_dec(x_144);
x_158 = l_List_appendTR(lean_box(0), x_155, x_157);
x_159 = l_Lean_Json_mkObj(x_158);
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_147);
lean_ctor_set(x_160, 1, x_159);
x_161 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_153);
x_162 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_162, 0, x_146);
lean_ctor_set(x_162, 1, x_161);
x_84 = x_162;
goto block_93;
}
block_229:
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_164);
lean_ctor_set(x_166, 1, x_165);
x_167 = lean_mk_string_unchecked("error", 5, 5);
x_168 = lean_mk_string_unchecked("code", 4, 4);
switch (x_142) {
case 0:
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_169 = lean_unsigned_to_nat(32700u);
x_170 = lean_nat_to_int(x_169);
x_171 = lean_int_neg(x_170);
lean_dec(x_170);
x_172 = l_Lean_JsonNumber_fromInt(x_171);
x_173 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_173, 0, x_172);
x_145 = x_168;
x_146 = x_166;
x_147 = x_167;
x_148 = x_173;
goto block_163;
}
case 1:
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_174 = lean_unsigned_to_nat(32600u);
x_175 = lean_nat_to_int(x_174);
x_176 = lean_int_neg(x_175);
lean_dec(x_175);
x_177 = l_Lean_JsonNumber_fromInt(x_176);
x_178 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_178, 0, x_177);
x_145 = x_168;
x_146 = x_166;
x_147 = x_167;
x_148 = x_178;
goto block_163;
}
case 2:
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_179 = lean_unsigned_to_nat(32601u);
x_180 = lean_nat_to_int(x_179);
x_181 = lean_int_neg(x_180);
lean_dec(x_180);
x_182 = l_Lean_JsonNumber_fromInt(x_181);
x_183 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_183, 0, x_182);
x_145 = x_168;
x_146 = x_166;
x_147 = x_167;
x_148 = x_183;
goto block_163;
}
case 3:
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_184 = lean_unsigned_to_nat(32602u);
x_185 = lean_nat_to_int(x_184);
x_186 = lean_int_neg(x_185);
lean_dec(x_185);
x_187 = l_Lean_JsonNumber_fromInt(x_186);
x_188 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_188, 0, x_187);
x_145 = x_168;
x_146 = x_166;
x_147 = x_167;
x_148 = x_188;
goto block_163;
}
case 4:
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_189 = lean_unsigned_to_nat(32603u);
x_190 = lean_nat_to_int(x_189);
x_191 = lean_int_neg(x_190);
lean_dec(x_190);
x_192 = l_Lean_JsonNumber_fromInt(x_191);
x_193 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_193, 0, x_192);
x_145 = x_168;
x_146 = x_166;
x_147 = x_167;
x_148 = x_193;
goto block_163;
}
case 5:
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_194 = lean_unsigned_to_nat(32002u);
x_195 = lean_nat_to_int(x_194);
x_196 = lean_int_neg(x_195);
lean_dec(x_195);
x_197 = l_Lean_JsonNumber_fromInt(x_196);
x_198 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_198, 0, x_197);
x_145 = x_168;
x_146 = x_166;
x_147 = x_167;
x_148 = x_198;
goto block_163;
}
case 6:
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_199 = lean_unsigned_to_nat(32001u);
x_200 = lean_nat_to_int(x_199);
x_201 = lean_int_neg(x_200);
lean_dec(x_200);
x_202 = l_Lean_JsonNumber_fromInt(x_201);
x_203 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_203, 0, x_202);
x_145 = x_168;
x_146 = x_166;
x_147 = x_167;
x_148 = x_203;
goto block_163;
}
case 7:
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_204 = lean_unsigned_to_nat(32801u);
x_205 = lean_nat_to_int(x_204);
x_206 = lean_int_neg(x_205);
lean_dec(x_205);
x_207 = l_Lean_JsonNumber_fromInt(x_206);
x_208 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_208, 0, x_207);
x_145 = x_168;
x_146 = x_166;
x_147 = x_167;
x_148 = x_208;
goto block_163;
}
case 8:
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_209 = lean_unsigned_to_nat(32800u);
x_210 = lean_nat_to_int(x_209);
x_211 = lean_int_neg(x_210);
lean_dec(x_210);
x_212 = l_Lean_JsonNumber_fromInt(x_211);
x_213 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_213, 0, x_212);
x_145 = x_168;
x_146 = x_166;
x_147 = x_167;
x_148 = x_213;
goto block_163;
}
case 9:
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_214 = lean_unsigned_to_nat(32900u);
x_215 = lean_nat_to_int(x_214);
x_216 = lean_int_neg(x_215);
lean_dec(x_215);
x_217 = l_Lean_JsonNumber_fromInt(x_216);
x_218 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_218, 0, x_217);
x_145 = x_168;
x_146 = x_166;
x_147 = x_167;
x_148 = x_218;
goto block_163;
}
case 10:
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_219 = lean_unsigned_to_nat(32901u);
x_220 = lean_nat_to_int(x_219);
x_221 = lean_int_neg(x_220);
lean_dec(x_220);
x_222 = l_Lean_JsonNumber_fromInt(x_221);
x_223 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_223, 0, x_222);
x_145 = x_168;
x_146 = x_166;
x_147 = x_167;
x_148 = x_223;
goto block_163;
}
default: 
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_224 = lean_unsigned_to_nat(32902u);
x_225 = lean_nat_to_int(x_224);
x_226 = lean_int_neg(x_225);
lean_dec(x_225);
x_227 = l_Lean_JsonNumber_fromInt(x_226);
x_228 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_228, 0, x_227);
x_145 = x_168;
x_146 = x_166;
x_147 = x_167;
x_148 = x_228;
goto block_163;
}
}
}
}
}
block_93:
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
x_86 = l_Lean_Json_mkObj(x_85);
x_87 = l_Lean_Json_compress(x_86);
x_88 = lean_string_append(x_79, x_87);
lean_dec(x_87);
x_89 = lean_mk_string_unchecked("'", 1, 1);
x_90 = lean_string_append(x_88, x_89);
lean_dec(x_89);
x_91 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_91, 0, x_90);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_7);
return x_92;
}
}
block_38:
{
lean_object* x_10; 
lean_inc(x_9);
x_10 = l___private_Lean_Data_Lsp_Extra_0__Lean_Lsp_fromJsonLeanDidOpenTextDocumentParams____x40_Lean_Data_Lsp_Extra___hyg_203_(x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_mk_string_unchecked("Unexpected param '", 18, 18);
x_14 = l_Lean_Json_compress(x_9);
x_15 = lean_string_append(x_13, x_14);
lean_dec(x_14);
x_16 = lean_mk_string_unchecked("' for method '", 14, 14);
x_17 = lean_string_append(x_15, x_16);
lean_dec(x_16);
x_18 = lean_string_append(x_17, x_3);
lean_dec(x_3);
x_19 = lean_mk_string_unchecked("'\n", 2, 2);
x_20 = lean_string_append(x_18, x_19);
lean_dec(x_19);
x_21 = lean_string_append(x_20, x_12);
lean_dec(x_12);
lean_ctor_set_tag(x_10, 18);
lean_ctor_set(x_10, 0, x_21);
if (lean_is_scalar(x_8)) {
 x_22 = lean_alloc_ctor(1, 2, 0);
} else {
 x_22 = x_8;
 lean_ctor_set_tag(x_22, 1);
}
lean_ctor_set(x_22, 0, x_10);
lean_ctor_set(x_22, 1, x_7);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_23 = lean_ctor_get(x_10, 0);
lean_inc(x_23);
lean_dec(x_10);
x_24 = lean_mk_string_unchecked("Unexpected param '", 18, 18);
x_25 = l_Lean_Json_compress(x_9);
x_26 = lean_string_append(x_24, x_25);
lean_dec(x_25);
x_27 = lean_mk_string_unchecked("' for method '", 14, 14);
x_28 = lean_string_append(x_26, x_27);
lean_dec(x_27);
x_29 = lean_string_append(x_28, x_3);
lean_dec(x_3);
x_30 = lean_mk_string_unchecked("'\n", 2, 2);
x_31 = lean_string_append(x_29, x_30);
lean_dec(x_30);
x_32 = lean_string_append(x_31, x_23);
lean_dec(x_23);
x_33 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_33, 0, x_32);
if (lean_is_scalar(x_8)) {
 x_34 = lean_alloc_ctor(1, 2, 0);
} else {
 x_34 = x_8;
 lean_ctor_set_tag(x_34, 1);
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_7);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_9);
x_35 = lean_ctor_get(x_10, 0);
lean_inc(x_35);
lean_dec(x_10);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_3);
lean_ctor_set(x_36, 1, x_35);
if (lean_is_scalar(x_8)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_8;
}
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_7);
return x_37;
}
}
}
else
{
uint8_t x_236; 
lean_dec(x_3);
x_236 = !lean_is_exclusive(x_5);
if (x_236 == 0)
{
return x_5;
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_237 = lean_ctor_get(x_5, 0);
x_238 = lean_ctor_get(x_5, 1);
lean_inc(x_238);
lean_inc(x_237);
lean_dec(x_5);
x_239 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_239, 0, x_237);
lean_ctor_set(x_239, 1, x_238);
return x_239;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspNotificationAs___at___Lean_Server_FileWorker_initAndRunWorker_spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_12; 
lean_inc(x_1);
x_12 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader(x_1, x_3);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_IO_FS_Stream_readNotificationAs___at___IO_FS_Stream_readLspNotificationAs___at___Lean_Server_FileWorker_initAndRunWorker_spec__9_spec__9(x_1, x_13, x_2, x_14);
lean_dec(x_13);
if (lean_obj_tag(x_15) == 0)
{
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_4 = x_16;
x_5 = x_17;
goto block_11;
}
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_2);
lean_dec(x_1);
x_18 = lean_ctor_get(x_12, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_dec(x_12);
x_4 = x_18;
x_5 = x_19;
goto block_11;
}
block_11:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_mk_string_unchecked("Cannot read LSP notification: ", 30, 30);
x_7 = lean_io_error_to_string(x_4);
x_8 = lean_string_append(x_6, x_7);
lean_dec(x_7);
x_9 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_5);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_initAndRunWorker_spec__11___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_3, x_2);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; 
lean_dec(x_4);
x_8 = lean_array_uget(x_1, x_3);
x_9 = lean_io_cancel(x_8, x_5);
lean_dec(x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_box(0);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_usize_of_nat(x_12);
x_14 = lean_usize_add(x_3, x_13);
x_3 = x_14;
x_4 = x_11;
x_5 = x_10;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_initAndRunWorker_spec__11(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_initAndRunWorker_spec__11___redArg(x_1, x_2, x_3, x_4, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_initAndRunWorker(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_32; lean_object* x_33; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; 
x_39 = lean_mk_string_unchecked("fwIn.txt", 8, 8);
x_40 = lean_box(0);
x_41 = lean_unbox(x_40);
x_42 = l_Lean_Server_maybeTee(x_39, x_41, x_1, x_5);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_mk_string_unchecked("fwOut.txt", 9, 9);
x_46 = lean_box(1);
x_47 = lean_unbox(x_46);
lean_inc(x_2);
x_48 = l_Lean_Server_maybeTee(x_45, x_47, x_2, x_44);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_mk_string_unchecked("initialize", 10, 10);
lean_inc(x_43);
x_52 = l_IO_FS_Stream_readLspRequestAs___at___Lean_Server_FileWorker_initAndRunWorker_spec__0(x_43, x_51, x_50);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_mk_string_unchecked("textDocument/didOpen", 20, 20);
lean_inc(x_43);
x_56 = l_IO_FS_Stream_readLspNotificationAs___at___Lean_Server_FileWorker_initAndRunWorker_spec__9(x_43, x_55, x_54);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
lean_inc(x_61);
x_62 = l_Lean_Server_moduleFromDocumentUri(x_61, x_58);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_99; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = lean_ctor_get(x_60, 2);
lean_inc(x_65);
x_66 = lean_ctor_get(x_60, 3);
lean_inc(x_66);
lean_dec(x_60);
x_67 = l_String_crlfToLf(x_66);
lean_dec(x_66);
x_68 = l_Lean_FileMap_ofString(x_67);
x_99 = lean_ctor_get(x_59, 1);
lean_inc(x_99);
lean_dec(x_59);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; uint8_t x_101; 
x_100 = lean_box(0);
x_101 = lean_unbox(x_100);
x_69 = x_101;
goto block_98;
}
else
{
lean_object* x_102; uint8_t x_103; 
x_102 = lean_ctor_get(x_99, 0);
lean_inc(x_102);
lean_dec(x_99);
x_103 = lean_unbox(x_102);
lean_dec(x_102);
x_69 = x_103;
goto block_98;
}
block_98:
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_70 = lean_mk_string_unchecked("[", 1, 1);
x_71 = lean_string_append(x_70, x_61);
x_72 = lean_mk_string_unchecked("] ", 2, 2);
x_73 = lean_string_append(x_71, x_72);
lean_dec(x_72);
x_74 = l_IO_FS_Stream_withPrefix(x_3, x_73);
lean_inc(x_74);
x_75 = lean_get_set_stderr(x_74, x_64);
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
lean_dec(x_75);
x_77 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_77, 0, x_61);
lean_ctor_set(x_77, 1, x_63);
lean_ctor_set(x_77, 2, x_65);
lean_ctor_set(x_77, 3, x_68);
lean_ctor_set_uint8(x_77, sizeof(void*)*4, x_69);
x_78 = lean_ctor_get(x_53, 2);
lean_inc(x_78);
lean_dec(x_53);
x_79 = l_Lean_Server_FileWorker_initializeWorker(x_77, x_49, x_74, x_78, x_4, x_76);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = lean_ctor_get(x_80, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_80, 1);
lean_inc(x_83);
lean_dec(x_80);
x_84 = lean_st_mk_ref(x_83, x_81);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
lean_inc(x_82);
x_87 = l_Lean_Server_FileWorker_runRefreshTasks(x_82, x_85, x_86);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
lean_inc(x_85);
x_90 = l_Lean_Server_FileWorker_mainLoop(x_43, x_82, x_85, x_89);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; size_t x_93; lean_object* x_94; size_t x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_2);
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
lean_dec(x_90);
x_92 = lean_box(0);
x_93 = lean_array_size(x_88);
x_94 = lean_unsigned_to_nat(0u);
x_95 = lean_usize_of_nat(x_94);
x_96 = l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_initAndRunWorker_spec__11___redArg(x_88, x_93, x_95, x_92, x_91);
lean_dec(x_88);
x_97 = lean_ctor_get(x_96, 1);
lean_inc(x_97);
lean_dec(x_96);
x_6 = x_85;
x_7 = x_92;
x_8 = x_97;
goto block_14;
}
else
{
lean_dec(x_88);
x_32 = x_85;
x_33 = x_90;
goto block_38;
}
}
}
else
{
uint8_t x_104; 
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_53);
lean_dec(x_49);
lean_dec(x_43);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_104 = !lean_is_exclusive(x_62);
if (x_104 == 0)
{
return x_62;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_62, 0);
x_106 = lean_ctor_get(x_62, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_62);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
}
else
{
uint8_t x_108; 
lean_dec(x_53);
lean_dec(x_49);
lean_dec(x_43);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_108 = !lean_is_exclusive(x_56);
if (x_108 == 0)
{
return x_56;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_56, 0);
x_110 = lean_ctor_get(x_56, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_56);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
}
else
{
uint8_t x_112; 
lean_dec(x_49);
lean_dec(x_43);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_112 = !lean_is_exclusive(x_52);
if (x_112 == 0)
{
return x_52;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_52, 0);
x_114 = lean_ctor_get(x_52, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_52);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
else
{
uint8_t x_116; 
lean_dec(x_43);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_116 = !lean_is_exclusive(x_48);
if (x_116 == 0)
{
return x_48;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_48, 0);
x_118 = lean_ctor_get(x_48, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_48);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
return x_119;
}
}
}
else
{
uint8_t x_120; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_120 = !lean_is_exclusive(x_42);
if (x_120 == 0)
{
return x_42;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_42, 0);
x_122 = lean_ctor_get(x_42, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_42);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
return x_123;
}
}
block_14:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_st_ref_get(x_6, x_8);
lean_dec(x_6);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_9, 0);
lean_dec(x_11);
lean_ctor_set(x_9, 0, x_7);
return x_9;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
block_31:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_st_ref_get(x_15, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
lean_inc(x_16);
x_24 = l_Lean_Server_FileWorker_initAndRunWorker_writeErrorDiag(x_2, x_23, x_16, x_20);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
lean_dec(x_15);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
lean_ctor_set_tag(x_24, 1);
lean_ctor_set(x_24, 0, x_16);
return x_24;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_16);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
else
{
lean_dec(x_16);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_24, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_24, 1);
lean_inc(x_30);
lean_dec(x_24);
x_6 = x_15;
x_7 = x_29;
x_8 = x_30;
goto block_14;
}
else
{
lean_dec(x_15);
return x_24;
}
}
}
block_38:
{
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_2);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_6 = x_32;
x_7 = x_34;
x_8 = x_35;
goto block_14;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_33, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_33, 1);
lean_inc(x_37);
lean_dec(x_33);
x_15 = x_32;
x_16 = x_36;
x_17 = x_37;
goto block_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___IO_FS_Stream_readRequestAs___at___IO_FS_Stream_readLspRequestAs___at___Lean_Server_FileWorker_initAndRunWorker_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___IO_FS_Stream_readRequestAs___at___IO_FS_Stream_readLspRequestAs___at___Lean_Server_FileWorker_initAndRunWorker_spec__0_spec__0_spec__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___IO_FS_Stream_readRequestAs___at___IO_FS_Stream_readLspRequestAs___at___Lean_Server_FileWorker_initAndRunWorker_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___IO_FS_Stream_readRequestAs___at___IO_FS_Stream_readLspRequestAs___at___Lean_Server_FileWorker_initAndRunWorker_spec__0_spec__0_spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___IO_FS_Stream_readRequestAs___at___IO_FS_Stream_readLspRequestAs___at___Lean_Server_FileWorker_initAndRunWorker_spec__0_spec__0_spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___IO_FS_Stream_readRequestAs___at___IO_FS_Stream_readLspRequestAs___at___Lean_Server_FileWorker_initAndRunWorker_spec__0_spec__0_spec__2(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___IO_FS_Stream_readRequestAs___at___IO_FS_Stream_readLspRequestAs___at___Lean_Server_FileWorker_initAndRunWorker_spec__0_spec__0_spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___IO_FS_Stream_readRequestAs___at___IO_FS_Stream_readLspRequestAs___at___Lean_Server_FileWorker_initAndRunWorker_spec__0_spec__0_spec__3(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___IO_FS_Stream_readRequestAs___at___IO_FS_Stream_readLspRequestAs___at___Lean_Server_FileWorker_initAndRunWorker_spec__0_spec__0_spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___IO_FS_Stream_readRequestAs___at___IO_FS_Stream_readLspRequestAs___at___Lean_Server_FileWorker_initAndRunWorker_spec__0_spec__0_spec__4(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Json_getObjValAs_x3f___at___IO_FS_Stream_readRequestAs___at___IO_FS_Stream_readLspRequestAs___at___Lean_Server_FileWorker_initAndRunWorker_spec__0_spec__0_spec__5_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lean_Json_getObjValAs_x3f___at___IO_FS_Stream_readRequestAs___at___IO_FS_Stream_readLspRequestAs___at___Lean_Server_FileWorker_initAndRunWorker_spec__0_spec__0_spec__5_spec__5(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___IO_FS_Stream_readRequestAs___at___IO_FS_Stream_readLspRequestAs___at___Lean_Server_FileWorker_initAndRunWorker_spec__0_spec__0_spec__5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___IO_FS_Stream_readRequestAs___at___IO_FS_Stream_readLspRequestAs___at___Lean_Server_FileWorker_initAndRunWorker_spec__0_spec__0_spec__5(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readRequestAs___at___IO_FS_Stream_readLspRequestAs___at___Lean_Server_FileWorker_initAndRunWorker_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_FS_Stream_readRequestAs___at___IO_FS_Stream_readLspRequestAs___at___Lean_Server_FileWorker_initAndRunWorker_spec__0_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readNotificationAs___at___IO_FS_Stream_readLspNotificationAs___at___Lean_Server_FileWorker_initAndRunWorker_spec__9_spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_FS_Stream_readNotificationAs___at___IO_FS_Stream_readLspNotificationAs___at___Lean_Server_FileWorker_initAndRunWorker_spec__9_spec__9(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_initAndRunWorker_spec__11___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_initAndRunWorker_spec__11___redArg(x_1, x_6, x_7, x_4, x_5);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_initAndRunWorker_spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l_Array_forIn_x27Unsafe_loop___at___Lean_Server_FileWorker_initAndRunWorker_spec__11(x_1, x_8, x_9, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* lean_server_worker_main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_25; 
x_3 = lean_get_stdin(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_get_stdout(x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_get_stderr(x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_10);
x_25 = l_Lean_Server_FileWorker_initAndRunWorker(x_4, x_7, x_10, x_1, x_11);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_unsigned_to_nat(0u);
x_28 = lean_uint8_of_nat(x_27);
x_29 = lean_io_exit(x_28, x_26);
if (lean_obj_tag(x_29) == 0)
{
lean_dec(x_10);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_12 = x_30;
x_13 = x_31;
goto block_24;
}
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_25, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_25, 1);
lean_inc(x_33);
lean_dec(x_25);
x_12 = x_32;
x_13 = x_33;
goto block_24;
}
block_24:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_io_error_to_string(x_12);
x_15 = l_IO_FS_Stream_putStrLn(x_10, x_14, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_uint8_of_nat(x_17);
x_19 = lean_io_exit(x_18, x_16);
return x_19;
}
else
{
uint8_t x_20; 
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
}
}
lean_object* initialize_Init_System_IO(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Sync_Channel(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_RBMap(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Environment(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Lsp(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Json_FromToJson(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_FileSetupInfo(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_LoadDynlib(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Language_Lean(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Server_Utils(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Server_AsyncList(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Server_References(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Server_FileWorker_Utils(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Server_FileWorker_RequestHandling(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Server_FileWorker_WidgetRequests(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Server_FileWorker_SetupFile(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Server_Rpc_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Widget_InteractiveDiagnostic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Server_Completion_ImportCompletion(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Server_CodeActions_UnknownIdentifier(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Server_FileWorker(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_IO(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Sync_Channel(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_RBMap(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Environment(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Json_FromToJson(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_FileSetupInfo(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_LoadDynlib(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Language_Lean(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_Utils(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_AsyncList(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_References(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_FileWorker_Utils(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_FileWorker_RequestHandling(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_FileWorker_WidgetRequests(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_FileWorker_SetupFile(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_Rpc_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Widget_InteractiveDiagnostic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_Completion_ImportCompletion(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_CodeActions_UnknownIdentifier(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Server_FileWorker_instInhabitedPartialHandlerInfo = _init_l_Lean_Server_FileWorker_instInhabitedPartialHandlerInfo();
lean_mark_persistent(l_Lean_Server_FileWorker_instInhabitedPartialHandlerInfo);
l_Lean_Server_FileWorker_instInhabitedReportSnapshotsState = _init_l_Lean_Server_FileWorker_instInhabitedReportSnapshotsState();
lean_mark_persistent(l_Lean_Server_FileWorker_instInhabitedReportSnapshotsState);
if (builtin) {res = l_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker___hyg_753_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Server_FileWorker_server_reportDelayMs = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Server_FileWorker_server_reportDelayMs);
lean_dec_ref(res);
}l_Lean_Server_FileWorker_instImpl____x40_Lean_Server_FileWorker___hyg_804_ = _init_l_Lean_Server_FileWorker_instImpl____x40_Lean_Server_FileWorker___hyg_804_();
lean_mark_persistent(l_Lean_Server_FileWorker_instImpl____x40_Lean_Server_FileWorker___hyg_804_);
l_Lean_Server_FileWorker_instTypeNameMemorizedInteractiveDiagnostics = _init_l_Lean_Server_FileWorker_instTypeNameMemorizedInteractiveDiagnostics();
lean_mark_persistent(l_Lean_Server_FileWorker_instTypeNameMemorizedInteractiveDiagnostics);
if (builtin) {res = l_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker___hyg_2716_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_importsLoadedRef = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_importsLoadedRef);
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
